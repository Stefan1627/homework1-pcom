#include <netinet/ip_icmp.h>
#include <sys/ioctl.h>
#include <net/if.h>
#include <netinet/in.h>
#include <linux/if_packet.h>
#include <string.h>
#include <sys/types.h>
#include <asm/byteorder.h>
#include <arpa/inet.h>

#include "protocols.h"
#include "queue.h"
#include "lib.h"
#include "list.h"

#define ETHERTYPE_IP 0x0800   /* IP */
#define ETHERTYPE_ARP 0x0806  /* ARP */

struct route_table_entry *routing_table = NULL;
size_t routing_table_size = 0;

// Dynamic ARP cache
struct arp_table_entry *arp_table = NULL;
int arp_table_size = 0;

// Structure for packets waiting for an ARP response
struct waiting_packet
{
    char *packet;
    size_t len;
    uint32_t next_hop_ip;
    size_t interface;
    struct waiting_packet *next;
};

struct waiting_packet *waiting_queue = NULL;

// Trie node
struct trie_node
{
    struct route_table_entry *route;
    struct trie_node *children[2];
};

/* 
 * create_trie_node
 * Creates a new trie node and initializes its members.
 */
struct trie_node *create_trie_node()
{
    struct trie_node *node = malloc(sizeof(struct trie_node));
    if (!node) {
        perror("Error allocating trie node");
        exit(1);
    }

    node->route = NULL;
    node->children[0] = node->children[1] = NULL;
    return node;
}

/* 
 * insert_route
 * Inserts a route into the trie data structure based on the IP prefix bits.
 */
void insert_route(struct trie_node *root, struct route_table_entry *entry)
{
    uint32_t host_prefix = ntohl(entry->prefix);
    int prefix_len = __builtin_popcount(ntohl(entry->mask));
    struct trie_node *curr = root;

    for (int i = 31; i >= 32 - prefix_len; i--) {
        int bit = (host_prefix >> i) & 1;

        if (curr->children[bit] == NULL)
            curr->children[bit] = create_trie_node();

        curr = curr->children[bit];
    }
    curr->route = entry;
}

/* 
 * lookup_route
 * Traverses the trie to find the best matching route (longest prefix match) 
 * for the provided destination IP address.
 */
struct route_table_entry *lookup_route(struct trie_node *root, uint32_t dest_ip) {
    struct trie_node *curr = root;
    struct route_table_entry *best = NULL;
    uint32_t host_ip = ntohl(dest_ip);

    for (int i = 31; i >= 0 && curr; i--) {
        int bit = (host_ip >> i) & 1;

        curr = curr->children[bit];
        if (curr && curr->route != NULL) {
            best = curr->route;
        }
    }
    return best;
}

/* 
 * arp_lookup
 * Searches the ARP cache for an entry corresponding to the specified IP address.
 * If found, copies the associated MAC address into the provided buffer.
 */
int arp_lookup(uint32_t ip, uint8_t *mac)
{
    for (int i = 0; i < arp_table_size; i++) {
        if (arp_table[i].ip == ip) {
            memcpy(mac, arp_table[i].mac, 6);
            return 0;
        }
    }
    return -1;
}

/* 
 * handle_icmp_msg
 * Processes an ICMP Echo Request message by swapping MAC and IP addresses,
 * recalculating the checksum, and sending back an ICMP Echo Reply.
 */
void handle_icmp_msg(char *buf, size_t len, size_t interface)
{
    struct icmp_hdr *icmp = (struct icmp_hdr *)(buf + sizeof(struct ether_hdr) + sizeof(struct ip_hdr));

    if (icmp->mtype == ICMP_ECHO) {

        struct ether_hdr *eth_reply = (struct ether_hdr *)buf;
        struct ip_hdr *ip_reply = (struct ip_hdr *)(buf + sizeof(struct ether_hdr));
        struct icmp_hdr *icmp_reply = (struct icmp_hdr *)(buf + sizeof(struct ether_hdr) + sizeof(struct ip_hdr));

        // Swap MAC addresses
        uint8_t temp_mac[6];

        memcpy(temp_mac, eth_reply->ethr_shost, 6);
        memcpy(eth_reply->ethr_shost, eth_reply->ethr_dhost, 6);
        memcpy(eth_reply->ethr_dhost, temp_mac, 6);

        // Swap IP addresses
        uint32_t temp_ip = ip_reply->source_addr;

        ip_reply->source_addr = ip_reply->dest_addr;
        ip_reply->dest_addr = temp_ip;

        size_t ip_packet_len = len - sizeof(struct ether_hdr);
        ip_reply->tot_len = htons(ip_packet_len);

        // Recalculate the IP header checksum
        ip_reply->checksum = 0;
        uint16_t ip_sum = checksum((uint16_t *)ip_reply, ip_reply->ihl * 4);
        ip_reply->checksum = htons(ip_sum);

        icmp_reply->mtype = ICMP_ECHOREPLY;
        icmp_reply->mcode = 0;

        size_t icmp_len = ip_packet_len - (ip_reply->ihl * 4);

        icmp_reply->check = 0;
        uint16_t icmp_sum = checksum((uint16_t *)icmp_reply, icmp_len);
        icmp_reply->check = htons(icmp_sum);

        send_to_link(len, buf, interface);
    }
}

/* 
 * handle_ttl_expiration
 * Constructs and sends an ICMP Time Exceeded message when a packet's TTL reaches 0.
 */
void handle_ttl_expiration(char *buf, size_t len, size_t interface)
{
    struct ether_hdr *orig_eth = (struct ether_hdr *)buf;
    struct ip_hdr *orig_ip = (struct ip_hdr *)(buf + sizeof(struct ether_hdr));
    int orig_ip_hdr_len = orig_ip->ihl * 4;
    int data_len = orig_ip_hdr_len + 8;

    if (len < sizeof(struct ether_hdr) + data_len) {
        data_len = len - sizeof(struct ether_hdr);
    }

    char copied_data[data_len];
    memcpy(copied_data, orig_ip, data_len);

    // Update Ethernet header: swap source and destination MAC addresses
    uint8_t temp_mac[6];

    memcpy(temp_mac, orig_eth->ethr_shost, 6);
    memcpy(orig_eth->ethr_shost, orig_eth->ethr_dhost, 6);
    memcpy(orig_eth->ethr_dhost, temp_mac, 6);

    // Build the new IP header in the buffer
    struct ip_hdr *ip_reply = orig_ip;

    ip_reply->ver = 4;
    ip_reply->ihl = 5;
    ip_reply->tos = 0;

    uint16_t ip_total_length = 20 + 8 + data_len;

    ip_reply->tot_len = htons(ip_total_length);
    ip_reply->id = 0;
    ip_reply->frag = 0;
    ip_reply->ttl = 64;
    ip_reply->proto = IPPROTO_ICMP;

    uint32_t orig_src_ip = ip_reply->source_addr;

    ip_reply->source_addr = inet_addr(get_interface_ip(interface));
    ip_reply->dest_addr = orig_src_ip;

    ip_reply->checksum = 0;
    uint16_t ip_sum = checksum((uint16_t *)ip_reply, sizeof(struct ip_hdr));
    ip_reply->checksum = htons(ip_sum);

    // Build the ICMP header for "Time Exceeded"
    struct icmp_hdr *icmp_reply = (struct icmp_hdr *)(buf + sizeof(struct ether_hdr) + sizeof(struct ip_hdr));

    icmp_reply->mtype = ICMP_TIME_EXCEEDED;
    icmp_reply->mcode = 0;
    icmp_reply->check = 0;
    *((uint32_t *)((char *)icmp_reply + 4)) = 0;

    char *icmp_payload = (char *)icmp_reply + sizeof(struct icmp_hdr);
    memcpy(icmp_payload, copied_data, data_len);

    int icmp_total_len = sizeof(struct icmp_hdr) + data_len;

    icmp_reply->check = checksum((uint16_t *)icmp_reply, icmp_total_len);
    icmp_reply->check = htons(icmp_reply->check);

    int packet_len = sizeof(struct ether_hdr) + ip_total_length;

    send_to_link(packet_len, buf, interface);
}

/* 
 * handle_dest_unreachable
 * Constructs and sends an ICMP Destination Unreachable message when no valid route exists 
 * for the destination IP of the received packet.
 */
void handle_dest_unreachable(char *buf, size_t len, size_t interface)
{
    struct ether_hdr *orig_eth = (struct ether_hdr *)buf;
    struct ip_hdr *orig_ip = (struct ip_hdr *)(buf + sizeof(struct ether_hdr));
    int orig_ip_hdr_len = orig_ip->ihl * 4;
    int data_len = orig_ip_hdr_len + 8;

    if (len < sizeof(struct ether_hdr) + data_len)
        data_len = len - sizeof(struct ether_hdr);

    char copied_data[data_len];

    memcpy(copied_data, orig_ip, data_len);

    // Update Ethernet header: swap MAC addresses
    uint8_t temp_mac[6];

    memcpy(temp_mac, orig_eth->ethr_shost, 6);
    memcpy(orig_eth->ethr_shost, orig_eth->ethr_dhost, 6);
    memcpy(orig_eth->ethr_dhost, temp_mac, 6);

    struct ip_hdr *ip_reply = orig_ip;

    ip_reply->ver = 4;
    ip_reply->ihl = 5;
    ip_reply->tos = 0;

    uint16_t ip_total_length = 20 + 8 + data_len;

    ip_reply->tot_len = htons(ip_total_length);
    ip_reply->id = 0;
    ip_reply->frag = 0;
    ip_reply->ttl = 64;
    ip_reply->proto = IPPROTO_ICMP;

    uint32_t orig_src_ip = ip_reply->source_addr;

    ip_reply->source_addr = inet_addr(get_interface_ip(interface));
    ip_reply->dest_addr = orig_src_ip;
    ip_reply->checksum = 0;

    uint16_t ip_sum2 = checksum((uint16_t *)ip_reply, sizeof(struct ip_hdr));

    ip_reply->checksum = htons(ip_sum2);

    struct icmp_hdr *icmp_reply = (struct icmp_hdr *)(buf + sizeof(struct ether_hdr) + sizeof(struct ip_hdr));

    icmp_reply->mtype = ICMP_DEST_UNREACH;
    icmp_reply->mcode = 0;
    icmp_reply->check = 0;
    *((uint32_t *)((char *)icmp_reply + 4)) = 0;

    char *icmp_payload = (char *)icmp_reply + sizeof(struct icmp_hdr);
    memcpy(icmp_payload, copied_data, data_len);

    int icmp_total_len = sizeof(struct icmp_hdr) + data_len;

    icmp_reply->check = checksum((uint16_t *)icmp_reply, icmp_total_len);
    icmp_reply->check = htons(icmp_reply->check);

    int packet_len = sizeof(struct ether_hdr) + ip_total_length;

    send_to_link(packet_len, buf, interface);
}

/* 
 * enqueue_packet
 * Queues a packet waiting for ARP resolution by storing its data, next-hop IP, and interface.
 */
void enqueue_packet(uint32_t next_hop_ip, char *buf, size_t len, size_t interface)
{
    struct waiting_packet *wp = malloc(sizeof(struct waiting_packet));
    if (!wp) {
        perror("malloc");
        exit(1);
    }

    wp->packet = malloc(len);
    if (!wp->packet) {
        perror("malloc");
        exit(1);
    }

    memcpy(wp->packet, buf, len);
    wp->len = len;
    wp->next_hop_ip = next_hop_ip;
    wp->interface = interface;
    wp->next = waiting_queue;
    waiting_queue = wp;
}

/* 
 * process_queued_packets
 * Processes all packets in the waiting queue that match the provided IP address once their ARP resolution is completed.
 */
void process_queued_packets(uint32_t ip)
{
    struct waiting_packet **curr = &waiting_queue;

    while (*curr) {
        if ((*curr)->next_hop_ip == ip) {
            uint8_t next_hop_mac[6];

            if (arp_lookup(ip, next_hop_mac) == 0) {
                struct ether_hdr *eth = (struct ether_hdr *)((*curr)->packet);
                uint8_t src_mac[6];

                get_interface_mac((*curr)->interface, src_mac);
                memcpy(eth->ethr_shost, src_mac, 6);
                memcpy(eth->ethr_dhost, next_hop_mac, 6);
                send_to_link((*curr)->len, (*curr)->packet, (*curr)->interface);
            }

            struct waiting_packet *to_free = *curr;

            *curr = (*curr)->next;
            free(to_free->packet);
            free(to_free);
        }
        else {
            curr = &((*curr)->next);
        }
    }
}

/* 
 * update_arp_cache
 * Updates the ARP cache by modifying an existing entry or adding a new one for the given IP.
 */
void update_arp_cache(uint32_t ip, uint8_t *mac)
{
    for (int i = 0; i < arp_table_size; i++) {
        if (arp_table[i].ip == ip) {
            memcpy(arp_table[i].mac, mac, 6);
            return;
        }
    }

    arp_table = realloc(arp_table, sizeof(struct arp_table_entry) * (arp_table_size + 1));
    if (!arp_table) {
        perror("realloc");
        exit(1);
    }

    arp_table[arp_table_size].ip = ip;
    memcpy(arp_table[arp_table_size].mac, mac, 6);
    arp_table_size++;
}

/* 
 * send_arp_request
 * Constructs and sends an ARP request for the target IP on the specified interface.
 */
void send_arp_request(uint32_t target_ip, int interface)
{
    char buf[sizeof(struct ether_hdr) + sizeof(struct arp_hdr)];

    memset(buf, 0, sizeof(buf));

    struct ether_hdr *eth = (struct ether_hdr *)buf;
    struct arp_hdr *arp = (struct arp_hdr *)(buf + sizeof(struct ether_hdr));

    memset(eth->ethr_dhost, 0xFF, 6);

    uint8_t src_mac[6];

    get_interface_mac(interface, src_mac);
    memcpy(eth->ethr_shost, src_mac, 6);
    eth->ethr_type = htons(ETHERTYPE_ARP);

    // ARP header
    arp->hw_type = htons(1);
    arp->proto_type = htons(ETHERTYPE_IP);
    arp->hw_len = 6;
    arp->proto_len = 4;
    arp->opcode = htons(1);
    memcpy(arp->shwa, src_mac, 6);
    arp->sprotoa = inet_addr(get_interface_ip(interface));
    memset(arp->thwa, 0, 6);
    arp->tprotoa = target_ip;

    send_to_link(sizeof(buf), buf, interface);
}

/* 
 * handle_arp_request
 * Processes an incoming ARP request and, if the target IP matches the current interface,
 * generates and sends an ARP reply.
 */
void handle_arp_request(char *buf, size_t len, int interface)
{
    struct arp_hdr *arp_req = (struct arp_hdr *)(buf + sizeof(struct ether_hdr));
    uint32_t target_ip = arp_req->tprotoa;
    uint32_t my_ip = inet_addr(get_interface_ip(interface));

    if (target_ip != my_ip)
        return;

    char reply_buf[sizeof(struct ether_hdr) + sizeof(struct arp_hdr)];

    memset(reply_buf, 0, sizeof(reply_buf));

    struct ether_hdr *eth_reply = (struct ether_hdr *)reply_buf;
    struct arp_hdr *arp_reply = (struct arp_hdr *)(reply_buf + sizeof(struct ether_hdr));

    memcpy(eth_reply->ethr_dhost, arp_req->shwa, 6);

    uint8_t src_mac[6];

    get_interface_mac(interface, src_mac);
    memcpy(eth_reply->ethr_shost, src_mac, 6);
    eth_reply->ethr_type = htons(ETHERTYPE_ARP);

    arp_reply->hw_type = htons(1);
    arp_reply->proto_type = htons(ETHERTYPE_IP);
    arp_reply->hw_len = 6;
    arp_reply->proto_len = 4;
    arp_reply->opcode = htons(2);
    memcpy(arp_reply->shwa, src_mac, 6);
    arp_reply->sprotoa = my_ip;
    memcpy(arp_reply->thwa, arp_req->shwa, 6);
    arp_reply->tprotoa = arp_req->sprotoa;

    send_to_link(sizeof(reply_buf), reply_buf, interface);
}

/* 
 * handle_arp_reply
 * Processes an incoming ARP reply, updates the ARP cache, and processes any queued packets
 * waiting for this ARP resolution.
 */
void handle_arp_reply(char *buf, size_t len, int interface)
{
    struct arp_hdr *arp_rep = (struct arp_hdr *)(buf + sizeof(struct ether_hdr));
    uint32_t sender_ip = arp_rep->sprotoa;
    uint8_t sender_mac[6];

    memcpy(sender_mac, arp_rep->shwa, 6);

    update_arp_cache(sender_ip, sender_mac);

    process_queued_packets(sender_ip);
}

/* 
 * main
 * Entry point of the router's dataplane.
 * Initializes the routing table, builds the trie for longest prefix matching, and 
 * enters the main loop to receive and process packets (ARP and IP), including TTL updates,
 * checksum recalculations, and packet forwarding.
 */
int main(int argc, char *argv[])
{
    if (argc < 2) {
        fprintf(stderr, "Usage: %s <routing_table_file>\n", argv[0]);
        exit(EXIT_FAILURE);
    }   

    /* --- Loading routing table --- */
    routing_table = malloc(sizeof(struct route_table_entry) * 100000);
    routing_table_size = read_rtable(argv[1], routing_table);

    struct trie_node *trie_root = create_trie_node();
    for (int i = 0; i < routing_table_size; i++) {
        insert_route(trie_root, &routing_table[i]);
    }

    arp_table = NULL;
    arp_table_size = 0;

    waiting_queue = NULL;

    char buf[MAX_PACKET_LEN];

    // Nu modifica această linie
    init(argv + 2, argc - 2);

    while (1) {

        size_t interface;
        size_t len;

        interface = recv_from_any_link(buf, &len);
        DIE(interface < 0, "recv_from_any_links");

        struct ether_hdr *eth_hdr = (struct ether_hdr *)buf;
        uint16_t eth_type = ntohs(eth_hdr->ethr_type);

        if (eth_type == ETHERTYPE_ARP) {
            struct arp_hdr *arp_hdr = (struct arp_hdr *)(buf + sizeof(struct ether_hdr));
            uint16_t opcode = ntohs(arp_hdr->opcode);

            if (opcode == 1) // ARP request
                handle_arp_request(buf, len, interface);
            else if (opcode == 2) // ARP reply
                handle_arp_reply(buf, len, interface);
            continue;
        }

        if (eth_type == ETHERTYPE_IP) {
            struct ip_hdr *ip_hdr = (struct ip_hdr *)(buf + sizeof(struct ether_hdr));

            /* --- Check IP checksum --- */
            uint16_t received_checksum = ntohs(ip_hdr->checksum);

            ip_hdr->checksum = 0;
            uint16_t computed_checksum = checksum((uint16_t *)ip_hdr, ip_hdr->ihl * 4);

            if (received_checksum != computed_checksum)
                continue;
            ip_hdr->checksum = htons(received_checksum);

            /* --- Check if this packet is destined for me --- */
            if (ip_hdr->dest_addr == inet_addr(get_interface_ip(interface))) {
                if (ip_hdr->proto == IPPROTO_ICMP)
                    handle_icmp_msg(buf, len, interface);
                continue;
            }

            /* --- Check TTL --- */
            if (ip_hdr->ttl <= 1) {
                handle_ttl_expiration(buf, len, interface);
                continue;
            }
            ip_hdr->ttl--;

            /* --- Recalculate checksum --- */
            ip_hdr->checksum = 0;
            uint16_t new_checksum = checksum((uint16_t *)ip_hdr, ip_hdr->ihl * 4);
            ip_hdr->checksum = htons(new_checksum);

            /* --- Next hop searching --- */
            struct route_table_entry *route = lookup_route(trie_root, ip_hdr->dest_addr);

            if (!route) {
                handle_dest_unreachable(buf, len, interface);
                continue;
            }

            /* --- Packet preparing --- */
            uint32_t next_hop_ip;

            if (route->next_hop != 0)
                next_hop_ip = route->next_hop;
            else
                next_hop_ip = ip_hdr->dest_addr;

            uint8_t next_hop_mac[6];

            if (arp_lookup(next_hop_ip, next_hop_mac) < 0) {
                // ARP table entry not found so send an ARP request
                enqueue_packet(next_hop_ip, buf, len, route->interface);
                send_arp_request(next_hop_ip, route->interface);
                continue;
            }

            uint8_t src_mac[6];

            get_interface_mac(route->interface, src_mac);
            memcpy(eth_hdr->ethr_shost, src_mac, 6);
            memcpy(eth_hdr->ethr_dhost, next_hop_mac, 6);

            int ip_packet_len = ntohs(ip_hdr->tot_len);
            int total_packet_len = sizeof(struct ether_hdr) + ip_packet_len;

            /* --- Forward the packet --- */
            send_to_link(total_packet_len, buf, route->interface);
        }
    }

    free(routing_table);

    return 0;
}
