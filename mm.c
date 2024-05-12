/*
 * mm.c
 *
 * Name: Vanshaj Agrawal
 *
 * This is an implementation of malloc, free and realloc for managing the heap. Each allocated/free block is preceded by a header 
 *containing information about that block. free blocks are additionally added as nodes in 'maxindex' number of linked lists, 
 *based on their size.
 *malloc calls finder() to retrieve a pointer to a free block. finder() calls get_freeblock() which abstracts the linked list 
 *traversal to retrieve a free node. finder() then calls allocate which splits large free nodes. If a free node does not exist, 
 *extend() increases heap memory by the appropriate memory. 
 *free() calls free_hf() which creates the header and footers and coalesces neighboring free blocks.
 *addnode() and removenode() abstract the manipulation of the various circular doubly linked lists pointed to by head[index].
 *mm_checkheap() is called at the beginning and end of each each malloc/free operation to validate heap consistency
 *printheap() and printlist() can be used to observe the changes in the heap's state during each malloc/free operation.
 * List of shorthands used: f=footer, h=header, n=node
 * 
 *
 */

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <stdint.h>
#include <stdbool.h>
#include "mm.h"
#include "memlib.h"


// #define DEBUG
// #define PRINT
#ifdef PRINT
#define dbg_printf(...) printf(__VA_ARGS__)
#else
#define dbg_printf(...)
#endif
#ifdef DEBUG
// When debugging is enabled, the underlying functions get called
// #define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
// When debugging is disabled, no code gets generated
// #define dbg_printf(...)
#define dbg_assert(...)
#endif // DEBUG

// do not change the following!
#ifdef DRIVER
// create aliases for driver tests
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mm_memset
#define memcpy mm_memcpy
#endif // DRIVER

#define ALIGNMENT 16
#define w 8
#define maxindex 16

typedef struct node* Node;
struct node{
    Node prev, next;
};

void* head[maxindex];

/* Initially empty lists must have NULL heads */
void head_init(){
    for(size_t index=0;index<maxindex;index++){
        head[index]=NULL; 
    }
    return;
}
/* Retrieve the appropriate list based on size */
int get_index(size_t size){

    if(size<=32) return 0;
    if(size<=48) return 1;
    if(size<=64) return 2;
    if(size<=96) return 3;
    if(size<=128) return 4;
    if(size<=256) return 5;
    if(size<=512) return 6;
    if(size<=1024) return 7;
    if(size<=2048) return 8;
    if(size<=4096) return 9;
    if(size<=8192) return 10;
    if(size<=16384) return 11;
    if(size<=65536) return 12;
    if(size<=131072) return 13;
    if(size<=262144) return 14;
    // if(size<=524288) return 14;
    else return 15;
}
static size_t align(size_t x)
{
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}
static bool aligned(const void* p)
{
    size_t ip = (size_t) p;
    return align(ip) == ip;
}
 static bool in_heap(const void* p)
{
    return p <= mm_heap_hi() && p >= mm_heap_lo();
}
/* Helper functions to increment/decrement pointers */
void* incr(void* ptr, size_t size)
{
    ptr=((char*)ptr+size);
    dbg_assert(in_heap(ptr));
    return ptr;
}
void* decr(void* ptr, size_t size)
{
    ptr=((char*)ptr-size);
    dbg_assert(in_heap(ptr));
    return ptr;
}
/* Retrieves the 16 byte aligned block size by masking out the last 4 bits*/
size_t get_size(void* ptr)
{
  size_t val=*(size_t*)ptr;
  size_t s=val & ~0xf;
  
  return s;
}
int diff(void* ptr1, void* ptr2)
{
    return (int)((char*)ptr1-(char*)ptr2);
}


void* get_f(void* ptr){
    size_t block_size=get_size(ptr);
    dbg_assert(in_heap(incr(ptr, block_size-w)));
    return incr(ptr, block_size-w);
}
void* get_h(void* ptr){
    size_t block_size=get_size(ptr);
    dbg_assert(in_heap(decr(ptr, block_size-w)));
    return decr(ptr, block_size-w);
}

/* To get/free/set the allocation status of the preceding block by manipulating the 2nd least significant bit*/
int get_prev_alloc(void* ptr){
    size_t val=*(size_t*)ptr;
    // int prev_alloc=((int)(val & 0x2))?1:0;
    int prev_alloc=(val >> 1) & 1;
    return prev_alloc;
}
size_t free_prev_alloc(void* ptr)
{
    
    size_t val=*(size_t*)ptr;
    dbg_assert(get_prev_alloc(ptr)==1);
    size_t s=val & ~0x2;
    *(size_t*)ptr=s;
    dbg_assert(get_prev_alloc(ptr)==0);
    return s;
}
size_t set_prev_alloc(void* ptr)
{
    
    size_t val=*(size_t*)ptr;
    dbg_assert(get_prev_alloc(ptr)==0);
    size_t s=val | 0x2;
    *(size_t*)ptr=s;
    dbg_assert(get_prev_alloc(ptr)==1);
    return s;
}
/* Note the function parameters which comprise the header*/
void* make_h(void* ptr, size_t size, int prev_alloc, int alloc)
{
    size_t val=size | alloc | prev_alloc<<1;
    *(size_t*)ptr=val;
    return ptr;
}
void* make_f(void* ptr, size_t size, int alloc)
{
    size_t val=size | alloc;
    *(size_t*)ptr=val;
    return ptr;
}
void* make_hf(void* ptr, size_t size, int prev_alloc, int alloc)
{
    make_h(ptr, size, prev_alloc, alloc);
    make_f(get_f(ptr), size, alloc);
    return ptr;
}
void* make_epi(void* ptr)
{
    make_h(ptr, 0, 1, 1);
    return ptr;
}
void* free_h(void* ptr)
{
    size_t val=*(size_t*)ptr & ~0x1;
    *(size_t*)ptr=val;
    return ptr;
}
int is_alloc(void* ptr){
    return (size_t)(*(size_t*)ptr%2);
}
/* To retrieve the corresponding node/header for a block */
void* n2h(void* ptr){
    return decr(ptr, w);
}
void* h2n(void* ptr){
    return incr(ptr, w);
}
bool printlist(int line_number)
{
#ifdef PRINT
    for (int index=0;index<maxindex;index++){
        if(head[index]!=NULL){
            Node x=head[index];
            dbg_printf("List %p:\n", head[index]);
            do{
                dbg_printf("%p, %p, %p, %zu\n", x, x->prev,x->next, get_size(n2h(x)));
                x=x->next;
            }while(x!=head[index]);
            dbg_printf("end of heap:%p\n", mm_heap_hi());
        }
    }
#endif // DEBUG
    return true;
}

bool printheap(int line_number)
{
#ifdef PRINT
    void* ptr=mm_heap_lo();
    ptr=incr(ptr, w); 
    size_t block_size=get_size(ptr);
    dbg_printf("Heap:\n");
    while(block_size!=0)
    {
        dbg_printf("%p, %p, %d, %zu, %d \n",ptr, incr(ptr,w), is_alloc(ptr), get_size(ptr), get_prev_alloc(ptr));
        ptr=incr(ptr,block_size);
        block_size=get_size(ptr);
    }
    printlist(__LINE__);
#endif 
    return true;
}

/* To check if a node ptr is part of the list. 
This can be called in the heap consistency checker to verify that all free blocks are also present as nodes */
bool check_presence(void* ptr, int index){
    if(head[index]!=NULL){
        Node x=head[index];
        do{
            if (x==ptr){
                return true;
            }
            x=x->next;
        }while(x!=head[index]); 
    }
    return false;
}

void addnode(void* ptr)
{
    dbg_printf("Add Node %p\n", ptr);
    
    dbg_assert(in_heap(ptr));
    Node newnode=ptr;
    size_t size=get_size(n2h(ptr));
    int index=get_index(size);
    
    //The first node in list points to itself
    if(head[index]==NULL){
        head[index]=newnode;
        newnode->next = (newnode->prev = newnode);
        return;
    }
    //Insertion at the front requires O(1) time
    else{
        Node first=head[index];
        newnode->prev=first->prev;
        newnode->next=first;
        first->prev->next=newnode;
        first->prev=newnode;
    }
    // printlist(__LINE__);
    return;
}

void removenode(void* ptr, int index)
{
    dbg_printf("Remove Node %p\n", ptr);
    Node freeblock=ptr;
    dbg_assert(head[index]!=NULL);
    dbg_assert(in_heap(ptr));
    //Removing the only node in a list also means removing the head
    if(freeblock==freeblock->next && head[index]==freeblock){  
        dbg_printf("Only one\n");
        head[index]=NULL;
        return;
    }
    //In a circular doubly linked list, any node can be the new head
    if(head[index]==freeblock){ 
        head[index]=freeblock->next;
    }
    freeblock->prev->next=freeblock->next;
    freeblock->next->prev=freeblock->prev;
    return;
}
/* To coalesce neighboring free blocks, their allocation status and sizes are computed and the previous footer and the next header 
are obtained accordingly. The node corresponding to each free block is removed from its list and the coalesced free block is added
back to the appropriate list.*/
void* free_hf(void* ptr)
{
    dbg_printf("free_hf starts: %p, %p\n", ptr, get_f(ptr));
    dbg_printf("heap hi: %p\n", mm_heap_hi());
     
    //The prev_footer and the next_header are used to manipulate the neighboring blocks
    //Note the prev_footer will not exist if the previous block is allocated.
    void* prev_footer=decr(ptr,w);
    void* next_header=incr(get_f(ptr),w);

    //To coalesce neighboring free blocks, their allocation status and sizes are computed
    int prev=get_prev_alloc(ptr);
    int next=is_alloc(next_header);

    dbg_assert(in_heap(prev_footer));
    dbg_assert(in_heap(next_header));

    size_t curr_size=get_size(ptr);
    size_t prev_size=get_size(prev_footer);
    size_t next_size=get_size(next_header);
    size_t size;

    int prev_index=get_index(prev_size);
    int next_index=get_index(next_size);

    //4 combinations of neighbours may exist
    if(prev==0 && next==0){
        dbg_printf("\n\nBoth Free\n\n");
        void* prev_header=get_h(prev_footer);
        void* prev_node=h2n(prev_header);
        void* next_node=h2n(next_header);
        removenode(prev_node, prev_index);
        dbg_printf("Between removenodes\n");
        printheap(__LINE__);
        removenode(next_node, next_index);
        size=curr_size+prev_size+next_size;
        make_h(prev_header, size, get_prev_alloc(prev_header), 0);
        make_f(get_f(next_header), size, 0);
        ptr=get_h(prev_footer);

    }
    else if(prev==0 && next==1){
        void* prev_node=h2n(get_h(prev_footer));
        removenode(prev_node, prev_index);
        size=curr_size+prev_size;
        make_h(get_h(prev_footer), size, get_prev_alloc(get_h(prev_footer)), 0);
        make_f(get_f(ptr),size,0);
        free_prev_alloc(next_header);
        ptr=get_h(prev_footer);

    }
    else if(prev==1 && next==0){
        void* next_node=h2n(next_header);
        removenode(next_node, next_index);
        size=curr_size+next_size;
        make_h(ptr, size, 1, 0);
        make_f(get_f(next_header),size,0);

    }
    else{
        size=curr_size+0*next_index+0*prev_index*next*prev;
        dbg_assert(size>0);
        make_h(ptr, size, 1, 0);
        make_f(get_f(ptr),size,0);
        free_prev_alloc(incr(get_f(ptr),w));

    }
    
    ptr=h2n(ptr);
    addnode(ptr);
    return ptr;
}

/* Execution starts from here and the heap is expanded for the first time to create the prologue and epilogue */
bool mm_init(void)
{
    
    //create prologue epilogue
    void* ptr=mm_sbrk(align(4*w)); 
    dbg_assert(aligned(ptr));

    head_init();
    make_hf(incr(ptr,8), 2*w, 0, 1);
    make_epi(incr(ptr, 3*w));
    if(ptr==NULL) return false;

    return true; 
}

/* Free nodes bigger than the user's requirments are split only if this produces a free node greater than 32 bytes. 
This is the minimum size a free node can have. The freenode is then added to the appropriate list. */
void* allocate(void* ptr, size_t block_size){

    //Free nodes bigger than the user's requirments are split only if this produces a free node greater than 32 bytes. 
    //This is the minimum size a free node can have.
    size_t total_size=get_size(ptr);
    size_t newblock_size=total_size-block_size;

    if (newblock_size>=4*w){
        void* end_hptr=incr(ptr,block_size);
        void* end_fptr=get_f(ptr);
        
        make_h(ptr, block_size, get_prev_alloc(ptr), 1);

        make_h(end_hptr, newblock_size, 1, 0);
        make_f(end_fptr, newblock_size, 0);
        //The new free node created, is then added to the appropriate list.
        addnode(h2n(end_hptr));
        
        dbg_assert(get_f(end_hptr)==end_fptr);
        dbg_assert(newblock_size==get_size(get_f(end_hptr)));
    }
    else{
        //If the node is not too big, give it directly to the user
        make_h(ptr, total_size, get_prev_alloc(ptr), 1);        
        set_prev_alloc(incr(ptr, total_size));
    }
    ptr=incr(ptr, w);
    dbg_assert(aligned(ptr));
    return ptr;
}

/* Iterate over the list to obtain a free block of size>=block_size
The commented out code finds the best-of-k free blocks to maximize utilization at the expense of throughput */
void* get_freeblock(size_t block_size){
    int index=get_index(block_size);
    // void* best=NULL; int best_index;
    // int k=0;
    for (int i=index;i<maxindex;i++){
        if(head[i]!=NULL){
            Node x=head[i];
            do{
                void* header=n2h(x);
                dbg_assert(in_heap(header));
                dbg_assert(in_heap(x));
                if(get_size(header)>=block_size){
                    // if(best==NULL ||get_size(header)<get_size(best)) {
                    //     best=header;
                    //     best_index=i;
                    //     k++;
                    //     if(k==4) break;
                    // }
                    removenode(x, i); //Comment out these 2 lines when finding the best-of-k blocks
                    return x;             //
                }
                x=x->next;
                
            }while(x!=head[i]);
        }
        // if(best!=NULL) break;
    }
    // if(best!=NULL){
    //     removenode(h2n(best), best_index);
    //     return h2n(best);
    // }

    return NULL;
}
/* Extending the heap also requires shifting the epilogue to the end of the heap */
void* extend(size_t block_size)
{
    int prev_alloc=get_prev_alloc(decr(mm_heap_hi(), w-1));
    void* new_ptr=mm_sbrk(block_size);
    if(new_ptr){
        
        make_h(decr(new_ptr,w), block_size, prev_alloc, 1);
        make_epi(incr(new_ptr,(block_size-w)));
    }
    return new_ptr;
}

/* finder returns the payload ptr */
void* finder(void * ptr, size_t block_size)
{
    dbg_assert(in_heap(ptr));
    //get_freeblock() goes through the linked list to retrieve and remove a free node
    void* freeblock=get_freeblock(block_size);
    dbg_assert(in_heap(freeblock) || freeblock==NULL);
    dbg_printf("Freeblock:%p\n", freeblock);
    dbg_printf("Between remove and add:\n");
    printheap(__LINE__);
    printlist(__LINE__);
    //If get_freeblock is successful, the new node must be processed before giving it to the user
    if(freeblock!=NULL){
        dbg_printf("Not null\n");

        ptr=n2h(freeblock);
        void* payload_ptr=allocate(ptr, block_size);
        return payload_ptr;
    }
    //If get_freeblock is successful, a free node of the required size cannot be found and the heap must be extended
    else{
        dbg_printf("null\n");
        void* payload_ptr=extend(block_size);
        return payload_ptr;
    }
    return NULL;
}
void* malloc(size_t size)
{
    //Obtain the start of the heap
    void* ptr=mm_heap_lo();
    //Pad and align the payload size  to ensure the return of aligned addresses 
    ptr=incr(ptr, 8); 
    size=align(size+w);
    if(size<32) size=32;//Minimum size of a freenode can be 32 bytes

    dbg_printf("\n\nMalloc starts for size:%zu\n", size);
    //Run the heap consistency checker
    mm_checkheap(__LINE__);
    dbg_printf("Before malloc:\n");    
    printheap(__LINE__);
    void* payload_ptr=finder(ptr, size);
    dbg_printf("After malloc:\n");
    printheap(__LINE__);
    dbg_printf("Returned at end of malloc: %p\n",payload_ptr);
    mm_checkheap(__LINE__);

    return payload_ptr;
}

void free(void* ptr)
{
    if (ptr!=NULL){
        dbg_printf("\n\nTo free:%p\n", ptr);
        mm_checkheap(__LINE__);
        printheap(__LINE__);
        dbg_assert(in_heap(ptr));
        free_hf(n2h(ptr));
        
        dbg_printf("After free:\n");
        printheap(__LINE__);
        mm_checkheap(__LINE__);        
    }

    return;
}

void* realloc(void* oldptr, size_t size)
{
    if(oldptr==NULL){
        return malloc(size);
        
    }
    else if(size==0){
        free(oldptr);
    }
    else{
        void* newptr=malloc(size);
        size_t oldsize=get_size(decr(oldptr,w));
        size_t minsize=size>oldsize?oldsize:size;
        memcpy(newptr, oldptr, minsize);
        return newptr;
    }

    return NULL;
}

void* calloc(size_t nmemb, size_t size)
{
    void* ptr;
    size *= nmemb;
    ptr = malloc(size);
    if (ptr) {
        memset(ptr, 0, size);
    }
    return ptr;
}

void freechecker()
{
#ifdef DEBUG
    int useful_heads=0;
    for (int index=0;index<maxindex;index++){
        if(head[index]!=NULL){
            Node x=head[index];
            do{
                void* header=n2h(x);
                dbg_assert(in_heap(x));
                dbg_assert(!is_alloc(header));
                x=x->next;
                
            }while(x!=head[index]);
            useful_heads++;
        }  
    }
    // dbg_printf("\n\n Non-empty lists:%d\n", useful_heads);
#endif
    return;
}

bool mm_checkheap(int line_number)
{
#ifdef DEBUG
    
    void* ptr=mm_heap_lo();
    ptr=incr(ptr, w); 
    size_t block_size=get_size(ptr);
    int prev=0;
    int curr;
    // int block_num=0;

    //Check to see if all free nodes are actually free
    // freechecker();

    while(block_size!=0)
    {
        //2) Check to see if all header ptrs are in heap
        dbg_assert(in_heap(ptr));

        if (!is_alloc(ptr) ){ //checks free blocks to verify if header size=footer size
            dbg_assert(block_size==get_size(get_f(ptr)));
            dbg_assert(aligned(incr(ptr,w)));
            dbg_assert(in_heap(h2n(ptr)));
        }

        //3) Check to see if prev_alloc bit is set correctly
        curr=get_prev_alloc(ptr);

        // Print block allocation information if needed
        //dbg_printf("For block %d: %d, %d, %p, %p\n", block_num, prev, curr, ptr, mm_heap_hi());
        dbg_assert(prev==curr);
        prev=is_alloc(ptr);
        //4) Check that no consecutive blocks are free
        dbg_assert(!(prev==0 && curr==0)); 

        ptr=incr(ptr,block_size);
        block_size=get_size(ptr);
    }
//5)Looping by adding block_size to header gives the next block's header. 
//If blocks overlap, then incr(header, get_size(header)) will point outside the heap throwing an assertion

#endif // DEBUG
    return true;
}
