/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.	Blocks are never coalesced or reused.	The size of
 * a block is found at the first aligned word before the block (we need
 * it for realloc).
 *
 * This code is correct and blazingly fast, but very bad usage-wise since
 * it never frees anything.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.	When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

// 8字节对齐，即块大小二进制表示的低三位一定为0，可以用来记录数据
// 另外保证堆的大小不会超过 2^32,即可以用4字节存储块大小(实际上是 4*8-3 bit)

// #define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// #define SIZE_PTR(p)	((size_t*)(((char*)(p)) - SIZE_T_SIZE))

#define CHUNKSIZE 1024

#define GET(p) (*(unsigned int*)(p))
#define PUT(p,val) (*(unsigned int*)(p)=(val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HEAD(p) ((char*)(p)-4)
#define TAIL(p) ((char*)(p)+GET_SIZE(HEAD(p)))

#define NEXT_P(p) ((char*)(p)+GET_SIZE(HEAD(p))+8)
#define PRE_P(p) ((char*)(p)-8- GET_SIZE((char*)(p)-8) )

/*
 * mm_init - Called when a new trace starts.
 */
int mm_init(void){
	// printf("\ninit %lx %lx %lx %lx\n",mem_heap_lo(),mem_heap_hi(),mem_heapsize(),mem_sbrk(0));
	return 0;
}

/*
 * malloc - Allocate a block by incrementing the brk pointer.
 *			Always allocate a block whose size is a multiple of the alignment.
 */
static void *extend_heap(size_t size){
	unsigned int newsize=ALIGN(size);
	unsigned char *p=mem_sbrk(newsize+8);
	if ((long)p < 0)return NULL;
	//malloc前8字节分别记录上个块的脚部和这个块的头部，接着是分配给用户的空间(这个块的尾部直接溢出到下个块记录)
	PUT(p+4,newsize|1);
	PUT(p+8+newsize,newsize|1);
	// printf("p=%lx,SIZE_PTR(p)=%lx\n",p,SIZE_PTR(p));
	// printf("malloc %d: %lx\n",size,p+8);
	// printf("make %lx %lx\n",p+4,p+8+newsize);
	return p+8;
}
static void SPLIT(void *p,unsigned int size1){
	int size2=GET_SIZE(HEAD(p))-size1-8;
	PUT(p+size1+4,size2|0);
	PUT(TAIL(p),size2|0);
	PUT(HEAD(p),size1|1);
	PUT(p+size1,size1|1);
}

void *malloc(size_t size){
	if(size==0)return NULL;
	// printf("%lx %lx %lx %lx\n",mem_heap_lo(),mem_heap_hi(),mem_heapsize(),mem_sbrk(0));
	void *currentp=mem_heap_lo()+8;
	while(currentp<=mem_heap_hi()){
		// printf("currentp: %lx\n",currentp);
		if(!GET_ALLOC(HEAD(currentp)) && GET_SIZE(HEAD(currentp))>=ALIGN(size)){
			// printf("check %lx %lx\n",HEAD(currentp),TAIL(currentp));
			if(GET_SIZE(HEAD(currentp))>ALIGN(size)+8)SPLIT(currentp,ALIGN(size));
			PUT(HEAD(currentp),GET_SIZE(HEAD(currentp))|1);
			PUT(TAIL(currentp),GET_SIZE(TAIL(currentp))|1);
			// printf("!!! malloc %d: %lx\n",size,currentp);
			return currentp;
		}
		currentp=NEXT_P(currentp);
	}
	return extend_heap(size);
}

static bool try_merge(void *ptr1,void *ptr2){
	// printf("%lx %lx\n",ptr1,ptr2);
	if(GET_ALLOC(HEAD(ptr1)) || GET_ALLOC(HEAD(ptr2)) ) return 0;
	unsigned int totsize=GET_SIZE(HEAD(ptr1))+GET_SIZE(HEAD(ptr2))+8;
	PUT(HEAD(ptr1),totsize|0);
	PUT(TAIL(ptr2),totsize|0);
	return 1;
}
/*
 * free - We don't know how to free a block.	So we ignore this call.
 *			Computers have big memories; surely it won't be a problem.
 */
void free(void *ptr){
	/*Get gcc to be quiet */
	if(ptr==NULL)return;
	// printf("free %lx\n",ptr);
	PUT(HEAD(ptr),GET_SIZE(HEAD(ptr))|0);
	PUT(TAIL(ptr),GET_SIZE(TAIL(ptr))|0);
	if(ptr!=mem_heap_lo()+8){
		void *ptr_pre=PRE_P(ptr);
		if(try_merge(ptr_pre,ptr))ptr=ptr_pre;
	}
	if(NEXT_P(ptr)<=mem_heap_hi()){
		try_merge(ptr,NEXT_P(ptr));
	}
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *			copying its data, and freeing the old block.	I'm too lazy
 *			to do better.
 */
void *realloc(void *oldptr, size_t size){
	size_t oldsize;
	void *newptr;

	/* If size == 0 then this is just free, and we return NULL. */
	if(size == 0) {
		free(oldptr);
		return 0;
	}

	/* If oldptr is NULL, then this is just malloc. */
	if(oldptr == NULL) {
		return malloc(size);
	}

	newptr = malloc(size);

	/* If realloc() fails the original block is left untouched	*/
	if(!newptr) {
		return 0;
	}

	/* Copy the old data. */
	oldsize = GET_SIZE(HEAD(oldptr)); //oldsize为上次实际分配的空间,而size为这次想要分配的空间(但问题不大)
	if(size < oldsize) oldsize = size;
	memcpy(newptr, oldptr, oldsize);

	/* Free the old block. */
	free(oldptr);

	return newptr;
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc (size_t nmemb, size_t size){
	size_t bytes = nmemb * size;
	void *newptr;

	newptr = malloc(bytes);
	memset(newptr, 0, bytes);

	return newptr;
}

/*
 * mm_checkheap - There are no bugs in my code, so I don't need to check,
 *			so nah!
 */
void mm_checkheap(int verbose){
	/*Get gcc to be quiet. */
	verbose = verbose;
}
