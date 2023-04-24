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


/*是否使用segregated lists*/
#define SEGREGATE
/*下面三选一*/
// #define FIRST_FIT__AND_INSERT_HEAD
#define FIRST_FIT__AND_INSERT_TAIL
// #define BEST_FIT

#define max(a,b) ((a)>(b)?(a):(b))

#define GET(p) (*(unsigned int*)(p))
#define PUT(p,val) (*(unsigned int*)(p)=(val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HEAD(p) ((char*)(p)-4)
#define TAIL(p) ((char*)(p)+GET_SIZE(HEAD(p)))

#define NEXT_P(p) ((char*)(p)+GET_SIZE(HEAD(p))+8)
#define PRE_P(p) ((char*)(p)-8- GET_SIZE((char*)(p)-8) )

#define NEXT_LIST_P(p) (mem_heap_lo()+GET(p))
#define PRE_LIST_P(p) (mem_heap_lo()+GET((char*)(p)+4))

#ifdef SEGREGATE
#define INIT_SIZE (8*10)
#define LIST_BEGIN(p) (mem_heap_lo()+((p)-2)*8)
#define LIST_END(p) (mem_heap_lo()+((p)-2)*8)
#else
#define INIT_SIZE 8
#define LIST_BEGIN mem_heap_lo()
#define LIST_END mem_heap_lo()
#endif


/*
[2^2,2^3),[2^3,2^4),...,[2^10,2^11)  ,  [2^11,2^32)
[2^p,2^(p+1))  ,(2<=p<=10)
[2^11,2^32)    ,(p=11)
*/

/*
 * mm_init - Called when a new trace starts.
 */
#ifdef SEGREGATE
int mm_init(void){
	// printf("\ninit %llx %llx %llx %llx\n",mem_heap_lo(),mem_heap_hi(),mem_heapsize(),mem_sbrk(0));
	mem_sbrk(INIT_SIZE);//p=mem_heap_lo()
	void *heap_begin=mem_heap_lo();
	for(int i=2;i<=11;i++){
		PUT(LIST_BEGIN(i),LIST_END(i)-heap_begin);
		PUT(LIST_END(i)+4,LIST_BEGIN(i)-heap_begin);
	}
	return 0;
}
static inline int GetListId(unsigned int size){
	if(size>=(1<<11))return 11;
	if(size<(1<<6)){//[2,5]
		if(size<(1<<4)){//[2,3]
			if((size>>3)&1)return 3;
			if((size>>2)&1)return 2;
		}
		else {//[4,5]
			if((size>>5)&1)return 5;
			if((size>>4)&1)return 4;
		}
	}
	else {//[6,10]
		if(size<(1<<8)){//[6,7]
			if((size>>7)&1)return 7;
			if((size>>6)&1)return 6;
		}
		else {//[8,10]
			if((size>>10)&1)return 10;
			if((size>>9)&1)return 9;
			if((size>>8)&1)return 8;
		}
	}
	// for(int i=10;i>=2;i--)if((size>>i)&1)return i;
	return -1;
}
static void AddToExplicitList(void *ptr){
	int id=GetListId(GET_SIZE(HEAD(ptr)));
	void *ptr2=NEXT_LIST_P(LIST_BEGIN(id));
	// printf("AddToExplicitList: ptr=%llx,ptr2=%llx\n",ptr,ptr2);
	void *heap_begin=mem_heap_lo();
	PUT(LIST_BEGIN(id),ptr-heap_begin),PUT(ptr+4,LIST_BEGIN(id)-heap_begin);
	PUT(ptr,ptr2-heap_begin),PUT(ptr2+4,ptr-heap_begin);
}
#else
int mm_init(void){
	// printf("\ninit %llx %llx %llx %llx\n",mem_heap_lo(),mem_heap_hi(),mem_heapsize(),mem_sbrk(0));
	mem_sbrk(INIT_SIZE);//p=mem_heap_lo()
	PUT(LIST_BEGIN,LIST_END-mem_heap_lo());//记录的是与mem_heap_lo()的插值 (2^32 bit)
	PUT(LIST_END+4,LIST_BEGIN-mem_heap_lo());
	return 0;
}
static void AddToExplicitList(void *ptr){
	void *ptr2=NEXT_LIST_P(LIST_BEGIN);
	// printf("AddToExplicitList: ptr=%llx,ptr2=%llx\n",ptr,ptr2);
	PUT(LIST_BEGIN,ptr-mem_heap_lo()),PUT(ptr+4,LIST_BEGIN-mem_heap_lo());
	PUT(ptr,ptr2-mem_heap_lo()),PUT(ptr2+4,ptr-mem_heap_lo());
}
#endif
static void DeleteFromExplicitList(void *ptr){
	void *preP=PRE_LIST_P(ptr);
	void *nextP=NEXT_LIST_P(ptr);
	// printf("DeleteFromExplicitList: ptr=%llx,preP=%llx,nextP=%llx\n",ptr,preP,nextP);
	PUT(preP,nextP-mem_heap_lo()),PUT(nextP+4,preP-mem_heap_lo());
}




static void *extend_heap(size_t size){
	unsigned int newsize=ALIGN(size);
	unsigned char *p=mem_sbrk(newsize+8);
	if ((long)p < 0)return NULL;
	//malloc前8字节分别记录上个块的脚部和这个块的头部，接着是分配给用户的空间(这个块的尾部直接溢出到下个块记录)
	//注意，对于一个已经被释放的空闲块，在第9~16字节记录上一个和下一个空闲块在哪里(由于8字节对齐，保证每个块至少有8字节的空间是分配给用户的)
	PUT(p+4,newsize|1);
	PUT(p+8+newsize,newsize|1);
	// printf("p=%llx,SIZE_PTR(p)=%llx\n",p,SIZE_PTR(p));
	// printf("malloc %d: %llx\n",size,p+8);
	// printf("make %llx %llx\n",p+4,p+8+newsize);
	return p+8;
}
static void* SPLIT(void *p,unsigned int size1){
	unsigned int size2=GET_SIZE(HEAD(p))-size1-8;
	bool flag=1;
	if((size1&size2)*2>max(size1,size2))flag=0; //最高位相同，就不重新delete再add了
	if(flag)DeleteFromExplicitList(p);
	PUT(p+size2+4,size1|1);
	PUT(TAIL(p),size1|1);
	PUT(HEAD(p),size2|0);
	PUT(p+size2,size2|0);
	if(flag)AddToExplicitList(p);
	return p+size2+8;
}

/*
 * malloc - Allocate a block by incrementing the brk pointer.
 *			Always allocate a block whose size is a multiple of the alignment.
 */
#ifdef SEGREGATE
void *malloc(size_t size){
	if(size==0)return NULL;
	// printf("%llx %llx %llx %llx\n",mem_heap_lo(),mem_heap_hi(),mem_heapsize(),mem_sbrk(0));
	#ifdef FIRST_FIT__AND_INSERT_HEAD
	{//first fit;等价于insert new free block into head
		int id=GetListId(ALIGN(size));
		while(id<=11){
			void *currentp=NEXT_LIST_P(LIST_BEGIN(id));
			while(currentp!=LIST_END(id)){
				// printf("currentp: %llx\n",currentp);
				if(GET_SIZE(HEAD(currentp))>=ALIGN(size)){
					// printf("check %llx %llx\n",HEAD(currentp),TAIL(currentp));
					if(GET_SIZE(HEAD(currentp))>ALIGN(size)+8)currentp=SPLIT(currentp,ALIGN(size));
					else {
						PUT(HEAD(currentp),GET_SIZE(HEAD(currentp))|1);
						PUT(TAIL(currentp),GET_SIZE(TAIL(currentp))|1);
						DeleteFromExplicitList(currentp);
					}
					// printf("!!! malloc %d: %llx\n",size,currentp);
					return currentp;
				}
				currentp=NEXT_LIST_P(currentp);
			}
			id++;
		}
	}
	#endif
	#ifdef FIRST_FIT__AND_INSERT_TAIL
	{//first fit;等价于insert new free block into tail
		int id=GetListId(ALIGN(size));
		while(id<=11){
			// printf("size=%u,id=%d\n",size,id);
			void *currentp=PRE_LIST_P(LIST_END(id));
			while(currentp!=LIST_BEGIN(id)){
				// printf("currentp: %llx\n",currentp);
				if(GET_SIZE(HEAD(currentp))>=ALIGN(size)){
					// printf("check %llx %llx\n",HEAD(currentp),TAIL(currentp));
					if(GET_SIZE(HEAD(currentp))>ALIGN(size)+8)currentp=SPLIT(currentp,ALIGN(size));
					else {
						PUT(HEAD(currentp),GET_SIZE(HEAD(currentp))|1);
						PUT(TAIL(currentp),GET_SIZE(TAIL(currentp))|1);
						DeleteFromExplicitList(currentp);
					}
					// printf("!!! malloc %d: %llx\n",size,currentp);
					return currentp;
				}
				currentp=PRE_LIST_P(currentp);
			}
			id++;
		}
	}
	#endif
	#ifdef BEST_FIT
	{//best fit
		int id=GetListId(ALIGN(size));
		while(id<=11){
			void *currentp=NEXT_LIST_P(LIST_BEGIN(id));
			void *bestP=NULL;
			while(currentp!=LIST_END(id)){
				// printf("currentp: %llx\n",currentp);
				if(!GET_ALLOC(HEAD(currentp)) && GET_SIZE(HEAD(currentp))>=ALIGN(size)){
					if(bestP==NULL || GET_SIZE(HEAD(currentp))<GET_SIZE(HEAD(bestP)))bestP=currentp;
				}
				currentp=NEXT_LIST_P(currentp);
			}
			if(bestP!=NULL){
				if(GET_SIZE(HEAD(bestP))>ALIGN(size)+8)bestP=SPLIT(bestP,ALIGN(size));
				else {
					PUT(HEAD(bestP),GET_SIZE(HEAD(bestP))|1);
					PUT(TAIL(bestP),GET_SIZE(TAIL(bestP))|1);
					DeleteFromExplicitList(bestP);
				}
				// printf("!!! malloc %d: %llx\n",size,bestP);
				return bestP;
			}
			id++;
		}
	}
	#endif
	return extend_heap(size);
}
static bool try_merge(void *ptr1,void *ptr2){
	// printf("try_merge: %llx %llx\n",ptr1,ptr2);
	if(GET_ALLOC(HEAD(ptr1)) || GET_ALLOC(HEAD(ptr2)) ) return 0;
	// printf("merge: %llx %llx\n",ptr1,ptr2);
	unsigned int totsize=GET_SIZE(HEAD(ptr1))+GET_SIZE(HEAD(ptr2))+8;
	PUT(HEAD(ptr1),totsize|0);
	PUT(TAIL(ptr2),totsize|0);
	DeleteFromExplicitList(ptr1);
	DeleteFromExplicitList(ptr2);
	AddToExplicitList(ptr1);
	return 1;
}
#else
int totNum=0,totSum=0;
void *malloc(size_t size){
	if(size==0)return NULL;
	// printf("%llx %llx %llx %llx\n",mem_heap_lo(),mem_heap_hi(),mem_heapsize(),mem_sbrk(0));
	#ifdef FIRST_FIT__AND_INSERT_HEAD
	{//first fit;等价于insert new free block into head
		void *currentp=NEXT_LIST_P(LIST_BEGIN);
		while(currentp!=LIST_END){
			// printf("currentp: %llx\n",currentp);
			if(GET_SIZE(HEAD(currentp))>=ALIGN(size)){
				// printf("check %llx %llx\n",HEAD(currentp),TAIL(currentp));
				if(GET_SIZE(HEAD(currentp))>ALIGN(size)+8)currentp=SPLIT(currentp,ALIGN(size));
				else {
					PUT(HEAD(currentp),GET_SIZE(HEAD(currentp))|1);
					PUT(TAIL(currentp),GET_SIZE(TAIL(currentp))|1);
					DeleteFromExplicitList(currentp);
				}
				// printf("!!! malloc %d: %llx\n",size,currentp);
				return currentp;
			}
			currentp=NEXT_LIST_P(currentp);
		}
	}
	#endif
	#ifdef FIRST_FIT__AND_INSERT_TAIL
	{//first fit;等价于insert new free block into tail
		totNum++;
		void *currentp=PRE_LIST_P(LIST_END);
		while(currentp!=LIST_BEGIN){
			totSum++;
			// printf("currentp: %llx\n",currentp);
			if(GET_SIZE(HEAD(currentp))>=ALIGN(size)){
				// printf("check %llx %llx\n",HEAD(currentp),TAIL(currentp));
				if(GET_SIZE(HEAD(currentp))>ALIGN(size)+8)currentp=SPLIT(currentp,ALIGN(size));
				else {
					PUT(HEAD(currentp),GET_SIZE(HEAD(currentp))|1);
					PUT(TAIL(currentp),GET_SIZE(TAIL(currentp))|1);
					DeleteFromExplicitList(currentp);
				}
				// printf("!!! malloc %d: %llx\n",size,currentp);
				return currentp;
			}
			currentp=PRE_LIST_P(currentp);
		}
		if(totNum%10000==0)printf("totNum=%d,totSum/totNum=%lf\n",totNum,1.0*totSum/totNum);
	}
	#endif
	#ifdef BEST_FIT
	{//best fit
		void *currentp=NEXT_LIST_P(LIST_BEGIN);
		void *bestP=NULL;
		while(currentp!=LIST_END){
			// printf("currentp: %llx\n",currentp);
			if(!GET_ALLOC(HEAD(currentp)) && GET_SIZE(HEAD(currentp))>=ALIGN(size)){
				if(bestP==NULL || GET_SIZE(HEAD(currentp))<GET_SIZE(HEAD(bestP)))bestP=currentp;
			}
			currentp=NEXT_LIST_P(currentp);
		}
		if(bestP!=NULL){
			if(GET_SIZE(HEAD(bestP))>ALIGN(size)+8)bestP=SPLIT(bestP,ALIGN(size));
			else {
				PUT(HEAD(bestP),GET_SIZE(HEAD(bestP))|1);
				PUT(TAIL(bestP),GET_SIZE(TAIL(bestP))|1);
				DeleteFromExplicitList(bestP);
			}
			// printf("!!! malloc %d: %llx\n",size,bestP);
			return bestP;
		}
	}
	#endif
	return extend_heap(size);
}
static bool try_merge(void *ptr1,void *ptr2){
	// printf("try_merge: %llx %llx\n",ptr1,ptr2);
	if(GET_ALLOC(HEAD(ptr1)) || GET_ALLOC(HEAD(ptr2)) ) return 0;
	// printf("merge: %llx %llx\n",ptr1,ptr2);
	unsigned int totsize=GET_SIZE(HEAD(ptr1))+GET_SIZE(HEAD(ptr2))+8;
	PUT(HEAD(ptr1),totsize|0);
	PUT(TAIL(ptr2),totsize|0);
	DeleteFromExplicitList(ptr2);
	return 1;
}
#endif
/*
 * free - We don't know how to free a block.	So we ignore this call.
 *			Computers have big memories; surely it won't be a problem.
 */
void free(void *ptr){
	/*Get gcc to be quiet */
	if(ptr==NULL)return;
	// printf("free %llx\n",ptr);
	PUT(HEAD(ptr),GET_SIZE(HEAD(ptr))|0);
	PUT(TAIL(ptr),GET_SIZE(TAIL(ptr))|0);
	AddToExplicitList(ptr);
	if(ptr!=mem_heap_lo()+INIT_SIZE+8){
		void *ptr_pre=PRE_P(ptr);
		if(try_merge(ptr_pre,ptr))ptr=ptr_pre;
	}
	if((void*)NEXT_P(ptr)<=mem_heap_hi()){
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
#ifdef SEGREGATE
void mm_checkheap(int verbose){
	/*Get gcc to be quiet. */
	printf("-------begin check-------\n");
	for(int i=2;i<=11;i++){
		void *pre_p=LIST_BEGIN(i),*p=NEXT_LIST_P(pre_p);
		while(p!=LIST_END(i)){
			printf("%llx\n",(unsigned long long)p);
			if(PRE_LIST_P(p)!=pre_p){
				printf("Wrong !!!\n");
				assert(0);
			}
			pre_p=p;
			p=NEXT_LIST_P(p);
		}
	}
	printf("-------end check-------\n");
	verbose=verbose;
}
#else
void mm_checkheap(int verbose){
	/*Get gcc to be quiet. */
	printf("-------begin check-------\n");
	void *pre_p=LIST_BEGIN,*p=NEXT_LIST_P(pre_p);
	while(p!=LIST_END){
		printf("%llx\n",(unsigned long long)p);
		if(PRE_LIST_P(p)!=pre_p){
			printf("Wrong !!!\n");
			assert(0);
		}
		pre_p=p;
		p=NEXT_LIST_P(p);
	}
	printf("-------end check-------\n");
	verbose=verbose;
}
#endif