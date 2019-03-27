/* 
 * Simple, 32-bit and 64-bit clean allocator based on an implicit free list,
 * first fit placement, and boundary tag coalescing, as described in the
 * CS:APP3e text.  Blocks are aligned to double-word boundaries.  This
 * yields 8-byte aligned blocks on a 32-bit processor, and 16-byte aligned
 * blocks on a 64-bit processor.  However, 16-byte alignment is stricter
 * than necessary; the assignment only requires 8-byte alignment.  The
 * minimum block size is four words.
 *
 * This allocator uses the size of a pointer, e.g., sizeof(void *), to
 * define the size of a word.  This allocator also uses the standard
 * type uintptr_t to define unsigned integers that are the same size
 * as a pointer, i.e., sizeof(uintptr_t) == sizeof(void *).
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
	/* Team name */
	"Ctrl Alt Del",
	/* First member's full name */
	"Kyran Adams",
	/* First member's NetID */
	"kpa1",
	/* Second member's full name (leave blank if none) */
	"Alex Bluestein",
	/* Second member's NetID (leave blank if none) */
	"arb19"
};

/* Basic constants and macros: */
#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define CHUNKSIZE  (1 << 12)      /* Extend heap by this amount (bytes) */
#define NUM_SEG (16)
#define MAX(x, y)  ((x) > (y) ? (x) : (y))  

/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p. */
#define GET_SIZE(p)   (GET(p) & ~(WSIZE - 1))
#define GET_NEXT_FREE(p) (GET(p + WSIZE))
#define PUT_NEXT_FREE(p, val) (PUT(p + WSIZE, val))
#define GET_PREV_FREE(p) (GET(p + WSIZE))
#define PUT_PREV_FREE(p, val) (PUT(p + WSIZE, val))
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp)  ((char *)(bp) - DSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - 2*DSIZE)
#define HDRLINK(bp)  ((char *)(bp) - WSIZE)

/* Given block ptr bp, compute address of next and previous blocks. */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - DSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - 2*DSIZE)))

/* Global variables: */
static char *heap_listp; /* Pointer to first block */  

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* Function prototypes for heap consistency checker routines: */
static bool checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp); 

const int should_check = 0;
const int check_verbose = 0;

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 */
int
mm_init(void) 
{
	/* Create the initial empty heap. */
	if ((heap_listp = mem_sbrk((6 + NUM_SEG) * WSIZE)) == (void *)-1)
		return (-1);
	PUT(heap_listp, PACK(NUM_SEG*WSIZE + 2*DSIZE, 1)); /* Prologue header */ 
	PUT(heap_listp + (1 * WSIZE), 0); 
	int num_seg_rounded = (NUM_SEG + (8 - 1)) & ~(8 - 1);
	int i;
	for (i = 0; i < num_seg_rounded; i++) {
		PUT(heap_listp + ((2 + i) * WSIZE), 0); /* Segment pointer */ 
	}
	PUT(heap_listp + ((2 + NUM_SEG) * WSIZE), PACK(NUM_SEG*WSIZE + 2*DSIZE, 1)); /* Prologue footer */ 
	PUT(heap_listp + ((3 + NUM_SEG) * WSIZE), 0);
	PUT(heap_listp + ((4 + NUM_SEG) * WSIZE), PACK(0, 1));     /* Epilogue header */
	PUT(heap_listp + ((5 + NUM_SEG) * WSIZE), PACK(0, 1));     /* Epilogue header */
	heap_listp += (2 * WSIZE);

	if (should_check)
		checkheap(check_verbose);

	/* Extend the empty heap with a free block of CHUNKSIZE bytes. */
	if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
		return (-1);

	if (should_check)
		checkheap(check_verbose);

	return (0);
}

/*
 * Given a size, returns a pointer to the segregation list for that size
 */
void *
get_segregation(size_t size)
{
        // Size classes: 1-2, 3, 4, 5-8, 9-16, 17-32, 33-64, 65-128, 129-256, 
        // 257-512, 513-1024, 1025-2048, 2049-4096, 4097-8192, 8193-inf
	size -= 2*DSIZE + WSIZE;

	void* p;
	if (size <= 256) {
		if (size <= 2) {
			p = heap_listp + WSIZE;
		} else if (size <= 4) {
			p = heap_listp + 2 * WSIZE;
		}  else if (size <= 6) {
			p = heap_listp + 3 * WSIZE;
		}  else if (size <= 8) {
			p = heap_listp + 4 * WSIZE;
		}  else if (size <= 16) {
			p = heap_listp + 5 * WSIZE;
		}  else if (size <= 32) {
			p = heap_listp + 6 * WSIZE;
		}  else if (size <= 64) {
			p = heap_listp + 7 * WSIZE;
		}  else if (size <= 128) {
			p = heap_listp + 8 * WSIZE;
		}  else  {
			p = heap_listp + 9 * WSIZE;
		}  
	} 
	else if (size <= 8192) {
		if (size <= 512) {
			p = heap_listp + 10 * WSIZE;
		}  else if (size <= 1024) {
			p = heap_listp + 11 * WSIZE;
		}  else if (size <= 2056) {
			p = heap_listp + 12 * WSIZE;
		}  else if (size <= 4096) {
			p = heap_listp + 13 * WSIZE;
		} else if (size <= 8192){
			p = heap_listp + 14 * WSIZE;
		} 
	}
	else {
		p = heap_listp + 15 * WSIZE;
	}
	
	return p;
}

/*
 * Adds this block to the segregation lists
 */
void seg_block(void *bp)
{
	uintptr_t seg_ptr = (uintptr_t) get_segregation(GET_SIZE(HDRP(bp)));
	/*if (GET(seg_ptr) != 0) {
		PUT_PREV_FREE(FTRP(GET(seg_ptr)), (uintptr_t) bp);
	}
	PUT_NEXT_FREE(HDRP(bp), GET(seg_ptr));
	PUT(seg_ptr, (uintptr_t)bp);
	PUT_PREV_FREE(FTRP(bp), 0);*/
	if (GET(seg_ptr) == 0) {
		PUT_NEXT_FREE(HDRP(bp), (uintptr_t) bp);
		PUT(seg_ptr, (uintptr_t) bp);
		PUT_PREV_FREE(FTRP(bp), (uintptr_t) bp);
	} else {
		PUT_NEXT_FREE(HDRP(GET_PREV_FREE(FTRP(GET(seg_ptr)))), (uintptr_t) bp);
		PUT_PREV_FREE(FTRP(bp), GET_PREV_FREE(FTRP(GET(seg_ptr))));
		PUT_NEXT_FREE(HDRP(bp), GET(seg_ptr));
		PUT_PREV_FREE(FTRP(GET(seg_ptr)), (uintptr_t) bp);
		PUT(seg_ptr, (uintptr_t) bp);
	}
}

void remove_freelist(void *bp) {
	void *prev = (void*) GET_PREV_FREE(FTRP(bp));
	void *next = (void*) GET_NEXT_FREE(HDRP(bp));

	if (check_verbose)
		printf("remove_freelist(%p) prev=%p next=%p\n", bp, prev, next);

	void *seg = get_segregation(GET_SIZE(HDRP(bp)));
	if (next == bp) {
		PUT(seg, 0);
	} else {
		PUT_NEXT_FREE(HDRP(prev), (uintptr_t) next);
		PUT_PREV_FREE(FTRP(next), (uintptr_t) prev);
		if ((void*) GET(seg) == bp) {
			PUT(seg, (uintptr_t) next);
		}
	}
		
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Allocate a block with at least "size" bytes of payload, unless "size" is
 *   zero.  Returns the address of this block if the allocation was successful
 *   and NULL otherwise.
 */
void *
mm_malloc(size_t size) 
{
	if (check_verbose)
		printf("mm_malloc(%d)\n", (int) size);

	size_t asize;      /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	void *bp;

 	/* Ignore spurious requests. */
	if (size == 0)
		return (NULL);

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= WSIZE)
		asize = 2 * DSIZE + WSIZE;
	else
		asize = WSIZE * ((size + 2*DSIZE + (WSIZE - 1)) / WSIZE);

	/* Search the free list for a fit. */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);

		if (should_check)
			checkheap(check_verbose);

		return (bp);
	}

	/* No fit found.  Get more memory and place the block. */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)  
		return (NULL);
	place(bp, asize);
	
	if (should_check)
		checkheap(check_verbose);

	return (bp);
} 

/* 
 * Requires:
 *   "bp" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Free a block.
 */
void
mm_free(void *bp)
{
	if (check_verbose)
		printf("mm_free(%p)\n", bp);
	size_t size;

	/* Ignore spurious requests. */
	if (bp == NULL)
		return;

	/* Free and coalesce the block. */
	size = GET_SIZE(HDRP(bp));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	
	coalesce(bp);

	if (should_check)
		checkheap(check_verbose);
}

/*
 * Requires:
 *   "ptr" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Reallocates the block "ptr" to a block with at least "size" bytes of
 *   payload, unless "size" is zero.  If "size" is zero, frees the block
 *   "ptr" and returns NULL.  If the block "ptr" is already a block with at
 *   least "size" bytes of payload, then "ptr" may optionally be returned.
 *   Otherwise, a new block is allocated and the contents of the old block
 *   "ptr" are copied to that new block.  Returns the address of this new
 *   block if the allocation was successful and NULL otherwise.
 */
void *
mm_realloc(void *ptr, size_t size)
{
	if (check_verbose)
		printf("mm_realloc\n");
	size_t oldsize = GET_SIZE(HDRP(ptr));
	void *newptr;

	/* If size == 0 then this is just free, and we return NULL. */
	if (size == 0) {
		mm_free(ptr);
		return (NULL);
	}

	/* If oldptr is NULL, then this is just malloc. */
	if (ptr == NULL)
		return (mm_malloc(size));

	if (size + 2*DSIZE <= oldsize) {
		return ptr;
	}
	void *nextblk = NEXT_BLKP(ptr);
	void *prevblk = PREV_BLKP(ptr);
	if (nextblk != NULL && 
	    !GET_ALLOC(HDRP(nextblk)) && 
	    GET_SIZE(HDRP(nextblk)) + oldsize >= size + 2*DSIZE) {
		int newsize = GET_SIZE(HDRP(nextblk)) + oldsize;
		remove_freelist(nextblk);
		PUT(HDRP(ptr), PACK(newsize, 1));
		PUT(FTRP(ptr), PACK(newsize, 1));
		return ptr;
	} else if (prevblk != NULL && 
		   !GET_ALLOC(HDRP(prevblk)) && 
		   GET_SIZE(HDRP(prevblk)) + oldsize >= size + 2*DSIZE) {
		int newsize = GET_SIZE(HDRP(prevblk)) + oldsize;
		remove_freelist(prevblk);
		PUT(HDRP(prevblk), PACK(newsize, 1));
		PUT(FTRP(prevblk), PACK(newsize, 1));
		memmove(prevblk, ptr, oldsize - DSIZE);
		return prevblk;
	} else if (nextblk != NULL && prevblk != NULL && 
		   !GET_ALLOC(HDRP(nextblk)) && !GET_ALLOC(HDRP(prevblk)) && 
		   GET_SIZE(HDRP(prevblk)) + oldsize + GET_SIZE(HDRP(nextblk)) >= size + 2*DSIZE) {
		int newsize = GET_SIZE(HDRP(prevblk)) + oldsize + GET_SIZE(HDRP(nextblk));
		remove_freelist(prevblk);
		remove_freelist(nextblk);
		PUT(HDRP(prevblk), PACK(newsize, 1));
		PUT(FTRP(prevblk), PACK(newsize, 1));
		memmove(prevblk, ptr, oldsize - DSIZE);
		return prevblk;
	}

	/* If we are the last block, just extend and coalesce */
	/*if (NEXT_BLKP(HDRP(ptr)) == NULL) {
		size_t asize = size - GET_SIZE(HDRP(ptr));
		mm_free(ptr);
	        int extendsize = MAX(asize, CHUNKSIZE);
		if ((ptr = extend_heap(extendsize / WSIZE)) == NULL)  
			return (NULL);
		ptr = coalesce(ptr);
		place(ptr, size);
		return ptr;
		}*/
	size = MAX(size, 2*oldsize);

	newptr = mm_malloc(size);

	/* If realloc() fails the original block is left untouched  */
	if (newptr == NULL)
		return (NULL);

	/* Copy the old data. */
	oldsize = GET_SIZE(HDRP(ptr));
	if (size < oldsize)
		oldsize = size;
	memcpy(newptr, ptr, oldsize);

	/* Free the old block. */
	mm_free(ptr);

	return (newptr);
}



/*
 * The following routines are internal helper routines.
 */

/*
 * Requires:
 *   "bp" is the address of a newly freed block, not in the free list.
 *
 * Effects:
 *   Perform boundary tag coalescing.  Returns the address of the coalesced
 *   block.
 */
static void *
coalesce(void *bp) 
{
	if (check_verbose)
		printf("coalesce(%p)\n", bp);
	size_t size = GET_SIZE(HDRP(bp));
	bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

	if (check_verbose)
		printf("coalescing w/ size=%d prev=%d next=%d\n", (int) size, (int) prev_alloc, (int) next_alloc);

	if (prev_alloc && next_alloc) {                 /* Case 1 */
		seg_block(bp);
	} else if (prev_alloc && !next_alloc) {         /* Case 2 */
		remove_freelist(NEXT_BLKP(bp));
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		seg_block(bp);
	} else if (!prev_alloc && next_alloc) {         /* Case 3 */
		remove_freelist(PREV_BLKP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	        
		seg_block(bp);
	} else {                                        /* Case 4 */
		remove_freelist(PREV_BLKP(bp));
		remove_freelist(NEXT_BLKP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
		    GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
		seg_block(bp);
	}
	if (should_check)
		checkheap(check_verbose);

	return (bp);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Extend the heap with a free block and return that block's address.
 */
static void *
extend_heap(size_t words) 
{
	if (check_verbose)
		printf("extend_heap(%d)\n", (int) words);
	size_t size;
	void *bp;

	/* Allocate an even number of words to maintain alignment. */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if ((bp = mem_sbrk(size)) == (void *)-1)  
		return (NULL);

	/* Initialize free block header/footer and the epilogue header. */
	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
	PUT(HDRP(NEXT_BLKP(bp)) + WSIZE, PACK(0, 1)); /* New epilogue header */

	/* Coalesce if the previous block was free. */
	bp = (coalesce(bp));

        if (should_check)
		checkheap(check_verbose);

	return bp;
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Find a fit for a block with "asize" bytes.  Returns that block's address
 *   or NULL if no suitable block was found.
 */
static void *
find_fit(size_t asize)
{
	if (check_verbose)
		printf("find_fit\n");
	// If there is one element in the list, check if it fits
	void *firstcheck = (void*) GET(get_segregation(asize));
	if (firstcheck != NULL && asize <= GET_SIZE(HDRP(firstcheck))) {
		return (firstcheck);
	}
	// otherwise start at the NEXT segregation to improve perf
	void *seg = get_segregation(asize);
	if (seg < (void*)((NUM_SEG - 1) * WSIZE + heap_listp)) {
		seg += WSIZE;
	}
	void *last_seg = NUM_SEG * WSIZE + heap_listp; 
	for (; seg < last_seg; seg += WSIZE) {
		void *bp;
		/* Search for the first fit. */
		void *startBp = NULL;
		for (bp = (void*) GET(seg); bp != startBp; bp = (void*) GET_NEXT_FREE(HDRP(bp))) {
			if (asize <= GET_SIZE(HDRP(bp))) {
				PUT(seg, (uintptr_t) GET_NEXT_FREE(HDRP(bp)));
				return (bp);
			}
			startBp = (void*) GET(seg);
		}
	}

	/* No fit was found. */
	return (NULL);
}

/* 
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 *
 * Effects:
 *   Place a block of "asize" bytes at the start of the free block "bp" and
 *   split that block if the remainder would be at least the minimum block
 *   size. 
 */
static void
place(void *bp, size_t asize)
{
	if (check_verbose)
		printf("place\n");
	if (should_check) {
		checkheap(check_verbose);
	}
	size_t csize = GET_SIZE(HDRP(bp));   

        remove_freelist(bp);

	if ((csize - asize) >= (2 * DSIZE + WSIZE) + 128) { 
	//if (csize > asize*2 && (csize - asize) >= (2 * DSIZE + WSIZE)) {
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(HDRLINK(bp), 0);
		PUT(FTRP(bp), PACK(asize, 1));
		// Create new free block
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));
		seg_block(bp);
	} else {
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(HDRLINK(bp), 0);
		PUT(FTRP(bp), PACK(csize, 1));
	}
	if (should_check)
		checkheap(check_verbose);

}

/* 
 * The remaining routines are heap consistency checker routines. 
 */

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */
static bool
checkblock(void *bp) 
{
	bool was_error = false;
	if (!GET_ALLOC(HDRP(bp))) {
		int found = 0;
		void *startP = NULL;
		void* p = (void*)GET(get_segregation(GET_SIZE(HDRP(bp))));
		while (p != startP) {
			if (p == bp) {
				found = 1;
				break;
			}
			p = (void*)GET_NEXT_FREE(HDRP(p));
			startP = (void*)GET(get_segregation(GET_SIZE(HDRP(bp))));
		}
		if (!found) {
			printf("Error: Free block %p is not in the segregation list\n", bp);
			was_error = true;
		}

	}
	if ((uintptr_t)bp % WSIZE) {
		printf("Error: %p is not word aligned\n", bp);
		was_error = true;
	}
	if (GET(HDRP(bp)) != GET(FTRP(bp))) {
		printf("Error: header does not match footer, was %d != %d\n",
		       (int)GET(HDRP(bp)), (int)GET(FTRP(bp)));
		was_error = true;
	}
	return was_error;
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a minimal check of the heap for consistency. 
 */
void
checkheap(bool verbose) 
{
	void *bp;
	int was_error = false;

	if (verbose)
		printf("Heap (%p):\n", heap_listp);

	if (GET_SIZE(HDRP(heap_listp)) != WSIZE*NUM_SEG + 2*DSIZE) {
		printf("Bad prologue header: HDRP size was %d\n", (int)GET_SIZE(HDRP(heap_listp)));
		was_error = true;
	}
	if (!GET_ALLOC(HDRP(heap_listp))) {
		was_error = true;
		printf("Bad prologue header: Was unallocated\n");
	}
	checkblock(heap_listp);
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (verbose)
			printblock(bp);
		was_error |= checkblock(bp);
	}

	if (verbose)
		printblock(bp);
	if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp))) {
		printf("Bad epilogue header, was %d\n", (int)GET(HDRP(bp)));
		was_error = true;
	}

	int i;
	for (i = 0; i < NUM_SEG; i++) {
		if (verbose)
			printf("Free list %d:\n", i);
		void* p = (void*) GET(heap_listp + i * WSIZE);
		if (p != NULL) {
			int isStart = 1;
			void* startP = p;
			void *prevP = NULL;
			while (isStart || p != startP) {
				//printf("block %p prev=%p next=%p\n", p, (void*) GET_PREV_FREE(FTRP(p)), (void*) GET_NEXT_FREE(HDRP(p)));
				isStart = 0;
				if (verbose)
					printblock(p);
				size_t size = GET_SIZE(HDRP(p));
				if (prevP != NULL && (void*)GET_PREV_FREE(FTRP(p)) != prevP) {
					printf("Block %p had previous block %p but was marked with previous %p.\n", p, prevP, (void*)GET_PREV_FREE(FTRP(p)));
					printf("start: %p\n", startP);
					was_error = true;
				}
				if (prevP != NULL && (void*)GET_NEXT_FREE(HDRP(prevP)) != p) {
					printf("Block %p had next block %p but was marked with next %p.\n", prevP, p, (void*)GET_NEXT_FREE(HDRP(prevP)));
					was_error = true;
				}
				if (get_segregation(size) != heap_listp + i * WSIZE) {
					printf("Block %p was in free list %d but was size %d. Should have been %d\n", p, i, (int)size, (int) (((char*)get_segregation(size) - heap_listp)/WSIZE));
					was_error = true;
				}
				if (GET_ALLOC(HDRP(p))) {
					printf("Block %p was in free list but was not free.\n", p);
					was_error = true;
				}
				prevP = p;
				p = (void*) GET_NEXT_FREE(HDRP(p));
			}
		}
	}
	if (was_error)
		exit(1);
}

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
static void
printblock(void *bp) 
{
	size_t hsize, fsize;
	bool halloc, falloc;

	//checkheap(false);
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));  
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));  

	if (hsize == 0) {
		printf("%p: end of heap\n", bp);
		return;
	}

	printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp, 
	    hsize, (halloc ? 'a' : 'f'), 
	    fsize, (falloc ? 'a' : 'f'));
}
