/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 * mm-naive.c - 가장 빠르지만, 메모리 효율은 최악인 malloc 패키지입니다.
 *
 * 이 단순한 방식에서는, 블록을 할당할 때 단순히 brk 포인터를 증가시킵니다.
 * 각 블록은 순수한 데이터 영역(payload)만 포함하며, 헤더나 푸터는 존재하지 않습니다.
 * 할당된 블록은 절대 병합(coalesce)되지 않으며, 재사용되지도 않습니다.
 * realloc 함수는 mm_malloc과 mm_free를 이용해 직접 구현됩니다.
 *
 * [학생에게 알림]: 아래의 헤더 주석은 여러분의 솔루션에 대한
 * 높은 수준의 설명으로 대체해야 합니다.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <limits.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "8",
    /* First member's full name */
    "JunPyo Ahn",
    /* First member's email address */
    "asdasd@gmail",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment 
 * 싱글 워드 4 또는 더블 워드 8 조정
*/

#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT 
정렬의 가장 가까운 배수까지 반올림
*/
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
// =====================================================
// 기본 상수와 매크로
#define WSIZE 4        /* 워드 및 헤더/푸터 크기 (바이트) */
#define DSIZE 8        /* 더블 워드 크기 (바이트) */
#define CHUNKSIZE (1<<12) /* 힙을 확장할 때 한 번에 늘리는 크기(4096바이트, 4KB).  페이지 크기가 4kb라 */

// 두 값 중 큰 값 반환
#define MAX(x, y) ((x) > (y)? (x) : (y))

// 블록의 크기(size)와 할당 여부(alloc, 0 또는 1)를 하나의 4바이트 워드로 합침
#define PACK(size, alloc) ((size) | (alloc))

// 포인터 p가 가리키는 주소에서 4바이트 워드를 읽고 쓰기
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// 헤더/푸터 주소 p에서 블록 크기와 할당 상태를 추출
// bp는 페이로드(payload)가 시작되는 주소
#define GET_SIZE(p) (GET(p) & ~0x7) // 순수한 블록 크기
#define GET_ALLOC(p) (GET(p) & 0x1) // 할당 상태 반환 (0=가용, 1=할당)

// 블록 포인터 bp를 기준으로 헤더와 푸터의 주소를 계산
#define HDRP(bp) ((char *)(bp) - WSIZE) // bp에서 워드 크기만큼(4바이트) 빼서 헤더 주소를 계산
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // bp에 (블록 전체 크기 - 8바이트)를 더해 푸터 주소를 계산

// 인접한 블록의 주소 계산
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // bp에 현재 블록의 크기를 더해 다음 블록의 bp를 계산
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // bp에서 이전 블록의 크기를 빼서 이전 블록의 bp를 계산

static char *heap_listp;  /* 힙의 시작 부분을 가리키는 전역 포인터입니다. 정확히는 프롤로그 블록의 bp를 가리키게 됩니다. find_fit에서 힙 순회의 시작점으로 사용 */

// next-fit을 위한 전역 변수 
static char *heap_curp; // 마지막으로 할당한 위치를 기억

// best-fit을 위한 전역 변수
static char *best_p; // 가용블럭 - 할당할 블럭의 차가 작은 대로 업데이트

// 함수 선언 추가
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // 힙 영역을 16바이트만큼 확장하여 초기 구조(패딩, 프롤로그 헤더/푸터, 에필로그 헤더)를 만듬
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1){
        return -1;
    }
    PUT(heap_listp, 0);                           /* 첫 4바이트는 정렬 패딩(alignment padding), 프롤로그 블록의 주소가 8의 배수가 되도록 만듬 */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* 프롤로그 헤더 */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* 프롤로그 푸터 */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* 에필로그 헤더 */
    heap_listp += (2*WSIZE); // heap_listp가 프롤로그 블록의 페이로드 시작점(bp)을 가리키도록 설정
    
    // next-fit 마지막 위치 기억, 처음에는 heap_listp와 같지만 place에서 업데이트 되면 달라짐
    heap_curp = heap_listp;

    // 빈 힙을 CHUNKSIZE 바이트의 가용 블록으로 확장
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}


static void *extend_heap(size_t words) {
    char *bp;
    size_t size;
    
    // 요청된 words 수를 짝수로 맞추어 8바이트 정렬을 유지
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    //가용 블록 헤더/풋터 및 에필로그 헤더 초기화
    PUT(HDRP(bp), PACK(size, 0));           /* 가용 블록 헤더 */
    PUT(FTRP(bp), PACK(size, 0));           /* 가용 블록 푸터 */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));  /* 새 에필로그 헤더 */
    
    // 이전 블록이 가용 가능한 경우 합병
    return coalesce(bp);
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    // 초기 코드
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
	// return NULL;
    // else {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }
    size_t asize;      /* 조정된 블록 크기 */
    size_t extendsize; /* 적합한 블록이 없을 때 확장할 크기 */
    char *bp;
    
    if (size == 0)
        return NULL;
    
    /* 블록 크기를 오버헤드와 정렬 요구사항을 포함하도록 조정 */
    // 요청 크기가 8바이트 이하면 최소 블록 크기인 16바이트(2*DSIZE)로 asize를 설정
    // 헤더(4) + 풋터(4) + 페이로드(8)
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else // 8보다 크면 헤더/푸터(8B)와 정렬 요구사항을 고려하여 실제 할당할 블록 크기(asize)를 계산, (size + DSIZE)로 오버헤드를 더하고, (DSIZE-1)을 더한 후 8의 배수로 올림
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    
    /* 가용 리스트에서 적합한 블록 검색 */
    // asize를 담을 수 있는 충분히 큰 가용 블록을 힙에서 찾아 그 블록의 bp를 반환
    if ((bp = find_fit(asize)) != NULL) {
        // find_fit으로 찾은 가용 블록 bp에 요청된 asize만큼의 블록을 할당
        place(bp, asize);

        return bp;
    }
    
    /* 적합한 블록을 찾지 못함. 더 많은 메모리를 얻고 블록 배치 */
    // 만약 find_fit이 NULL을 반환했다면(적합한 가용 블록이 없다면), CHUNKSIZE와 asize 중 더 큰 값으로 힙을 확장하고, 확장된 공간에 블록을 할당
    extendsize = MAX(asize, CHUNKSIZE);

    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);

    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    // NULL 포인터 체크: 안전성을 위해 즉시 반환
    if (ptr == NULL) {
        return;
    }

    // 현재 블록의 크기 계산 (헤더에서 크기 정보 추출)
    size_t size = GET_SIZE(HDRP(ptr));

    // 블록을 가용 상태로 변경: 헤더와 푸터의 할당 비트를 0으로 설정
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    // 인접한 가용 블록들과 병합(coalescing) 수행
    // 이는 외부 단편화를 줄이고 큰 가용 블록을 만드는 데 도움
    coalesce(ptr);
}

// coalesce 함수 - 인접한 가용 블록들을 병합하여 외부 단편화를 줄임
static void *coalesce(void *bp) {
    // 인접 블록들의 할당 상태 확인
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));  // 이전 블록 할당 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));  // 다음 블록 할당 여부
    size_t size = GET_SIZE(HDRP(bp));                    // 현재 블록 크기

    // CASE 1: 이전과 다음 블록이 모두 할당된 경우 - 병합 불가능
    if (prev_alloc && next_alloc) {           /* CASE 1 이전과 다음 블록이 모두 할당됨*/
        return bp;
    }
    // CASE 2: 이전 블록은 할당, 다음 블록은 가용 - 다음 블록과 병합
    else if (prev_alloc && !next_alloc) {     /* CASE 2 이전 블록은 할당, 다음 블록은 가용*/
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));  // 다음 블록 크기를 현재 블록에 추가
        PUT(HDRP(bp), PACK(size, 0));           // 확장된 크기로 헤더 업데이트
        PUT(FTRP(bp), PACK(size, 0));           // 확장된 크기로 푸터 업데이트
    }
    // CASE 3: 이전 블록은 가용, 다음 블록은 할당 - 이전 블록과 병합
    else if (!prev_alloc && next_alloc) {     /* CASE 3 이전 블록은 가용, 다음 블록은 할당*/
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));  // 이전 블록 크기를 현재 블록에 추가
        PUT(FTRP(bp), PACK(size, 0));           // 현재 블록의 푸터를 확장된 크기로 업데이트
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록의 헤더를 확장된 크기로 업데이트
        bp = PREV_BLKP(bp);                      // 병합된 블록의 시작점을 이전 블록으로 이동
    }
    // CASE 4: 이전과 다음 블록이 모두 가용 - 세 블록 모두 병합
    else {                                     /* CASE 4 이전과 다음 블록이 모두 가용 상태*/
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +   // 이전 블록 크기 추가
                GET_SIZE(FTRP(NEXT_BLKP(bp)));     // 다음 블록 크기 추가
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));  // 이전 블록의 헤더를 전체 크기로 업데이트
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));  // 다음 블록의 푸터를 전체 크기로 업데이트
        bp = PREV_BLKP(bp);                        // 병합된 블록의 시작점을 이전 블록으로 이동
    }

    // next-fit을 위해 heap_curp가 유효한 범위에 있는지 확인하고 필요시 업데이트
    // heap_curp < (char *)bp + size 내부 외부에 있는지 확인
    // if (heap_curp > (char *)bp && heap_curp < (char *)bp + size) {
    //     heap_curp = bp; // 병합된 블록의 시작점으로 이동
    // }
    heap_curp = bp;

    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size); // 1. 요청된 크기로 새 메모리 블록 할당
    
    if (newptr == NULL)
      return NULL;

    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE); // 2. 기존 블록의 크기를 헤더에서 읽어옴
    if (size < copySize)
      copySize = size;  // 3. 새 크기가 작으면 새 크기만큼만 복사하도록 조정

    memcpy(newptr, oldptr, copySize); // 4. 기존 데이터를 새 블록으로 복사
    mm_free(oldptr); // 5. 기존 블록 해제

    return newptr;
}


static void *find_fit(size_t asize)
{
    // first-fit 검색: 힙을 순회하며 첫 번째로 발견되는 적합한 가용 블록을 반환
    void *bp;

    // 힙의 시작부터 에필로그 블록(크기 0)까지 모든 블록을 순회
    // for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    //     // 가용 블록이면서 요청 크기(asize)를 수용할 수 있는 블록을 찾으면
    //     if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
    //         return bp; // 해당 블록의 포인터 반환
    //     }
    // }

    // // next-fit 검색: 마지막으로 할당한 위치부터 힙을 순히하며 첫 번째로 발견되는 가용 블록을 반환
    // // 첫 번째 검색: 마지막 heap_curp 위치부터 에필로그까지
    // for (bp = heap_curp; GET_SIZE(HDRP(bp))>0; bp = NEXT_BLKP(bp)) {
    //     if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
    //         heap_curp = bp; // 찾은 위치를 기억
    //         return bp;
    //     }
    // }
    
    // // 두 번째 검색: 처음부터 heap_curp까지
    // for (bp = heap_listp; bp < heap_curp; bp = NEXT_BLKP(bp)) {
    //     if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
    //         heap_curp = bp; // 찾은 위치를 기억
    //         return bp;
    //     }
    // }


    // // best-fit 검색: 처음부터 에필로그까지 순회하여 할당할 블럭과 가용 블록의 차가 제일 적은 곳에 블럭을 할당
    int min_diff = INT_MAX;
    int cur_diff = 0;
    best_p = NULL; 

    for (bp = heap_listp;GET_SIZE(HDRP(bp))>0;bp = NEXT_BLKP(bp)) {
        // 가용 블록이면서 요청 크기(asize)를 수용할 수 있는 블록을 찾으면
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            cur_diff = GET_SIZE(HDRP(bp)) - asize;
            if (cur_diff < min_diff ) {
               min_diff = cur_diff;
               best_p = bp;

                if (cur_diff == 0) {
                    break;
                }
            }
            // 적합한 핏한거 찾았을 때
            
        }
    }
    
    
    return best_p;
    // return NULL; // 적합한 블록을 찾지 못한 경우
}


// place 함수 - 가용 블록에 요청된 크기만큼 할당하고, 남은 공간이 충분하면 분할
static void place(void *bp, size_t asize) {
    
    // 현재 가용 블록의 전체 크기 계산
    size_t csize = GET_SIZE(HDRP(bp));

    // 남은 공간이 최소 블록 크기(16바이트) 이상이면 분할 수행
    if ((csize - asize) >= (2*DSIZE)) {
        // 요청된 크기만큼 할당된 블록 생성
        PUT(HDRP(bp), PACK(asize, 1));           // 할당된 블록 헤더
        PUT(FTRP(bp), PACK(asize, 1));           // 할당된 블록 푸터
        
        // 남은 공간을 새로운 가용 블록으로 분할
        bp = NEXT_BLKP(bp);                      // 분할된 가용 블록의 시작점
        PUT(HDRP(bp), PACK(csize - asize, 0));  // 가용 블록 헤더
        PUT(FTRP(bp), PACK(csize - asize, 0));  // 가용 블록 푸터
    }
    // 남은 공간이 부족하면 전체 블록을 할당 (분할하지 않음)
    else {
        PUT(HDRP(bp), PACK(csize, 1));           // 전체 블록을 할당된 상태로 설정
        PUT(FTRP(bp), PACK(csize, 1));
    }
}












