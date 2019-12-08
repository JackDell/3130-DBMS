/*-------------------------------------------------------------------------
 *
 * nodeHashjoin.c
 *	  Routines to handle hash join nodes
 *
 * Portions Copyright (c) 1996-2005, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  $PostgreSQL: pgsql/src/backend/executor/nodeHashjoin.c,v 1.75.2.4 2007/02/02 00:07:44 tgl Exp $
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "executor/executor.h"
#include "executor/hashjoin.h"
#include "executor/nodeHash.h"
#include "executor/nodeHashjoin.h"
#include "optimizer/clauses.h"
#include "utils/memutils.h"


static TupleTableSlot *ExecHashJoinOuterGetTuple(PlanState *outerNode,
						  HashJoinState *hjstate,
						  uint32 *hashvalue);
static TupleTableSlot *ExecHashJoinInnerGetTuple(PlanState *innerNode,
						  HashJoinState *hjstate,
						  uint32 *hashvalue);
static TupleTableSlot *ExecHashJoinGetSavedTuple(HashJoinState *hjstate,
						  BufFile *file,
						  uint32 *hashvalue,
						  TupleTableSlot *tupleSlot);
static int	ExecHashJoinNewBatch(HashJoinState *hjstate);


/* ----------------------------------------------------------------
 *		ExecHashJoin
 *
 *		This function implements the Hybrid Hashjoin algorithm.
 *
 *		Note: the relation we build hash table on is the "inner"
 *			  the other one is "outer".
 * ----------------------------------------------------------------
 */
TupleTableSlot *				/* return: a tuple or NULL */
ExecHashJoin(HashJoinState *node)
{
	EState	   *estate;
	//CSI3130 inner node
	HashState  *outerHashNode;
	HashState *innerHashNode;
	List	   *joinqual;
	List	   *otherqual;
	TupleTableSlot *inntuple;
	TupleTableSlot *outTuple; //CSI3130
	ExprContext *econtext;
	ExprDoneCond isDone;
	//CSI3130 ---------------------------------------------
	HashJoinTable innerHashTable;
	HashJoinTable outerHashTable;
	HeapTuple	curtuple;
	TupleTableSlot *outerTupleSlot;
	//CSI3130 innerTupleSlot:
	TupleTableSlot *innerTupleSlot;

	uint32		hashvalue;
	int			batchno;

	/*
	 * get information from HashJoin node
	 */
	estate = node->js.ps.state;
	joinqual = node->js.joinqual;
	otherqual = node->js.ps.qual;
	innerHashNode = (HashState *) innerPlanState(node);
	//CSI3130 -----------------------------------------------------
	
	outerHashNode = (HashState *) outerPlanState(node);

	/*
	 * get information from HashJoin state
	 */

	//CSI3130 ----------------------------------------------------

	innerHashTable = node->inner_hj_HashTable;
	outerHashTable = node->outer_hj_HashTable;

	econtext = node->js.ps.ps_ExprContext;

	/*
	 * Check to see if we're still projecting out tuples from a previous join
	 * tuple (because there is a function-returning-set in the projection
	 * expressions).  If so, try to project another one.
	 */
//	if (node->js.ps.ps_TupFromTlist)
//	{
//		TupleTableSlot *result;
//
//		result = ExecProject(node->js.ps.ps_ProjInfo, &isDone);
//		if (isDone == ExprMultipleResult)
//			return result;
		/* Done with that source tuple... */
//		node->js.ps.ps_TupFromTlist = false;
//	}

	/*
	 * If we're doing an IN join, we want to return at most one row per outer
	 * tuple; so we can stop scanning the inner scan if we matched on the
	 * previous try.
	 */
	if (node->js.jointype == JOIN_IN && node->hj_MatchedOuter)
		node->hj_NeedNewOuter = true;

	/*
	 * Reset per-tuple memory context to free any expression evaluation
	 * storage allocated in the previous tuple cycle.  Note this can't happen
	 * until we're done projecting out tuples from a join tuple.
	 */
	ResetExprContext(econtext);

	/*
	 * if this is the first call, build the hash table for inner and outer relation
	 */
	if (innerHashTable == NULL && outerHashTable == NULL) //CSI3130
	{
		/*
		 * If the outer relation is completely empty, we can quit without
		 * building the hash table.  However, for an inner join it is only a
		 * win to check this when the outer relation's startup cost is less
		 * than the projected cost of building the hash table.	Otherwise it's
		 * best to build the hash table first and see if the inner relation is
		 * empty.  (When it's an outer join, we should always make this check,
		 * since we aren't going to be able to skip the join on the strength
		 * of an empty inner relation anyway.)
		 *
		 * If we are rescanning the join, we make use of information gained
		 * on the previous scan: don't bother to try the prefetch if the
		 * previous scan found the outer relation nonempty.  This is not
		 * 100% reliable since with new parameters the outer relation might
		 * yield different results, but it's a good heuristic.
		 *
		 * The only way to make the check is to try to fetch a tuple from the
		 * outer plan node.  If we succeed, we have to stash it away for later
		 * consumption by ExecHashJoinOuterGetTuple.
		 */
//		if (node->js.jointype == JOIN_LEFT ||
//			(outerNode->plan->startup_cost < hashNode->ps.plan->total_cost &&
//			 !node->hj_OuterNotEmpty))
//		{
//			node->hj_FirstOuterTupleSlot = ExecProcNode(outerNode);
//			if (TupIsNull(node->hj_FirstOuterTupleSlot))
//			{
//				node->hj_OuterNotEmpty = false;
//				return NULL;
//			}
//			else
//				node->hj_OuterNotEmpty = true;
//		}
//		else
//			node->hj_FirstOuterTupleSlot = NULL;

		/*
		 * create the hash table
		 */
		innerHashTable = ExecHashTableCreate((Hash *) innerHashNode->ps.plan, node->hj_HashOperators); //csi3130
		//CSI3130 ------------------------------------------
		outerHashTable = ExecHashTableCreate((Hash *) outerHashNode->ps.plan, node->hj_HashOperators);
		node->outer_hj_HashTable = outerHashTable;

		/*
		 * execute the Hash node, to build the hash table
		 */

		//csi3130
		innerHashNode->hashtable = innerHashTable;
		outerHashNode->hashtable = outerHashTable;

		//(void) MultiExecProcNode((PlanState *) hashNode);

		/*
		 * If the inner relation is completely empty, and we're not doing an
		 * outer join, we can quit without scanning the outer relation.
		 */
//		if (hashtable->totalTuples == 0 && node->js.jointype != JOIN_LEFT)
//			return NULL;

		/*
		 * need to remember whether nbatch has increased since we began
		 * scanning the outer relation
		 */
		//hashtable->nbatch_outstart = hashtable->nbatch;

		/*
		 * Reset OuterNotEmpty for scan.  (It's OK if we fetched a tuple
		 * above, because ExecHashJoinOuterGetTuple will immediately
		 * set it again.)
		 */
		//node->hj_OuterNotEmpty = false;
	}

	/*
	 * run the hash join process
	 */

	/*
	CSI3130 Implementation of the new symmetric Hash Join Algotrithm
	----------------------------------------------------------------
	*/
	
	for (;;)
	{
		if(!node->innerFinished || !node->outerFinished){
			if(node->outerFinished){
				node->inner = true;
			}

			if(node->innerFinished){
				node->inner = false;
			}

			
			//CSI3130
			//If it is hashing an inner node

			if(node->hj_NeedNewInner && node->inner && !node->innerFinished){
				
				innerTupleSlot = ExecProcNode((PlanState *) innerHashNode);

				if(TupIsNull(innerTupleSlot)){
					node->innerFinished = true;
					
				}else{
					node->js.ps.ps_InnerTupleSlot = innerTupleSlot;
					ExprContext *econtext = node->js.ps.ps_ExprContext;
					econtext->ecxt_innertuple = innerTupleSlot;
					node->hj_NeedNewInner = false;

					hashvalue = ExecHashGetHashValue(outerHashTable, econtext, node->hj_InnerHashKeys);
					node->inner_hj_CurHashValue = hashvalue;
					ExecHashGetBucketAndBatch(outerHashTable, hashvalue, &node->inner_hj_CurBucketNo, &batchno);

					node->outer_hj_CurTuple = NULL;
				}
				
			}

			
			//CSI3130
			//If it is hashing an outer node

			if(node->hj_NeedNewOuter && !node->inner && !node->outerFinished){
				
				outerTupleSlot = ExecProcNode((PlanState *) outerHashNode);

				if(TupIsNull(outerTupleSlot)){		
					node->outerFinished = true;
				}else{
					node->js.ps.ps_OuterTupleSlot = outerTupleSlot;
					econtext->ecxt_outertuple = outerTupleSlot;
					node->hj_NeedNewOuter = false;

					hashvalue = ExecHashGetHashValue(innerHashTable, econtext, node->hj_OuterHashKeys);
					node->outer_hj_CurHashValue = hashvalue;
					ExecHashGetBucketAndBatch(innerHashTable, hashvalue, &node->outer_hj_CurBucketNo, &batchno);

					node->outer_hj_CurTuple = NULL;
				}
			}
			
			//CSI3130
			//If inner and outer are finished join is over
			if(node->innerFinished && node->outerFinished){
				printf("both inner (%f tuples) and outer (%f tuples) exhausted\n",innerHashTable->totalTuples,outerHashTable->totalTuples);
				printf("Got %d matches by probing inner hash table\n",node->matches_by_probing_inner);
				printf("Got %d matches by probing outer hash table\n",node->matches_by_probing_outer);
				printf("Assuming outer is always probed first\n");
				return NULL;
			}

			//CSI3130
			//If it hashed an innernode it scans the outerhashtable
			if(node->inner){
				for(;;){
					ExprContext *econtext = node->js.ps.ps_ExprContext;
					econtext->ecxt_innertuple = node->js.ps.ps_InnerTupleSlot;

					curtuple = ExecScanHashBucket(node, econtext);
					if(curtuple == NULL){
						node->inner = false;
						break;
					}

					outTuple = ExecStoreTuple(curtuple, node->outer_hj_HashTupleSlot, InvalidBuffer, false);
					//ExprContext *econtext -node->js.ps.ps_ExprContext;
					econtext->ecxt_outertuple = outTuple; //maybe needs change

					ResetExprContext(econtext);

					if (joinqual == NIL || ExecQual(joinqual, econtext, false)) {
                        if (otherqual == NIL || ExecQual(otherqual, econtext, false)) {
                            TupleTableSlot *result;
                            result = ExecProject(node->js.ps.ps_ProjInfo, &isDone);
                            if (isDone != ExprEndResult) {
                                node->matches_by_probing_outer = node->matches_by_probing_outer+ 1;
								node->js.ps.ps_TupFromTlist = (isDone == ExprMultipleResult);
                                return result;
                            }
                        }
                    }
				}

				node->hj_NeedNewInner = true;
				node->inner = false;
				node->js.ps.ps_InnerTupleSlot = NULL;

			}//CSI3130 Or else it is an outer node and scans the innerhashtable
			else{

				for(;;){
					
					ExprContext *econtext = node->js.ps.ps_ExprContext;
					econtext->ecxt_outertuple = node->js.ps.ps_OuterTupleSlot;

					curtuple = ExecScanHashBucket(node, econtext);
					if(curtuple == NULL){
						node->inner = true;
						break;
					}

					inntuple = ExecStoreTuple(curtuple, node->inner_hj_HashTupleSlot, InvalidBuffer, false);
					econtext->ecxt_innertuple = inntuple;

					ResetExprContext(econtext);

					if (joinqual == NIL || ExecQual(joinqual, econtext, false)) {
                        if (otherqual == NIL || ExecQual(otherqual, econtext, false)) {
                            TupleTableSlot *result;
                            result = ExecProject(node->js.ps.ps_ProjInfo, &isDone);
                            if (isDone != ExprEndResult) {
                                node->matches_by_probing_inner = node->matches_by_probing_inner + 1;
								node->js.ps.ps_TupFromTlist = (isDone == ExprMultipleResult);
                                return result;
                            }
                        }
                    }
				}

				node->hj_NeedNewOuter = true;
				node->inner = true;
				node->js.ps.ps_OuterTupleSlot = NULL;
				//continue;
			}
		}
	}
}
		
	

/* ----------------------------------------------------------------
 *		ExecInitHashJoin
 *
 *		Init routine for HashJoin node.
 * ----------------------------------------------------------------
 */
HashJoinState *
ExecInitHashJoin(HashJoin *node, EState *estate)
{
	printf("This is a test");
	HashJoinState *hjstate;
	//CSI3130
	Hash *innerHashNode;
	Hash *outerHashNode;
	List	   *lclauses;
	List	   *rclauses;
	List	   *hoperators;
	ListCell   *l;

	/*
	 * create state structure
	 */
	hjstate = makeNode(HashJoinState);
	hjstate->js.ps.plan = (Plan *) node;
	hjstate->js.ps.state = estate;

	/*
	 * Miscellaneous initialization
	 *
	 * create expression context for node
	 */
	ExecAssignExprContext(estate, &hjstate->js.ps);

	/*
	 * initialize child expressions
	 */
	hjstate->js.ps.targetlist = (List *)
		ExecInitExpr((Expr *) node->join.plan.targetlist,
					 (PlanState *) hjstate);
	hjstate->js.ps.qual = (List *)
		ExecInitExpr((Expr *) node->join.plan.qual,
					 (PlanState *) hjstate);
	hjstate->js.jointype = node->join.jointype;
	hjstate->js.joinqual = (List *)
		ExecInitExpr((Expr *) node->join.joinqual,
					 (PlanState *) hjstate);
	hjstate->hashclauses = (List *)
		ExecInitExpr((Expr *) node->hashclauses,
					 (PlanState *) hjstate);

	/*
	 * initialize child nodes
	 */

	//CSI3130 ---------------------------------------------------

	innerHashNode = (Hash *) innerPlanState(node);
	outerHashNode = (Hash *) outerPlanState(node);

	
	//CSI3130 ------------------------------------------------------------

	outerPlanState(hjstate) = ExecInitNode((Plan *) outerHashNode, estate);
	innerPlanState(hjstate) = ExecInitNode((Plan *) innerHashNode, estate);

#define HASHJOIN_NSLOTS 3

	/*
	 * tuple table initialization
	 */
	ExecInitResultTupleSlot(estate, &hjstate->js.ps);
	hjstate->hj_OuterTupleSlot = ExecInitExtraTupleSlot(estate);
	//CSI3130
	hjstate->hj_InnerTupleSlot = ExecInitExtraTupleSlot(estate);

	switch (node->join.jointype)
	{
		case JOIN_INNER:
		case JOIN_IN:
			break;
		case JOIN_LEFT:
			hjstate->hj_NullInnerTupleSlot =
				ExecInitNullTupleSlot(estate,
								 ExecGetResultType(innerPlanState(hjstate)));
			break;
		default:
			elog(ERROR, "unrecognized join type: %d",
				 (int) node->join.jointype);
	}

	/*
	 * now for some voodoo.  our temporary tuple slot is actually the result
	 * tuple slot of the Hash node (which is our inner plan).  we do this
	 * because Hash nodes don't return tuples via ExecProcNode() -- instead
	 * the hash join node uses ExecScanHashBucket() to get at the contents of
	 * the hash table.	-cim 6/9/91
	 */
	{
		HashState  *hashstate = (HashState *) innerPlanState(hjstate);
		TupleTableSlot *slot = hashstate->ps.ps_ResultTupleSlot;
		hjstate->inner_hj_HashTupleSlot = slot;

		//CSI3130 ---------------------------------------------
		hashstate = (HashState *) outerPlanState(hjstate);
		slot = hashstate->ps.ps_ResultTupleSlot;
		hjstate->outer_hj_HashTupleSlot = slot;
	}

	/*
	 * initialize tuple type and projection info
	 */
	ExecAssignResultTypeFromTL(&hjstate->js.ps);
	ExecAssignProjectionInfo(&hjstate->js.ps, NULL);

	ExecSetSlotDescriptor(hjstate->hj_OuterTupleSlot, ExecGetResultType(outerPlanState(hjstate)),false);

	//CSI3130
	ExecSetSlotDescriptor(hjstate->hj_InnerTupleSlot, ExecGetResultType(innerPlanState(hjstate)), false);

	/*
	 * initialize hash-specific info
	 */

	//CSI3130 ------------------------------------------------
	hjstate->inner_hj_HashTable = NULL;
	hjstate->outer_hj_HashTable = NULL;
	hjstate->hj_FirstOuterTupleSlot = NULL;
	hjstate->hj_FirstInnerTupleSlot = NULL;

	hjstate->inner_hj_CurHashValue = 0;
	hjstate->inner_hj_CurBucketNo = 0;
	hjstate->inner_hj_CurTuple = NULL;

	hjstate->outer_hj_CurHashValue = 0;
	hjstate->outer_hj_CurBucketNo = 0;
	hjstate->outer_hj_CurTuple = NULL;

	/*
	 * Deconstruct the hash clauses into outer and inner argument values, so
	 * that we can evaluate those subexpressions separately.  Also make a list
	 * of the hash operator OIDs, in preparation for looking up the hash
	 * functions to use.
	 */
	lclauses = NIL;
	rclauses = NIL;
	hoperators = NIL;
	foreach(l, hjstate->hashclauses)
	{
		FuncExprState *fstate = (FuncExprState *) lfirst(l);
		OpExpr	   *hclause;

		Assert(IsA(fstate, FuncExprState));
		hclause = (OpExpr *) fstate->xprstate.expr;
		Assert(IsA(hclause, OpExpr));
		lclauses = lappend(lclauses, linitial(fstate->args));
		rclauses = lappend(rclauses, lsecond(fstate->args));
		hoperators = lappend_oid(hoperators, hclause->opno);
	}
	hjstate->hj_OuterHashKeys = lclauses;
	hjstate->hj_InnerHashKeys = rclauses;
	hjstate->hj_HashOperators = hoperators;
	/* child Hash node needs to evaluate inner hash keys, too */
	((HashState *) innerPlanState(hjstate))->hashkeys = lclauses;
	//CSI3130
	((HashState *) outerPlanState(hjstate))->hashkeys = rclauses;

	//CSI3130
	hjstate->js.ps.ps_OuterTupleSlot = NULL;
	hjstate->js.ps.ps_InnerTupleSlot = NULL;
	hjstate->js.ps.ps_TupFromTlist = false;
	hjstate->hj_NeedNewOuter = true;
	hjstate->hj_NeedNewInner = true;
	hjstate->outerFinished = false;
	hjstate->innerFinished = false;

	hjstate->hj_MatchedOuter = false;
	hjstate->hj_OuterNotEmpty = false;
	hjstate->matches_by_probing_inner = 0;
	hjstate->matches_by_probing_outer = 0;
	
	hjstate->inner = true;

	return hjstate;
}

int
ExecCountSlotsHashJoin(HashJoin *node)
{
	return ExecCountSlotsNode(outerPlan(node)) +
		ExecCountSlotsNode(innerPlan(node)) +
		HASHJOIN_NSLOTS;
}

/* ----------------------------------------------------------------
 *		ExecEndHashJoin
 *
 *		clean up routine for HashJoin node
 * ----------------------------------------------------------------
 */
void
ExecEndHashJoin(HashJoinState *node)
{
	/*
	 * Free hash table
	 */

	//CSI3130
	if (node->outer_hj_HashTable)
	{
		ExecHashTableDestroy(node->outer_hj_HashTable);
		node->outer_hj_HashTable = NULL;
	}
	if(node->inner_hj_HashTable){
		ExecHashTableDestroy(node->inner_hj_HashTable);
		node->inner_hj_HashTable = NULL;
	}

	/*
	 * Free the exprcontext
	 */
	ExecFreeExprContext(&node->js.ps);

	/*
	 * clean out the tuple table
	 */
	ExecClearTuple(node->js.ps.ps_OuterTupleSlot);
	ExecClearTuple(node->js.ps.ps_InnerTupleSlot);
	ExecClearTuple(node->hj_OuterTupleSlot);
	ExecClearTuple(node->hj_InnerTupleSlot);
	ExecClearTuple(node->outer_hj_HashTupleSlot);
	ExecClearTuple(node->inner_hj_HashTupleSlot);

	/*
	 * clean up subtrees
	 */
	ExecEndNode(outerPlanState(node));
	ExecEndNode(innerPlanState(node));
}

/*
 * ExecHashJoinOuterGetTuple
 *
 *		get the next outer tuple for hashjoin: either by
 *		executing a plan node in the first pass, or from
 *		the temp files for the hashjoin batches.
 *
 * Returns a null slot if no more outer tuples.  On success, the tuple's
 * hash value is stored at *hashvalue --- this is either originally computed,
 * or re-read from the temp file.
 */
static TupleTableSlot *
ExecHashJoinOuterGetTuple(PlanState *outerNode,
						  HashJoinState *hjstate,
						  uint32 *hashvalue)
{
	HashJoinTable hashtable = hjstate->inner_hj_HashTable;
	int			curbatch = hashtable->curbatch;
	TupleTableSlot *slot;

	if (curbatch == 0)
	{							/* if it is the first pass */

		/*
		 * Check to see if first outer tuple was already fetched by
		 * ExecHashJoin() and not used yet.
		 */
		slot = hjstate->hj_FirstOuterTupleSlot;
		if (!TupIsNull(slot))
			hjstate->hj_FirstOuterTupleSlot = NULL;
		else
			slot = ExecProcNode(outerNode);
		if (!TupIsNull(slot))
		{
			/*
			 * We have to compute the tuple's hash value.
			 */
			ExprContext *econtext = hjstate->js.ps.ps_ExprContext;

			econtext->ecxt_outertuple = slot;
			*hashvalue = ExecHashGetHashValue(hashtable, econtext,
											  hjstate->hj_OuterHashKeys);

			/* remember outer relation is not empty for possible rescan */
			//hjstate->hj_OuterNotEmpty = true;

			return slot;
		}

		/*
		 * We have just reached the end of the first pass. Try to switch to a
		 * saved batch.
		 */
		curbatch = ExecHashJoinNewBatch(hjstate);
	}

	/*
	 * Try to read from a temp file. Loop allows us to advance to new batches
	 * as needed.  NOTE: nbatch could increase inside ExecHashJoinNewBatch, so
	 * don't try to optimize this loop.
	 */
	while (curbatch < hashtable->nbatch)
	{
		slot = ExecHashJoinGetSavedTuple(hjstate,
										 hashtable->outerBatchFile[curbatch],
										 hashvalue,
										 hjstate->hj_OuterTupleSlot);
		if (!TupIsNull(slot))
			return slot;
		curbatch = ExecHashJoinNewBatch(hjstate);
	}
	

	/* Out of batches... */
	return NULL;
}


/*
 * ExecHashJoinNewBatch
 *		switch to a new hashjoin batch
 *
 * Returns the number of the new batch (1..nbatch-1), or nbatch if no more.
 * We will never return a batch number that has an empty outer batch file.
 */
static int
ExecHashJoinNewBatch(HashJoinState *hjstate)
{
	return 0;
}

/*
 * ExecHashJoinSaveTuple
 *		save a tuple to a batch file.
 *
 * The data recorded in the file for each tuple is its hash value,
 * then an image of its HeapTupleData (with meaningless t_data pointer)
 * followed by the HeapTupleHeader and tuple data.
 *
 * Note: it is important always to call this in the regular executor
 * context, not in a shorter-lived context; else the temp file buffers
 * will get messed up.
 */
void
ExecHashJoinSaveTuple(HeapTuple heapTuple, uint32 hashvalue,
					  BufFile **fileptr)
{
	BufFile    *file = *fileptr;
	size_t		written;

	if (file == NULL)
	{
		/* First write to this batch file, so open it. */
		file = BufFileCreateTemp(false);
		*fileptr = file;
	}

	written = BufFileWrite(file, (void *) &hashvalue, sizeof(uint32));
	if (written != sizeof(uint32))
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not write to hash-join temporary file: %m")));

	written = BufFileWrite(file, (void *) heapTuple, sizeof(HeapTupleData));
	if (written != sizeof(HeapTupleData))
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not write to hash-join temporary file: %m")));

	written = BufFileWrite(file, (void *) heapTuple->t_data, heapTuple->t_len);
	if (written != (size_t) heapTuple->t_len)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not write to hash-join temporary file: %m")));
}

/*
 * ExecHashJoinGetSavedTuple
 *		read the next tuple from a batch file.	Return NULL if no more.
 *
 * On success, *hashvalue is set to the tuple's hash value, and the tuple
 * itself is stored in the given slot.
 */
static TupleTableSlot *
ExecHashJoinGetSavedTuple(HashJoinState *hjstate,
						  BufFile *file,
						  uint32 *hashvalue,
						  TupleTableSlot *tupleSlot)
{
	HeapTupleData htup;
	size_t		nread;
	HeapTuple	heapTuple;

	nread = BufFileRead(file, (void *) hashvalue, sizeof(uint32));
	if (nread == 0)
		return NULL;			/* end of file */
	if (nread != sizeof(uint32))
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not read from hash-join temporary file: %m")));
	nread = BufFileRead(file, (void *) &htup, sizeof(HeapTupleData));
	if (nread != sizeof(HeapTupleData))
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not read from hash-join temporary file: %m")));
	heapTuple = palloc(HEAPTUPLESIZE + htup.t_len);
	memcpy((char *) heapTuple, (char *) &htup, sizeof(HeapTupleData));
	heapTuple->t_datamcxt = CurrentMemoryContext;
	heapTuple->t_data = (HeapTupleHeader)
		((char *) heapTuple + HEAPTUPLESIZE);
	nread = BufFileRead(file, (void *) heapTuple->t_data, htup.t_len);
	if (nread != (size_t) htup.t_len)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not read from hash-join temporary file: %m")));
	return ExecStoreTuple(heapTuple, tupleSlot, InvalidBuffer, true);
}


void
ExecReScanHashJoin(HashJoinState *node, ExprContext *exprCtxt)
{
	/*
	 * In a multi-batch join, we currently have to do rescans the hard way,
	 * primarily because batch temp files may have already been released. But
	 * if it's a single-batch join, and there is no parameter change for the
	 * inner subnode, then we can just re-use the existing hash table without
	 * rebuilding it.
	 */
//	if (node->hj_HashTable != NULL)
//	{
//		if (node->hj_HashTable->nbatch == 1 &&
//			((PlanState *) node)->righttree->chgParam == NULL)
//		{
			/*
			 * okay to reuse the hash table; needn't rescan inner, either.
			 *
			 * What we do need to do is reset our state about the emptiness
			 * of the outer relation, so that the new scan of the outer will
			 * update it correctly if it turns out to be empty this time.
			 * (There's no harm in clearing it now because ExecHashJoin won't
			 * need the info.  In the other cases, where the hash table
			 * doesn't exist or we are destroying it, we leave this state
			 * alone because ExecHashJoin will need it the first time
			 * through.)
			 */
			//node->hj_OuterNotEmpty = false;
//		}
//		else
//		{
			/* must destroy and rebuild hash table */
//			ExecHashTableDestroy(node->hj_HashTable);
//			node->hj_HashTable = NULL;

			/*
			 * if chgParam of subnode is not null then plan will be re-scanned
			 * by first ExecProcNode.
			 */
//			if (((PlanState *) node)->righttree->chgParam == NULL)
//				ExecReScan(((PlanState *) node)->righttree, exprCtxt);
//		}
//	}

	/* Always reset intra-tuple state */
	//node->hj_CurHashValue = 0;
	//node->outer_hj_CurBucketNo = 0;
	//node->hj_CurTuple = NULL;

	node->js.ps.ps_OuterTupleSlot = NULL;
	node->js.ps.ps_TupFromTlist = false;
	node->hj_NeedNewOuter = true;
	node->hj_MatchedOuter = false;
	node->hj_FirstOuterTupleSlot = NULL;

	/*
	 * if chgParam of subnode is not null then plan will be re-scanned by
	 * first ExecProcNode.
	 */
	if (((PlanState *) node)->lefttree->chgParam == NULL)
		ExecReScan(((PlanState *) node)->lefttree, exprCtxt);
}

