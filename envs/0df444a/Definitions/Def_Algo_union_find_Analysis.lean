-- Prove2me | Definitions.Def_Algo_union_find_Analysis
-- name    : Algo_union_find_Analysis
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:51:21.498022+00:00
-- url     : https://prove2.me/theorems/84783246-5c85-430f-ad74-f349be0770fe
-- title:
--   Mutable union-find representation, frames and cost functions
-- statement:
--   `UnionFindAnalysis.Layout` names an allocated object and its distinct parent/rank sequences. `Rep heap layout model` relates the object's fields and all in-range array values to the finite pure forest, including `Valid model`. `Storage` describes exact preservation of allocation counters, objects, collections and all arrays outside the specified writable references.
--
--   `findCosts` and `unionCosts` describe every clock increment from the traversed path lengths. `work` sums `uf_init`, `uf_find`, `uf_compress`, and `uf_union`. `findResult` and `unionResult` describe the model after the same mutations as the actual calls. The representation and potential must use the same returned model when composing operations.
--
--   This bundle supplies definitions used by the independently published mutable find/union contracts. It contains no graph-specific assumptions. In-range arguments use `Fin n`; callers prove the representation once and carry it between calls.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/kruskal/analysis/union_find.lean

import Definitions.Def_Algo_union_find_Points
import Definitions.Def_Algo_union_find_Facts
import Definitions.Def_Algo2LeanLib_UnionFindAmortized
import Definitions.Def_Algo2LeanLib_CallCost
import Definitions.Def_Algo2LeanLib_Footprint

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Reusable contracts for the compiled union-find implementation.

`find_contract` and `union_contract` give the exact model, storage, and clock
effects of full path compression and union by rank. `find_amortized` and
`union_amortized` bound incremental work using a shared inverse-Ackermann
potential. The simpler `find_summary` and `union_summary` retain logarithmic
worst-case bounds, partition guarantees, and protection for caller storage.

The forest and rank invariants are independent of generated code and graphs.
Constructor correctness is in the companion `union_find_init` analysis. Costs
count the explicit source clocks and compose from arbitrary initial counters.
-/

namespace UnionFindAnalysis

open Algo2LeanCore Algo2LeanGenerated
open Algo.union_find Algo.union_find.Algo2LeanGenerated

/-- A parent path ending at a root, with its number of non-root edges. -/
inductive ParentPath (parent : Seq) : Int → Int → Nat → Prop where
  | root (vertex : Int) (fixed : parent vertex = vertex) :
      ParentPath parent vertex vertex 0
  | next (vertex root : Int) (length : Nat) (different : parent vertex ≠ vertex)
      (tail : ParentPath parent (parent vertex) root length) :
      ParentPath parent vertex root (length + 1)

/-- Exact storage and clock effects of recursive path compression. The number
    of parent links is supplied by the independently established path witness. -/
def findHeap (heap : Heap) (parent : SeqRef) (vertex root : Int) : Nat → Heap
  | 0 => heap.tick "uf_find"
  | length + 1 =>
      ((findHeap (heap.tick "uf_find") parent (heap.read parent vertex) root length).write
        parent vertex root).tick "uf_compress"

@[simp] theorem findHeap_nextRef (heap : Heap) (parent : SeqRef) (vertex root : Int)
    (length : Nat) : (findHeap heap parent vertex root length).nextRef = heap.nextRef := by
  induction length generalizing heap vertex with
  | zero => rfl
  | succ length ih => simp [findHeap, Heap.write, ih]

@[simp] theorem findHeap_objects (heap : Heap) (parent : SeqRef) (vertex root : Int)
    (length : Nat) : (findHeap heap parent vertex root length).objects = heap.objects := by
  induction length generalizing heap vertex with
  | zero => rfl
  | succ length ih => simp [findHeap, Heap.write, ih]

@[simp] theorem findHeap_nextObject (heap : Heap) (parent : SeqRef) (vertex root : Int)
    (length : Nat) : (findHeap heap parent vertex root length).nextObject = heap.nextObject := by
  induction length generalizing heap vertex with
  | zero => rfl
  | succ length ih => simp [findHeap, Heap.write, ih]








open Algo2Lean.UnionFind (State Find compress    )

/-- Storage references are separate from the mathematical partition. -/
structure Layout where
  object : Ref_UnionFind
  parent : SeqRef
  rank : SeqRef

/-- A heap stores a valid finite disjoint-set forest with these two arrays. -/
structure Rep (heap : Heap) (layout : Layout) {n : Nat} (model : State n) : Prop where
  valid : Algo2Lean.UnionFind.Valid model
  object : is_UnionFind heap layout.object
  readParent : field_UnionFind_parent heap layout.object = some layout.parent
  readRank : field_UnionFind_rank heap layout.object = some layout.rank
  readSize : field_UnionFind_size heap layout.object = some (n : Int)
  parentAllocated : layout.parent < heap.nextRef
  rankAllocated : layout.rank < heap.nextRef
  separate : layout.parent ≠ layout.rank
  parents : ∀ vertex : Fin n, heap.read layout.parent (vertex.val : Int) = (model.parent vertex).val
  ranks : ∀ vertex : Fin n, heap.read layout.rank (vertex.val : Int) = (model.rank vertex : Int)



/-- The pure result of compressing one complete parent path on return. -/
abbrev findResult := @Algo2Lean.UnionFind.compressPath

@[simp] theorem findResult_representative {n : Nat} (model : State n) (vertex : Fin n)
    (length : Nat) : (findResult model vertex length).representative = model.representative := by
  induction length generalizing vertex with
  | zero => rfl
  | succ length ih => exact ih (model.parent vertex)

@[simp] theorem findResult_rank {n : Nat} (model : State n) (vertex : Fin n)
    (length : Nat) : (findResult model vertex length).rank = model.rank := by
  induction length generalizing vertex with
  | zero => rfl
  | succ length ih => exact ih (model.parent vertex)












@[simp] theorem parent_tick (heap : Heap) (object : Ref_UnionFind) (clock : String) (amount : Nat) :
    field_UnionFind_parent (heap.tick clock amount) object = field_UnionFind_parent heap object := rfl
@[simp] theorem rank_tick (heap : Heap) (object : Ref_UnionFind) (clock : String) (amount : Nat) :
    field_UnionFind_rank (heap.tick clock amount) object = field_UnionFind_rank heap object := rfl
@[simp] theorem parent_write (heap : Heap) (object : Ref_UnionFind) (ref : SeqRef) (index value : Int) :
    field_UnionFind_parent (heap.write ref index value) object = field_UnionFind_parent heap object := rfl
@[simp] theorem rank_write (heap : Heap) (object : Ref_UnionFind) (ref : SeqRef) (index value : Int) :
    field_UnionFind_rank (heap.write ref index value) object = field_UnionFind_rank heap object := rfl

/-- Constant-time rank-linking after the two representative lookups. -/
def unionHeap (heap : Heap) (layout : Layout) (left right : Int) : Heap :=
  let charged := heap.tick "uf_union"
  if left = right then charged
  else if heap.read layout.rank left < heap.read layout.rank right then
    charged.write layout.parent left right
  else if heap.read layout.rank right < heap.read layout.rank left then
    charged.write layout.parent right left
  else (charged.write layout.parent right left).write layout.rank left
    (heap.read layout.rank left + 1)




/-- Heap effect of linking a lower-ranked root under a higher-ranked root. -/
def linkHeap (heap : Heap) (layout : Layout) (loser winner : Int) : Heap :=
  let linked := heap.write layout.parent loser winner
  if heap.read layout.rank loser = heap.read layout.rank winner then
    linked.write layout.rank winner (heap.read layout.rank winner + 1)
  else linked






/-- The sum of all four union-find source clocks. -/
def work (clocks : Clocks) : Nat :=
  clocks "uf_init" + clocks "uf_find" + clocks "uf_compress" + clocks "uf_union"



@[simp] theorem unionHeap_clocks (heap : Heap) (layout : Layout) (left right : Int) (clock : String) :
    (unionHeap heap layout left right).clocks clock =
      heap.clocks clock + if clock = "uf_union" then 1 else 0 := by
  by_cases same : left = right <;>
    by_cases less : heap.read layout.rank left < heap.read layout.rank right <;>
    by_cases more : heap.read layout.rank right < heap.read layout.rank left <;>
    by_cases counter : clock = "uf_union" <;> simp [unionHeap, same, less, more, counter, Heap.tick, Heap.write]








/-- A method changes only its owned arrays and allocates no storage. Clocks
    have a separate, exact increment contract. -/
structure Storage (before after : Heap) (sequences : List SeqRef) : Prop where
  footprint : before.Footprint after sequences [] []
  nextRef : after.nextRef = before.nextRef
  nextObject : after.nextObject = before.nextObject
  nextCollection : after.nextCollection = before.nextCollection

/-- Following `length` parent links performs one final root test and compresses
    every visited non-root vertex. All other clocks have zero increment. -/
def findCosts (length : Nat) : Clocks := fun clock =>
  (if clock = "uf_find" then length + 1 else 0) +
  (if clock = "uf_compress" then length else 0)

/-- Two find calls and one rank comparison/link stage make one union. -/
def unionCosts (first second : Nat) : Clocks := fun clock =>
  findCosts first clock + findCosts second clock + if clock = "uf_union" then 1 else 0

/-- The precise model produced by the source's two full compressions and link. -/
def unionResult {n : Nat} (model : State n) (a b : Fin n) (first second : Nat) : State n :=
  Algo2Lean.UnionFind.union (findResult (findResult model a first) b second) a b











@[simp] theorem work_findCosts (length : Nat) : work (findCosts length) = 2 * length + 1 := by
  simp [work, findCosts]
  omega

@[simp] theorem work_unionCosts (first second : Nat) :
    work (unionCosts first second) = 2 * (first + second) + 3 := by
  simp [work, unionCosts, findCosts]
  omega












-- Main result: Correctness and running time


end UnionFindAnalysis


