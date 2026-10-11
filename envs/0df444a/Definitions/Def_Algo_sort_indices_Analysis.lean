-- Prove2me | Definitions.Def_Algo_sort_indices_Analysis
-- name    : Algo_sort_indices_Analysis
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:51:09.523841+00:00
-- url     : https://prove2.me/theorems/57bb57b3-3316-41fe-8460-7d9002ac5776
-- title:
--   Sorting identifiers: permutation, preservation and clock budgets
-- statement:
--   `SortedPermutation keys count output` requires a finite permutation of the identifiers $0,\ldots,count-1$, pairwise nondecreasing input keys, and agreement with the output sequence on that finite prefix. It does not specify the sequence outside the prefix or impose a stable order on equal keys.
--
--   `Preserves` protects every previously allocated sequence/object and all typed collections. `Budget count steps before after` gives a per-clock upper bound using `rate`: 1 for `sort_steps`, twice the binary depth for `heap_comparisons`, and binary depth plus one for `heap_swaps`. `runtime` sums those three clocks and `runtimeBound m = 2m(3 floor(log₂(m+1))+2)`. The independent sorting `call` theorem supplies these definitions as proved postconditions.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/kruskal/analysis/sort_indices.lean

import Definitions.Def_Algo_sort_indices_Points
import Definitions.Def_Algo_sort_indices_Facts
import Definitions.Def_Algo_indexed_heap_Analysis
import Definitions.Def_Algo2LeanLib_FiniteIndex
import Definitions.Def_Algo2LeanLib_CallCost

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Sorting identifiers keeps weights in their original sequence. The insertion
phase reuses the proved heap insertion contract; the extraction phase reuses
minimum extraction. Neither phase unfolds a heap operation's transitions.
-/

open Algo2LeanCore Algo2LeanGenerated
open Algo.indexed_heap.Algo2LeanGenerated hiding Step Frame Result Configuration Stack Transcript
open Algo.sort_indices Algo.sort_indices.Algo2LeanGenerated
open BinaryModuleAnalysis

namespace SortIndicesAnalysis

/-- The finite output is a permutation of the identifiers, ordered by key. -/
def SortedPermutation (keys : Seq) (count : Int) (output : Seq) : Prop :=
  ∃ values : List Int, values.Perm (Algo2Lean.FiniteIndex.range count) ∧
    values.Pairwise (fun first second => keys first ≤ keys second) ∧
    ∀ index : Nat, index < values.length → output index = values[index]!

/-- Sorting changes no previously allocated client data. -/
structure Preserves (before after : Heap) : Prop where
  sequences : ∀ ref, ref < before.nextRef → after.read ref = before.read ref
  objects : ∀ ref, ref < before.nextObject → after.objects ref = before.objects ref
  collections : after.collections = before.collections
  refs : before.nextRef ≤ after.nextRef
  objectRefs : before.nextObject ≤ after.nextObject
  collectionRefs : after.nextCollection = before.nextCollection
  clocks : ∀ name, name ≠ "sort_steps" → name ≠ "heap_comparisons" → name ≠ "heap_swaps" →
    after.clocks name = before.clocks name

/-- Cost of the source loop body plus logarithmic heap operations. -/
def rate (count : Int) (clock : String) : Nat :=
  if clock = "sort_steps" then 1
  else if clock = "heap_comparisons" then 2 * depth count
  else if clock = "heap_swaps" then depth count + 1 else 0

def Budget (count : Int) (steps : Nat) (before after : Heap) : Prop :=
  ∀ clock, after.clocks clock ≤ before.clocks clock + steps * rate count clock





/-- Internal heap operations preserve every array except the three private
    heap arrays and the newly allocated output array. -/
 structure Storage (queue : ObjectRef) (privateRefs : List SeqRef)
    (before after : Heap) : Prop where
  arrays : ∀ ref, ref ∉ privateRefs → after.read ref = before.read ref
  objects : ∀ ref, ref ≠ queue → after.objects ref = before.objects ref
  nextRef : after.nextRef = before.nextRef
  nextObject : after.nextObject = before.nextObject
  collections : after.collections = before.collections
  nextCollection : after.nextCollection = before.nextCollection
  clocks : ∀ name, name ≠ "sort_steps" → name ≠ "heap_comparisons" → name ≠ "heap_swaps" →
    after.clocks name = before.clocks name

















 def Contents (keys : Seq) (remaining : List Int) (heap : Heap) (layout : Layout) : Prop :=
  (∀ value, 0 ≤ heap.read layout.positions value ↔ value ∈ remaining) ∧
  (∀ value ∈ remaining, heap.read layout.keys value = keys value)

 def afterExtract (state : State_sort_indices) (vertex : Int) : State_sort_indices :=
  { state with v4 := state.v4 + 1, t6 := true, t7 := vertex, t8 := state.v4, t9 := state.v3, t10 := state.v2 }





 def afterInsert (state : State_sort_indices) (key : Int) : State_sort_indices :=
  { state with v4 := state.v4 + 1, t11 := true, t12 := (), t13 := state.v2, t14 := state.v4, t15 := key }







 def preparedHeap (heap : Heap) : Heap := (newHeap heap).allocate (fun _ => 0)







/-- Unit weight for loop bodies, heap comparisons, and heap swaps. -/
def runtime (costs : Clocks) : Nat :=
  Clocks.weighted [("sort_steps", 1), ("heap_comparisons", 1), ("heap_swaps", 1)] costs

/-- An explicit O(n log(n + 1)) operation bound. -/
def runtimeBound (count : Nat) : Nat := 2 * count * (3 * (count + 1).log2 + 2)



-- Main result: Correctness


-- Main result: Running time


end SortIndicesAnalysis


