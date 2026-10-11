-- Prove2me | Definitions.Def_Algo_union_find_init_Analysis
-- name    : Algo_union_find_init_Analysis
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:51:43.502033+00:00
-- url     : https://prove2.me/theorems/009c9f4b-9434-4e27-9cfc-bb2056d2e43f
-- title:
--   Mutable union-find initialization: heap, layout and exact costs
-- statement:
--   `newHeap heap n` describes the constructor's final heap and `newLayout heap` identifies its fresh union-find object, parent array and rank array. `constructorCosts n` assigns $n+1$ to `uf_init` and zero to every other clock. Definitions for the initialization loop express the partially initialized prefix.
--
--   The associated constructor theorem nodes establish execution, singleton representation, exact allocation counts and preservation of the caller's previous storage. These are facts proved about this heap description, not assumptions built into a client-specific algorithm.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/kruskal/analysis/union_find_init.lean

import Definitions.Def_Algo_union_find_Analysis

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Construction of the reusable rank-and-compression disjoint-set structure.
The constructor allocates one object and two arrays, initializes singleton
components, and charges exactly `n + 1` initialization ticks. -/

namespace UnionFindAnalysis

open Algo2LeanCore Algo2LeanGenerated
open Algo.union_find Algo.union_find.Algo2LeanGenerated

/-- The exact heap effect of initializing a consecutive interval of parent entries. -/
def initializeEntries (heap : Heap) (parent : SeqRef) (first : Int) : Nat → Heap
  | 0 => heap
  | count + 1 => initializeEntries ((heap.write parent first first).tick "uf_init")
      parent (first + 1) count

@[simp] theorem initializeEntries_objects (heap : Heap) (parent : SeqRef)
    (first : Int) (count : Nat) :
    (initializeEntries heap parent first count).objects = heap.objects := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih => simp [initializeEntries, ih, Heap.write]

@[simp] theorem initializeEntries_nextObject (heap : Heap) (parent : SeqRef)
    (first : Int) (count : Nat) :
    (initializeEntries heap parent first count).nextObject = heap.nextObject := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih => simp [initializeEntries, ih]

@[simp] theorem initializeEntries_nextRef (heap : Heap) (parent : SeqRef)
    (first : Int) (count : Nat) :
    (initializeEntries heap parent first count).nextRef = heap.nextRef := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih => simp [initializeEntries, ih]

@[simp] theorem initializeEntries_collections (heap : Heap) (parent : SeqRef)
    (first : Int) (count : Nat) :
    (initializeEntries heap parent first count).collections = heap.collections := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih => simp [initializeEntries, ih]

@[simp] theorem initializeEntries_nextCollection (heap : Heap) (parent : SeqRef)
    (first : Int) (count : Nat) :
    (initializeEntries heap parent first count).nextCollection = heap.nextCollection := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih => simp [initializeEntries, ih]



/-- Allocate the two zero-filled arrays and install the object's fields. -/
def prepareInitialHeap (heap : Heap) (object : Ref_UnionFind) (size : Int) : Heap :=
  let withParent := set_UnionFind_parent (heap.allocate (fun _ => 0)) object heap.nextRef
  let withRank := set_UnionFind_rank (withParent.allocate (fun _ => 0)) object withParent.nextRef
  set_UnionFind_size withRank object size

/-- The initializer's exact output heap. -/
def initializedHeap (heap : Heap) (object : Ref_UnionFind) (size : Nat) : Heap :=
  initializeEntries ((prepareInitialHeap heap object size).tick "uf_init") heap.nextRef 0 size

/-- The constructor's exact output heap, with all allocation identities explicit. -/
def newHeap (heap : Heap) (size : Nat) : Heap :=
  initializedHeap (heap.allocateObject "union_find.UnionFind") heap.nextObject size

/-- The two newly allocated sequence references and their owning object. -/
def newLayout (heap : Heap) : Layout :=
  ⟨heap.nextObject, heap.nextRef, heap.nextRef + 1⟩

@[simp] theorem prepareInitialHeap_valid (heap : Heap) (object : Ref_UnionFind) (size : Int)
    (valid : is_UnionFind heap object) : is_UnionFind (prepareInitialHeap heap object size) object := by
  simpa [prepareInitialHeap, is_UnionFind, set_UnionFind_parent, set_UnionFind_rank,
    set_UnionFind_size] using valid

@[simp] theorem prepareInitialHeap_nextRef (heap : Heap) (object : Ref_UnionFind) (size : Int) :
    (prepareInitialHeap heap object size).nextRef = heap.nextRef + 2 := by
  simp [prepareInitialHeap, set_UnionFind_parent, set_UnionFind_rank, set_UnionFind_size, Nat.add_assoc]

@[simp] theorem prepareInitialHeap_parent (heap : Heap) (object : Ref_UnionFind) (size : Int)
    (valid : is_UnionFind heap object) :
    field_UnionFind_parent (prepareInitialHeap heap object size) object = some heap.nextRef := by
  have preparedValid := prepareInitialHeap_valid heap object size valid
  rw [field_UnionFind_parent, if_pos preparedValid]
  simp [prepareInitialHeap, set_UnionFind_parent, set_UnionFind_rank, set_UnionFind_size,
    valid.2, ObjectValue.asSeq]

@[simp] theorem prepareInitialHeap_rank (heap : Heap) (object : Ref_UnionFind) (size : Int)
    (valid : is_UnionFind heap object) :
    field_UnionFind_rank (prepareInitialHeap heap object size) object = some (heap.nextRef + 1) := by
  have preparedValid := prepareInitialHeap_valid heap object size valid
  rw [field_UnionFind_rank, if_pos preparedValid]
  simp [prepareInitialHeap, set_UnionFind_parent, set_UnionFind_rank, set_UnionFind_size,
    valid.2, ObjectValue.asSeq]

@[simp] theorem prepareInitialHeap_size (heap : Heap) (object : Ref_UnionFind) (size : Int)
    (valid : is_UnionFind heap object) :
    field_UnionFind_size (prepareInitialHeap heap object size) object = some size := by
  have preparedValid := prepareInitialHeap_valid heap object size valid
  rw [field_UnionFind_size, if_pos preparedValid]
  simp [prepareInitialHeap, set_UnionFind_parent, set_UnionFind_rank, set_UnionFind_size,
    valid.2, ObjectValue.asInt]

@[simp] theorem initializedHeap_valid (heap : Heap) (object : Ref_UnionFind) (size : Nat)
    (valid : is_UnionFind heap object) : is_UnionFind (initializedHeap heap object size) object := by
  simpa [initializedHeap, is_UnionFind, Heap.objectClass] using
    prepareInitialHeap_valid heap object size valid













@[simp] theorem initializeEntries_objectClass (heap : Heap) (parent : SeqRef)
    (first : Int) (count : Nat) (object : Ref_UnionFind) :
    (initializeEntries heap parent first count).objectClass object = heap.objectClass object := by
  simp [Heap.objectClass]

@[simp] theorem initializeEntries_readField (heap : Heap) (parent : SeqRef)
    (first : Int) (count : Nat) (object : Ref_UnionFind) (field : String) :
    (initializeEntries heap parent first count).readField object field = heap.readField object field := by
  simp [Heap.readField]









-- Main result: Correctness and running time



/-- Constructor cost includes setup and one initialized parent per vertex. -/
def constructorCosts (size : Nat) : Clocks := fun clock =>
  if clock = "uf_init" then size + 1 else 0







@[simp] theorem constructor_work (size : Nat) : work (constructorCosts size) = size + 1 := by
  simp [work, constructorCosts]

end UnionFindAnalysis


