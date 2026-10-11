-- Prove2me | Definitions.Def_Algo_indexed_heap_Analysis
-- name    : Algo_indexed_heap_Analysis
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:41:02.849773+00:00
-- url     : https://prove2.me/theorems/4b412148-57a4-4e17-85ea-420410c03856
-- title:
--   Indexed binary heap representation and operation postconditions
-- statement:
--   `BinaryModuleAnalysis.Layout` identifies the vertex, inverse-position and key arrays and active size. `Indexed` states the inverse-map property; `Ordered` is min-heap order. `QueueRep` combines valid allocated storage, indexing, nonnegative size, and ordering. Loop predicates and `UpInvariant`/`DownInvariant` describe the local order violations repaired by sifting.
--
--   `Extracted` packages minimum-key correctness, removal of exactly one present vertex, restoration of the queue, preservation of keys and unrelated storage, and bounds on `heap_comparisons` and `heap_swaps`. `depth i = (i.toNat+1).log2` gives the binary-tree depth used by those bounds. These definitions are shared by the operation theorem nodes and the independent sorter.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/kruskal/analysis/indexed_heap.lean

import Definitions.Def_Algo_indexed_heap_Points

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Analysis outline:
- `new_heap_rep`: Empty heap representation.
- `insert_correct`: Insertion correctness and cost.
- `decrease_correct`: Decrease-key correctness and cost.
- `pop_correct`: Minimum extraction correctness and cost.
-/

open Algo.indexed_heap Algo.indexed_heap.Algo2LeanGenerated

open Algo2LeanCore Algo2LeanGenerated

namespace BinaryModuleAnalysis

-- A small source-facing description of the object's storage. The three arrays
-- are separate mutable sequences; aliases to the MinHeap object remain valid.
structure Layout where
  vertices : SeqRef
  positions : SeqRef
  keys : SeqRef
  size : Int

structure Layout.Valid (layout : Layout) (heap : Heap) (queue : Ref_MinHeap) : Prop where
  object : is_MinHeap heap queue
  readVertices : field_MinHeap_vertices heap queue = some layout.vertices
  readPositions : field_MinHeap_positions heap queue = some layout.positions
  readKeys : field_MinHeap_keys heap queue = some layout.keys
  readSize : field_MinHeap_size heap queue = some layout.size
  verticesAllocated : layout.vertices < heap.nextRef
  positionsAllocated : layout.positions < heap.nextRef
  keysAllocated : layout.keys < heap.nextRef
  verticesPositions : layout.vertices ≠ layout.positions
  verticesKeys : layout.vertices ≠ layout.keys
  positionsKeys : layout.positions ≠ layout.keys

-- These observations use only the generated field interface. Updating an
-- array does not replace the object's fields or change its identity.
@[simp] theorem vertices_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_MinHeap) :
    field_MinHeap_vertices (heap.write ref index value) queue =
      field_MinHeap_vertices heap queue := rfl

@[simp] theorem positions_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_MinHeap) :
    field_MinHeap_positions (heap.write ref index value) queue =
      field_MinHeap_positions heap queue := rfl

-- Exact heap effect of swap, including the cost counter. The original two
-- vertices are read before either array is changed, including when i = j.
def swapHeap (heap : Heap) (layout : Layout) (i j : Int) : Heap :=
  let a := heap.read layout.vertices i
  let b := heap.read layout.vertices j
  ((((heap.write layout.vertices i b).write layout.vertices j a).write
    layout.positions a j).write layout.positions b i).tick "heap_swaps"



-- A permutation of positions, with all other positions left fixed.
def exchange (values : Seq) (i j index : Int) : Int :=
  if index = j then values i else if index = i then values j else values index









-- No duplicate active vertices, no stale positive positions, and exactly -1
-- for vertices outside the heap. These are finite-prefix map invariants.
structure Indexed (vertices positions : Seq) (size : Int) : Prop where
  forward : ∀ index, 0 ≤ index → index < size → positions (vertices index) = index
  backward : ∀ vertex, 0 ≤ positions vertex →
    positions vertex < size ∧ vertices (positions vertex) = vertex
  absent : ∀ vertex, positions vertex < 0 → positions vertex = -1



@[simp] theorem exchange_left (values : Seq) (i j : Int) :
    exchange values i j i = values j := by
  by_cases same : i = j <;> simp [exchange, same]

@[simp] theorem exchange_right (values : Seq) (i j : Int) :
    exchange values i j j = values i := by simp [exchange]

-- Swapping two valid heap positions preserves the inverse map, including a
-- self-swap. No heap-order assumption or concrete input values are required.


-- Position numbers may change, but exactly the same vertices remain present.






-- Simple endpoint cases are checked against the compiled methods as well.






-- The mathematical depth is the prospective logarithmic bound. Each upward
-- move decreases it by exactly one; downward moves increase it by one.
def depth (index : Int) : Nat := (index.toNat + 1).log2







-- Construction keeps its heap effect in source order. Each sequence has a
-- distinct fresh reference, and the empty queue has no present vertices.
def initializedHeap (heap : Heap) (queue : Ref_MinHeap) : Heap :=
  let first := set_MinHeap_vertices (heap.allocate (fun _ => 0)) queue heap.nextRef
  let second := set_MinHeap_positions (first.allocate (fun _ => -1)) queue first.nextRef
  let third := set_MinHeap_keys (second.allocate (fun _ => 0)) queue second.nextRef
  set_MinHeap_size third queue 0

def emptyLayout (heap : Heap) : Layout :=
  ⟨heap.nextRef, heap.nextRef + 1, heap.nextRef + 2, 0⟩





def newHeap (heap : Heap) : Heap :=
  initializedHeap (heap.allocateObject "indexed_heap.MinHeap") heap.nextObject













@[simp] theorem keys_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_MinHeap) :
    field_MinHeap_keys (heap.write ref index value) queue = field_MinHeap_keys heap queue := rfl

@[simp] theorem size_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_MinHeap) :
    field_MinHeap_size (heap.write ref index value) queue = field_MinHeap_size heap queue := rfl















def poppedHeap (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) : Heap :=
  (set_MinHeap_size (swapHeap heap layout 0 0) queue 0).write
    layout.positions (heap.read layout.vertices 0) (-1)













-- Client-owned arrays, such as Dijkstra's distances and settled flags, are
-- unchanged by creating and manipulating this separate priority queue.






/-- The parent of a positive position in the zero-based binary heap. -/
def parent (index : Int) : Int := Int.fdiv (index - 1) 2

/-- Heap order concerns only the finite active prefix; priorities are arbitrary integers. -/
def Ordered (priority : Seq) (size : Int) : Prop :=
  ∀ child, 0 < child → child < size → priority (parent child) ≤ priority child



/-- At sift-up's moving position only its incoming edge may violate heap order.
    Its parent is also below its children, so exchanging parent and child is safe. -/
structure UpInvariant (priority : Seq) (size index : Int) : Prop where
  orderedExcept : ∀ child, 0 < child → child < size → child ≠ index →
    priority (parent child) ≤ priority child
  parentBelowChildren : ∀ child, 0 < child → child < size → parent child = index →
    0 < index → priority (parent index) ≤ priority child















-- The loop proof is expressed through the named source location and its two
-- live inputs. Other temporary locals are irrelevant to the specification.
def AtSiftUp (state : Configuration) (queue : Ref_MinHeap) (index : Int) : Prop :=
  MinHeap.sift_up.At.up_loop state ∧
    MinHeap.sift_up.Local.self state = some queue ∧
    MinHeap.sift_up.Local.i state = some index

@[simp] theorem keys_tick (heap : Heap) (name : String) (amount : Nat) (queue : Ref_MinHeap) :
    field_MinHeap_keys (heap.tick name amount) queue = field_MinHeap_keys heap queue := rfl

@[simp] theorem vertices_tick (heap : Heap) (name : String) (amount : Nat) (queue : Ref_MinHeap) :
    field_MinHeap_vertices (heap.tick name amount) queue = field_MinHeap_vertices heap queue := rfl







def upHeap (heap : Heap) (layout : Layout) (index : Int) : Heap :=
  swapHeap (heap.tick "heap_comparisons") layout index (Int.fdiv (index - 1) 2)





-- One unsuccessful comparison swaps with the parent and returns to the named
-- loop location. Any proof for the remaining loop can be plugged in here.


-- Reordering the integer arrays leaves object fields, typed collections, and
-- all allocation counters unchanged. In particular, graph objects in a caller
-- remain available with their original fields after either sifting method.
structure OtherStoragePreserved (before after : Heap) : Prop where
  nextRef : after.nextRef = before.nextRef
  nextObject : after.nextObject = before.nextObject
  objects : after.objects = before.objects
  nextCollection : after.nextCollection = before.nextCollection
  collections : after.collections = before.collections





-- The remaining loop has one final heap for every configuration with these
-- source inputs. Induction follows tree depth, not the transcript length.


-- A valid active index always terminates. The map invariant is preserved, and
-- each of the two instrumented operation counts is at most floor(log2(i+1)).
-- Sift-up repairs its expected single-edge order exception. Keys and client
-- arrays are preserved because only the vertices and positions arrays change.








/-- Preparing an absent vertex at the new last position, before sift-up. -/
def appendedHeap (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (vertex key : Int) : Heap :=
  set_MinHeap_size (((heap.write layout.keys vertex key).write layout.vertices layout.size vertex).write
    layout.positions vertex layout.size) queue (layout.size + 1)

























/-- A usable priority queue combines storage validity, inverse positions, and
    heap order. Clients need no program counters or transcript representation. -/
structure QueueRep (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) : Prop where
  valid : layout.Valid heap queue
  nonnegative : 0 ≤ layout.size
  indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size
  ordered : Ordered (fun index => heap.read layout.keys (heap.read layout.vertices index)) layout.size









/-- During sift-down, only edges leaving the moving position may be unordered.
    Its parent is below its children, so promoting the smaller child is safe. -/
structure DownInvariant (priority : Seq) (size index : Int) : Prop where
  orderedExcept : ∀ child, 0 < child → child < size → parent child ≠ index →
    priority (parent child) ≤ priority child
  parentBelowChildren : ∀ child, 0 < child → child < size → parent child = index →
    0 < index → priority (parent index) ≤ priority child











-- Sift-down first selects the smaller child, then compares it with the parent.
def selectedChild (heap : Heap) (layout : Layout) (index : Int) : Int :=
  if 2 * index + 2 < layout.size ∧
      heap.read layout.keys (heap.read layout.vertices (2 * index + 2)) <
      heap.read layout.keys (heap.read layout.vertices (2 * index + 1))
  then 2 * index + 2 else 2 * index + 1

def selectionComparisons (layout : Layout) (index : Int) : Nat :=
  if 2 * index + 2 < layout.size then 1 else 0

def AtSiftDown (state : Configuration) (queue : Ref_MinHeap) (index : Int) : Prop :=
  MinHeap.sift_down.At.down_loop state ∧
    MinHeap.sift_down.Local.self state = some queue ∧
    MinHeap.sift_down.Local.i state = some index

def AtChildComparison (state : Configuration) (queue : Ref_MinHeap) (index child : Int) : Prop :=
  MinHeap.sift_down.At.compare_child state ∧
    MinHeap.sift_down.Local.self state = some queue ∧
    MinHeap.sift_down.Local.i state = some index ∧
    MinHeap.sift_down.Local.child state = some child



















-- Induction descends through the tree. Each non-leaf iteration examines at
-- most two keys and exchanges at most one pair of heap positions.


-- The public contract allows arbitrary initial priorities. Its conditional
-- repair clause explains when this terminating run also restores heap order.


/-- The heap after moving the old root to the last position, shrinking the
    active prefix, and marking that old root absent, before any sift-down. -/
def removedHeap (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) : Heap :=
  (set_MinHeap_size (swapHeap heap layout 0 (layout.size - 1)) queue (layout.size - 1)).write
    layout.positions (heap.read layout.vertices 0) (-1)































/-- Minimum extraction's client contract: remove one minimum-priority vertex,
    preserve every other key, restore the queue, and bound the two cost clocks. -/
structure Extracted (before after : Heap) (queue : Ref_MinHeap) (layout : Layout) (vertex : Int) : Prop where
  representation : QueueRep after queue { layout with size := layout.size - 1 }
  wasPresent : 0 ≤ before.read layout.positions vertex
  minimum : ∀ value, 0 ≤ before.read layout.positions value →
    before.read layout.keys vertex ≤ before.read layout.keys value
  membership : ∀ value, 0 ≤ after.read layout.positions value ↔
    0 ≤ before.read layout.positions value ∧ value ≠ vertex
  keys : ∀ value, after.read layout.keys value = before.read layout.keys value
  comparisons : Heap.cost before after "heap_comparisons" ≤ 2 * depth (layout.size - 2)
  swaps : Heap.cost before after "heap_swaps" ≤ depth (layout.size - 2) + 1
  otherArrays : ∀ ref, ref ≠ layout.vertices → ref ≠ layout.positions →
    ∀ index, after.read ref index = before.read ref index
  otherClocks : ∀ name, name ≠ "heap_comparisons" → name ≠ "heap_swaps" →
    after.clocks name = before.clocks name
  otherStorage : OtherStoragePreserved (set_MinHeap_size before queue (layout.size - 1)) after











end BinaryModuleAnalysis


