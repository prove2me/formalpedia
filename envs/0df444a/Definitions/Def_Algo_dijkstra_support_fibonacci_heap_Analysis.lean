-- Prove2me | Definitions.Def_Algo_dijkstra_support_fibonacci_heap_Analysis
-- name    : Algo_dijkstra_support_fibonacci_heap_Analysis
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:51:01.341106+00:00
-- url     : https://prove2.me/theorems/e9ffb2b0-77eb-4008-9286-cd0da07902b3
-- title:
--   Algo.dijkstra.support.fibonacci_heap.Analysis definitions
-- statement:
--   Definitions and required structural lemmas from `Algo.dijkstra.support.fibonacci_heap.Analysis`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/analysis/dijkstra/support/fibonacci_heap.lean

import Definitions.Def_Algo_fibonacci_heap_Points
import Definitions.Def_Algo2LeanLib_FibonacciConsolidation
import Definitions.Def_Algo2LeanLib_HeapFrame
import Definitions.Def_Algo2LeanLib_FibonacciDeleteMin
import Definitions.Def_Algo2LeanLib_FibonacciStorage
import Definitions.Def_Algo2LeanLib_FibonacciRootInsertion
import Definitions.Def_Algo2LeanLib_FibonacciRebuild
import Definitions.Def_Algo2LeanLib_FibonacciKeyUpdate

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Analysis outline:
- `new_heap_representation`: Empty Fibonacci heap representation.
- `QueueRep.update`: Insertion and decrease-key amortized contract.
- `QueueRep.pop_minimum`: Minimum extraction amortized contract.
-/

open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap Algo.fibonacci_heap.Algo2LeanGenerated

namespace FibonacciModuleAnalysis

-- Storage descriptions are independent of the mathematical forest invariant.
-- This lets local ring facts apply inside any caller and at any named location.
structure Layout where
  keys : SeqRef
  parents : SeqRef
  children : SeqRef
  left : SeqRef
  right : SeqRef
  degrees : SeqRef
  marks : SeqRef
  present : SeqRef
  table : SeqRef
  minimum : Int
  size : Int

def Layout.refs (layout : Layout) : List SeqRef :=
  [layout.keys, layout.parents, layout.children, layout.left, layout.right, layout.degrees, layout.marks, layout.present, layout.table]

structure Layout.Valid (layout : Layout) (heap : Heap) (queue : Ref_FibonacciHeap) : Prop where
  object : is_FibonacciHeap heap queue
  readKeys : field_FibonacciHeap_keys heap queue = some layout.keys
  readParents : field_FibonacciHeap_parents heap queue = some layout.parents
  readChildren : field_FibonacciHeap_children heap queue = some layout.children
  readLeft : field_FibonacciHeap_left heap queue = some layout.left
  readRight : field_FibonacciHeap_right heap queue = some layout.right
  readDegrees : field_FibonacciHeap_degrees heap queue = some layout.degrees
  readMarks : field_FibonacciHeap_marks heap queue = some layout.marks
  readPresent : field_FibonacciHeap_present heap queue = some layout.present
  readTable : field_FibonacciHeap_table heap queue = some layout.table
  readMinimum : field_FibonacciHeap_minimum heap queue = some layout.minimum
  readSize : field_FibonacciHeap_size heap queue = some layout.size
  keysAllocated : layout.keys < heap.nextRef
  parentsAllocated : layout.parents < heap.nextRef
  childrenAllocated : layout.children < heap.nextRef
  leftAllocated : layout.left < heap.nextRef
  rightAllocated : layout.right < heap.nextRef
  degreesAllocated : layout.degrees < heap.nextRef
  marksAllocated : layout.marks < heap.nextRef
  presentAllocated : layout.present < heap.nextRef
  tableAllocated : layout.table < heap.nextRef
  separate : layout.refs.Nodup

@[simp] theorem keys_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_keys (heap.write ref index value) queue =
      field_FibonacciHeap_keys heap queue := rfl

@[simp] theorem parents_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_parents (heap.write ref index value) queue =
      field_FibonacciHeap_parents heap queue := rfl

@[simp] theorem children_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_children (heap.write ref index value) queue =
      field_FibonacciHeap_children heap queue := rfl

@[simp] theorem left_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_left (heap.write ref index value) queue =
      field_FibonacciHeap_left heap queue := rfl

@[simp] theorem right_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_right (heap.write ref index value) queue =
      field_FibonacciHeap_right heap queue := rfl

@[simp] theorem degrees_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_degrees (heap.write ref index value) queue =
      field_FibonacciHeap_degrees heap queue := rfl

@[simp] theorem marks_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_marks (heap.write ref index value) queue =
      field_FibonacciHeap_marks heap queue := rfl

@[simp] theorem present_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_present (heap.write ref index value) queue =
      field_FibonacciHeap_present heap queue := rfl

@[simp] theorem table_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_table (heap.write ref index value) queue =
      field_FibonacciHeap_table heap queue := rfl

@[simp] theorem minimum_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_minimum (heap.write ref index value) queue =
      field_FibonacciHeap_minimum heap queue := rfl

@[simp] theorem size_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_size (heap.write ref index value) queue =
      field_FibonacciHeap_size heap queue := rfl

-- Detaching a vertex changes four links and does not require a whole run.
def removeHeap (heap : Heap) (layout : Layout) (vertex : Int) : Heap :=
  let before := heap.read layout.left vertex
  let after := heap.read layout.right vertex
  (((heap.write layout.right before after).write layout.left after before).write
    layout.left vertex vertex).write layout.right vertex vertex











-- Initialization follows the source allocation order. The exact-effect
-- statement can be reused without opening this method's transition rules.
def initializedHeap (heap : Heap) (queue : Ref_FibonacciHeap) : Heap :=
  let h0 := set_FibonacciHeap_keys (heap.allocate (fun _ => 0)) queue heap.nextRef
  let h1 := set_FibonacciHeap_parents (h0.allocate (fun _ => -1)) queue h0.nextRef
  let h2 := set_FibonacciHeap_children (h1.allocate (fun _ => -1)) queue h1.nextRef
  let h3 := set_FibonacciHeap_left (h2.allocate (fun _ => 0)) queue h2.nextRef
  let h4 := set_FibonacciHeap_right (h3.allocate (fun _ => 0)) queue h3.nextRef
  let h5 := set_FibonacciHeap_degrees (h4.allocate (fun _ => 0)) queue h4.nextRef
  let h6 := set_FibonacciHeap_marks (h5.allocate (fun _ => 0)) queue h5.nextRef
  let h7 := set_FibonacciHeap_present (h6.allocate (fun _ => 0)) queue h6.nextRef
  let h8 := set_FibonacciHeap_table (h7.allocate (fun _ => -1)) queue h7.nextRef
  set_FibonacciHeap_size (set_FibonacciHeap_minimum h8 queue (-1)) queue 0

def emptyLayout (heap : Heap) : Layout :=
  ⟨heap.nextRef, heap.nextRef + 1, heap.nextRef + 2, heap.nextRef + 3, heap.nextRef + 4, heap.nextRef + 5, heap.nextRef + 6, heap.nextRef + 7, heap.nextRef + 8, -1, 0⟩





def newHeap (heap : Heap) : Heap :=
  initializedHeap (heap.allocateObject "fibonacci_heap.FibonacciHeap") heap.nextObject



























@[simp] theorem keys_tick (heap : Heap) (clock : String) (amount : Nat)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_keys (heap.tick clock amount) queue =
      field_FibonacciHeap_keys heap queue := rfl

@[simp] theorem parents_tick (heap : Heap) (clock : String) (amount : Nat)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_parents (heap.tick clock amount) queue =
      field_FibonacciHeap_parents heap queue := rfl

@[simp] theorem children_tick (heap : Heap) (clock : String) (amount : Nat)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_children (heap.tick clock amount) queue =
      field_FibonacciHeap_children heap queue := rfl

@[simp] theorem left_tick (heap : Heap) (clock : String) (amount : Nat)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_left (heap.tick clock amount) queue =
      field_FibonacciHeap_left heap queue := rfl

@[simp] theorem right_tick (heap : Heap) (clock : String) (amount : Nat)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_right (heap.tick clock amount) queue =
      field_FibonacciHeap_right heap queue := rfl

@[simp] theorem degrees_tick (heap : Heap) (clock : String) (amount : Nat)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_degrees (heap.tick clock amount) queue =
      field_FibonacciHeap_degrees heap queue := rfl

@[simp] theorem marks_tick (heap : Heap) (clock : String) (amount : Nat)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_marks (heap.tick clock amount) queue =
      field_FibonacciHeap_marks heap queue := rfl

@[simp] theorem present_tick (heap : Heap) (clock : String) (amount : Nat)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_present (heap.tick clock amount) queue =
      field_FibonacciHeap_present heap queue := rfl

@[simp] theorem table_tick (heap : Heap) (clock : String) (amount : Nat)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_table (heap.tick clock amount) queue =
      field_FibonacciHeap_table heap queue := rfl

@[simp] theorem minimum_tick (heap : Heap) (clock : String) (amount : Nat)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_minimum (heap.tick clock amount) queue =
      field_FibonacciHeap_minimum heap queue := rfl

@[simp] theorem size_tick (heap : Heap) (clock : String) (amount : Nat)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_size (heap.tick clock amount) queue =
      field_FibonacciHeap_size heap queue := rfl

def rootHeaderHeap (heap : Heap) (layout : Layout) (vertex : Int) : Heap :=
  (heap.write layout.parents vertex (-1)).write layout.marks vertex 0

def insertRingHeap (heap : Heap) (layout : Layout) (vertex : Int) : Heap :=
  let after := heap.read layout.right layout.minimum
  (((heap.write layout.left vertex layout.minimum).write layout.right vertex after).write
    layout.right layout.minimum vertex).write layout.left after vertex

def addRootHeap (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex : Int) : Heap :=
  let prepared := rootHeaderHeap heap layout vertex
  if layout.minimum < 0 then
    set_FibonacciHeap_minimum
      ((prepared.write layout.left vertex vertex).write layout.right vertex vertex) queue vertex
  else
    let linked := (insertRingHeap prepared layout vertex).tick "heap_comparisons"
    if linked.read layout.keys vertex < linked.read layout.keys layout.minimum then
      set_FibonacciHeap_minimum linked queue vertex
    else linked







theorem Layout.Valid.write (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (ref : SeqRef) (index value : Int) :
    layout.Valid (heap.write ref index value) queue := by
  exact ⟨valid.object, valid.readKeys, valid.readParents, valid.readChildren, valid.readLeft, valid.readRight, valid.readDegrees, valid.readMarks, valid.readPresent, valid.readTable, valid.readMinimum, valid.readSize, valid.keysAllocated, valid.parentsAllocated, valid.childrenAllocated, valid.leftAllocated, valid.rightAllocated, valid.degreesAllocated, valid.marksAllocated, valid.presentAllocated, valid.tableAllocated, valid.separate⟩

theorem Layout.Valid.tick (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (clock : String) (amount : Nat) :
    layout.Valid (heap.tick clock amount) queue := by
  exact ⟨valid.object, valid.readKeys, valid.readParents, valid.readChildren, valid.readLeft, valid.readRight, valid.readDegrees, valid.readMarks, valid.readPresent, valid.readTable, valid.readMinimum, valid.readSize, valid.keysAllocated, valid.parentsAllocated, valid.childrenAllocated, valid.leftAllocated, valid.rightAllocated, valid.degreesAllocated, valid.marksAllocated, valid.presentAllocated, valid.tableAllocated, valid.separate⟩

def linkHeaderHeap (heap : Heap) (layout : Layout) (child parent : Int) : Heap :=
  (heap.write layout.parents child parent).write layout.marks child 0

def linkRingHeap (heap : Heap) (layout : Layout) (child parent : Int) : Heap :=
  let first := heap.read layout.children parent
  if first < 0 then
    (heap.write layout.left child child).write layout.right child child
  else
    let before := heap.read layout.left first
    (((heap.write layout.left child before).write layout.right child first).write
      layout.right before child).write layout.left first child

def linkHeap (heap : Heap) (layout : Layout) (child parent : Int) : Heap :=
  let prepared := linkHeaderHeap heap layout child parent
  let ring := linkRingHeap prepared layout child parent
  let headed := ring.write layout.children parent child
  (headed.write layout.degrees parent (headed.read layout.degrees parent + 1)).tick "heap_links"

-- A link's compiled contract is independent of any whole-heap invariant.
-- Its callers separately establish equal degree, key order, and disjoint trees.









def cutHeaderHeap (heap : Heap) (layout : Layout) (vertex parent : Int) : Heap :=
  if heap.read layout.children parent = vertex then
    heap.write layout.children parent
      (if heap.read layout.right vertex = vertex then -1 else heap.read layout.right vertex)
  else heap

def cutTailHeap (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex parent : Int) : Heap :=
  let decreased := heap.write layout.degrees parent (heap.read layout.degrees parent - 1)
  let detached := removeHeap decreased layout vertex
  (addRootHeap detached queue layout vertex).tick "heap_cuts"

def cutHeap (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex parent : Int) : Heap :=
  cutTailHeap (cutHeaderHeap heap layout vertex parent) queue layout vertex parent

-- The proof composes the checked ring-removal and root-insertion contracts.
-- Their internal transitions are not revisited when a cut is verified.




def addRootLayout (heap : Heap) (layout : Layout) (vertex : Int) : Layout :=
  if layout.minimum < 0 then { layout with minimum := vertex }
  else
    let linked := (insertRingHeap (rootHeaderHeap heap layout vertex) layout vertex).tick
      "heap_comparisons"
    if linked.read layout.keys vertex < linked.read layout.keys layout.minimum then
      { layout with minimum := vertex }
    else layout



def cutLayout (heap : Heap) (layout : Layout) (vertex parent : Int) : Layout :=
  let headed := cutHeaderHeap heap layout vertex parent
  let decreased := headed.write layout.degrees parent (headed.read layout.degrees parent - 1)
  addRootLayout (removeHeap decreased layout vertex) layout vertex











@[simp] theorem add_root_layout_parents (heap : Heap) (layout : Layout) (vertex : Int) :
    (addRootLayout heap layout vertex).parents = layout.parents := by
  unfold addRootLayout
  split
  · rfl
  · dsimp only
    split <;> rfl

@[simp] theorem add_root_layout_marks (heap : Heap) (layout : Layout) (vertex : Int) :
    (addRootLayout heap layout vertex).marks = layout.marks := by
  unfold addRootLayout
  split
  · rfl
  · dsimp only
    split <;> rfl

@[simp] theorem cut_layout_parents (heap : Heap) (layout : Layout) (vertex parent : Int) :
    (cutLayout heap layout vertex parent).parents = layout.parents := by
  simp [cutLayout]

@[simp] theorem cut_layout_marks (heap : Heap) (layout : Layout) (vertex parent : Int) :
    (cutLayout heap layout vertex parent).marks = layout.marks := by
  simp [cutLayout]

-- Ranking every parent pointer is a strong sufficient termination premise.
-- The scoped parent-rank invariant restricts the ordering to active vertices, so unused
-- sequence cells can remain unconstrained. Cutting edges preserves either form.




-- A source-facing description of the cascade's exact heap changes. It records
-- actual cuts and marks, independently of the compiler's temporary states.
inductive CascadeEffect (queue : Ref_FibonacciHeap) :
    Heap → Layout → Int → Heap → Layout → Nat → Prop where
  | root (heap : Heap) (layout : Layout) (vertex : Int)
      (root : heap.read layout.parents vertex < 0) :
      CascadeEffect queue heap layout vertex heap layout 0
  | mark (heap : Heap) (layout : Layout) (vertex : Int)
      (nonroot : 0 ≤ heap.read layout.parents vertex) (unmarked : heap.read layout.marks vertex = 0) :
      CascadeEffect queue heap layout vertex (heap.write layout.marks vertex 1) layout 0
  | cut {heap after : Heap} {layout finalLayout : Layout} {vertex : Int} {cuts : Nat}
      (nonroot : 0 ≤ heap.read layout.parents vertex) (marked : heap.read layout.marks vertex ≠ 0)
      (rest : CascadeEffect queue
        (cutHeap heap queue layout vertex (heap.read layout.parents vertex))
        (cutLayout heap layout vertex (heap.read layout.parents vertex))
        (heap.read layout.parents vertex) after finalLayout cuts) :
      CascadeEffect queue heap layout vertex after finalLayout (cuts + 1)





-- This is a terminating compiled execution, derived from decreasing parents;
-- it does not ask the caller to supply a transcript or a cascade result.


/-- Ordinary field observations; this description is independent of execution. -/
def snapshot (heap : Heap) (layout : Layout) : Algo2Lean.Fibonacci.Snapshot :=
  ⟨heap.read layout.keys, heap.read layout.parents, heap.read layout.children,
    heap.read layout.left, heap.read layout.right, heap.read layout.degrees,
    heap.read layout.marks, heap.read layout.present, heap.read layout.table,
    layout.minimum, layout.size⟩

/-- The queue's concrete storage realizes a finite, ordered Fibonacci forest. -/
structure QueueRep (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (forest : Algo2Lean.Fibonacci.Forest) : Prop where
  layoutValid : layout.Valid heap queue
  represented : Algo2Lean.Fibonacci.Represented (snapshot heap layout) forest










end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis





end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis







/-- Initialize the inserted vertex and increment the public size before root insertion. -/
def insertionHeaderHeap (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex key : Int) : Heap :=
  set_FibonacciHeap_size
    (((((heap.tick "heap_operations").write layout.keys vertex key).write
      layout.children vertex (-1)).write layout.degrees vertex 0).write
      layout.present vertex 1) queue (layout.size + 1)

def insertionHeap (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex key : Int) : Heap :=
  addRootHeap (insertionHeaderHeap heap queue layout vertex key) queue
    { layout with size := layout.size + 1 } vertex

def insertionLayout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex key : Int) : Layout :=
  addRootLayout (insertionHeaderHeap heap queue layout vertex key)
    { layout with size := layout.size + 1 } vertex



































end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis

/-- Unlink the next child from its parent's child header before promoting it. -/
def promotionHeaderHeap (heap : Heap) (layout : Layout) (vertex : Int) : Heap :=
  let child := heap.read layout.children vertex
  if heap.read layout.right child = child then heap.write layout.children vertex (-1)
  else heap.write layout.children vertex (heap.read layout.right child)

def promotionDetachedHeap (heap : Heap) (layout : Layout) (vertex : Int) : Heap :=
  let child := heap.read layout.children vertex
  let headed := promotionHeaderHeap heap layout vertex
  removeHeap (headed.write layout.degrees vertex (headed.read layout.degrees vertex - 1))
    layout child

def promotionHeap (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex : Int) : Heap :=
  (addRootHeap (promotionDetachedHeap heap layout vertex) queue layout
    (heap.read layout.children vertex)).tick "heap_promotions"

def promotionLayout (heap : Heap) (layout : Layout) (vertex : Int) : Layout :=
  addRootLayout (promotionDetachedHeap heap layout vertex) layout
    (heap.read layout.children vertex)







/-- The child-promotion loop's finite operational effect. Existence is proved
    separately from a finite child-ring invariant; no transcript is an input. -/
inductive PromotionEffect (queue : Ref_FibonacciHeap) (vertex : Int) :
    Heap → Layout → Heap → Layout → Nat → Prop where
  | done (heap : Heap) (layout : Layout)
      (childless : heap.read layout.children vertex < 0) :
      PromotionEffect queue vertex heap layout heap layout 0
  | next {heap after : Heap} {layout finalLayout : Layout} {count : Nat}
      (hasChild : 0 ≤ heap.read layout.children vertex)
      (rest : PromotionEffect queue vertex (promotionHeap heap queue layout vertex)
        (promotionLayout heap layout vertex) after finalLayout count) :
      PromotionEffect queue vertex heap layout after finalLayout (count + 1)



/-- Remove the selected root, clear membership, and decrement size. -/
def extractionHeap (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex : Int) : Heap :=
  set_FibonacciHeap_size ((removeHeap heap layout vertex).write layout.present vertex 0)
    queue (layout.size - 1)

def extractionLayout (layout : Layout) : Layout := { layout with size := layout.size - 1 }



/-- A nonempty remainder calls the independently verified consolidation method.
    The constructor records that precise call contract, not a pop-min correctness claim. -/
inductive ExtractionEffect (queue : Ref_FibonacciHeap) (vertex : Int)
    (heap : Heap) (layout : Layout) : Heap → Layout → Prop where
  | last (onlyRoot : heap.read layout.right vertex = vertex) :
      ExtractionEffect queue vertex heap layout
        (set_FibonacciHeap_minimum (extractionHeap heap queue layout vertex) queue (-1))
        { extractionLayout layout with minimum := -1 }
  | consolidate {after : Heap} {finalLayout : Layout}
      (moreRoots : heap.read layout.right vertex ≠ vertex)
      (call : FibonacciHeap.consolidate.Call
        (set_FibonacciHeap_minimum (extractionHeap heap queue layout vertex)
          queue (heap.read layout.right vertex)) queue after ())
      (resultLayout : finalLayout.Valid after queue) :
      ExtractionEffect queue vertex heap layout after finalLayout



/-- Operational pop-min effects: inspect the minimum, promote children, remove it,
    and, when required, reuse one separate consolidation call. -/
inductive PopEffect (queue : Ref_FibonacciHeap) (heap : Heap) (layout : Layout) :
    Heap → Layout → Int → Nat → Prop where
  | empty (empty : layout.minimum < 0) :
      PopEffect queue heap layout (heap.tick "heap_operations") layout (-1) 0
  | nonempty {promoted after : Heap} {promotedLayout finalLayout : Layout} {count : Nat}
      (nonempty : 0 ≤ layout.minimum)
      (promote : PromotionEffect queue layout.minimum (heap.tick "heap_operations")
        layout promoted promotedLayout count)
      (extract : ExtractionEffect queue layout.minimum promoted promotedLayout after finalLayout) :
      PopEffect queue heap layout after finalLayout layout.minimum count





def lowerKeyHeap (heap : Heap) (layout : Layout) (vertex key : Int) : Heap :=
  ((heap.tick "heap_operations").tick "heap_comparisons").write layout.keys vertex key

def finishDecreaseHeap (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex : Int) : Heap :=
  let compared := heap.tick "heap_comparisons"
  if heap.read layout.keys vertex < heap.read layout.keys layout.minimum then
    set_FibonacciHeap_minimum compared queue vertex
  else compared

def finishDecreaseLayout (heap : Heap) (layout : Layout) (vertex : Int) : Layout :=
  if heap.read layout.keys vertex < heap.read layout.keys layout.minimum then
    { layout with minimum := vertex }
  else layout









-- The three decrease cases record exact heap effects and reuse a cascade's
-- contract. The initial key update is kept separate from its tree repairs.
inductive DecreaseEffect (queue : Ref_FibonacciHeap) (vertex key : Int) :
    Heap → Layout → Heap → Layout → Nat → Prop where
  | root (heap : Heap) (layout : Layout) (root : heap.read layout.parents vertex < 0) :
      DecreaseEffect queue vertex key heap layout
        (finishDecreaseHeap heap queue layout vertex) (finishDecreaseLayout heap layout vertex) 0
  | ordered (heap : Heap) (layout : Layout) (nonroot : 0 ≤ heap.read layout.parents vertex)
      (ordered : heap.read layout.keys (heap.read layout.parents vertex) ≤ key) :
      DecreaseEffect queue vertex key heap layout
        (finishDecreaseHeap (heap.tick "heap_comparisons") queue layout vertex)
        (finishDecreaseLayout (heap.tick "heap_comparisons") layout vertex) 0
  | cut {heap after : Heap} {layout finalLayout : Layout} {cuts : Nat}
      (nonroot : 0 ≤ heap.read layout.parents vertex)
      (unordered : key < heap.read layout.keys (heap.read layout.parents vertex))
      (rest : CascadeEffect queue
        (cutHeap (heap.tick "heap_comparisons") queue layout vertex (heap.read layout.parents vertex))
        (cutLayout (heap.tick "heap_comparisons") layout vertex (heap.read layout.parents vertex))
        (heap.read layout.parents vertex) after finalLayout cuts) :
      DecreaseEffect queue vertex key heap layout
        (finishDecreaseHeap after queue finalLayout vertex)
        (finishDecreaseLayout after finalLayout vertex) (cuts + 1)


















@[simp] theorem add_root_layout_refs (heap : Heap) (layout : Layout) (vertex : Int) :
    (addRootLayout heap layout vertex).refs = layout.refs := by
  unfold addRootLayout
  split
  · rfl
  · dsimp only
    split <;> rfl

@[simp] theorem cut_layout_refs (heap : Heap) (layout : Layout) (vertex parent : Int) :
    (cutLayout heap layout vertex parent).refs = layout.refs := by simp [cutLayout]







@[simp] theorem finish_decrease_layout_refs (heap : Heap) (layout : Layout) (vertex : Int) :
    (finishDecreaseLayout heap layout vertex).refs = layout.refs := by
  unfold finishDecreaseLayout
  split <;> rfl


























end FibonacciModuleAnalysis


namespace FibonacciModuleAnalysis

@[simp] theorem promotion_layout_refs (heap : Heap) (layout : Layout) (vertex : Int) :
    (promotionLayout heap layout vertex).refs = layout.refs := by
  exact add_root_layout_refs _ _ _



























end FibonacciModuleAnalysis


namespace FibonacciModuleAnalysis

open Algo2Lean.Fibonacci.Rings











@[simp] theorem promotion_layout_left (heap : Heap) (layout : Layout) (vertex : Int) :
    (promotionLayout heap layout vertex).left = layout.left := by
  unfold promotionLayout addRootLayout
  split
  · rfl
  · dsimp only
    split <;> rfl

@[simp] theorem promotion_layout_right (heap : Heap) (layout : Layout) (vertex : Int) :
    (promotionLayout heap layout vertex).right = layout.right := by
  unfold promotionLayout addRootLayout
  split
  · rfl
  · dsimp only
    split <;> rfl

@[simp] theorem promotion_layout_children (heap : Heap) (layout : Layout) (vertex : Int) :
    (promotionLayout heap layout vertex).children = layout.children := by
  unfold promotionLayout addRootLayout
  split
  · rfl
  · dsimp only
    split <;> rfl



















end FibonacciModuleAnalysis


namespace FibonacciModuleAnalysis

/-- One degree-table visit clears its bucket before reconnecting its root. -/
def rebuildClear (heap : Heap) (layout : Layout) (degree : Int) : Heap :=
  (heap.tick "heap_degree_scans").write layout.table degree (-1)

def rebuildHeap (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout) (degree : Int) : Heap :=
  let cleared := rebuildClear heap layout degree
  let vertex := heap.read layout.table degree
  if vertex < 0 then cleared else addRootHeap cleared queue layout vertex

def rebuildLayout (heap : Heap) (layout : Layout) (degree : Int) : Layout :=
  if heap.read layout.table degree < 0 then layout
  else addRootLayout (rebuildClear heap layout degree) layout (heap.read layout.table degree)



/-- A finite interval of degree buckets, with the exact mutation at each visit. -/
inductive RebuildEffect (queue : Ref_FibonacciHeap) (maximum : Int) :
    Heap → Layout → Int → Heap → Layout → Prop where
  | done (heap : Heap) (layout : Layout) (degree : Int) (finished : maximum < degree) :
      RebuildEffect queue maximum heap layout degree heap layout
  | step {heap after : Heap} {layout finalLayout : Layout} {degree : Int}
      (remaining : degree ≤ maximum)
      (rest : RebuildEffect queue maximum (rebuildHeap heap queue layout degree)
        (rebuildLayout heap layout degree) (degree + 1) after finalLayout) :
      RebuildEffect queue maximum heap layout degree after finalLayout





/-- Clear the colliding bucket before comparing and linking its two roots. -/
def collisionStart (heap : Heap) (layout : Layout) (degree : Int) : Heap :=
  (heap.write layout.table degree (-1)).tick "heap_comparisons"

def collisionParent (heap : Heap) (layout : Layout) (vertex degree : Int) : Int :=
  let ready := collisionStart heap layout degree
  let other := heap.read layout.table degree
  if ready.read layout.keys other < ready.read layout.keys vertex then other else vertex

def collisionChild (heap : Heap) (layout : Layout) (vertex degree : Int) : Int :=
  let ready := collisionStart heap layout degree
  let other := heap.read layout.table degree
  if ready.read layout.keys other < ready.read layout.keys vertex then vertex else other

def collisionHeap (heap : Heap) (layout : Layout) (vertex degree : Int) : Heap :=
  linkHeap (collisionStart heap layout degree) layout (collisionChild heap layout vertex degree)
    (collisionParent heap layout vertex degree)



/-- One equal-degree collision per link; the final bucket is empty. -/
inductive CollisionEffect (layout : Layout) : Heap → Int → Int → Heap → Int → Int → Nat → Prop where
  | done (heap : Heap) (vertex degree : Int) (empty : heap.read layout.table degree < 0) :
      CollisionEffect layout heap vertex degree heap vertex degree 0
  | step {heap after : Heap} {vertex degree finalVertex finalDegree : Int} {links : Nat}
      (occupied : 0 ≤ heap.read layout.table degree)
      (rest : CollisionEffect layout (collisionHeap heap layout vertex degree)
        (collisionParent heap layout vertex degree) (degree + 1) after finalVertex finalDegree links) :
      CollisionEffect layout heap vertex degree after finalVertex finalDegree (links + 1)











/-- Detach the next pending root before looking it up in the degree table. -/
def pendingMinimum (heap : Heap) (layout : Layout) : Int :=
  if heap.read layout.right layout.minimum = layout.minimum then -1
  else heap.read layout.right layout.minimum

def detachLayout (heap : Heap) (layout : Layout) : Layout :=
  {layout with minimum := pendingMinimum heap layout}

def detachHeap (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout) : Heap :=
  (removeHeap (set_FibonacciHeap_minimum heap queue (pendingMinimum heap layout)) layout
    layout.minimum).tick "heap_root_scans"





/-- Pending roots are consumed once; each detached root resolves collisions,
    then stores its surviving tree in the now-empty degree bucket. -/
inductive ConsumeEffect (queue : Ref_FibonacciHeap) :
    Heap → Layout → Int → Heap → Layout → Nat → Nat → Prop where
  | done {heap after : Heap} {layout finalLayout : Layout} {maximum : Int}
      (empty : layout.minimum < 0)
      (rebuild : RebuildEffect queue maximum heap layout 0 after finalLayout) :
      ConsumeEffect queue heap layout maximum after finalLayout 0 0
  | next {heap merged after : Heap} {layout finalLayout : Layout}
      {maximum vertex degree : Int} {links tailRoots tailLinks : Nat}
      (pending : 0 ≤ layout.minimum)
      (collisions : CollisionEffect (detachLayout heap layout)
        (detachHeap heap queue layout) layout.minimum
        ((detachHeap heap queue layout).read layout.degrees layout.minimum)
        merged vertex degree links)
      (rest : ConsumeEffect queue (merged.write layout.table degree vertex)
        (detachLayout heap layout) (max maximum degree) after finalLayout tailRoots tailLinks) :
      ConsumeEffect queue heap layout maximum after finalLayout (tailRoots + 1) (links + tailLinks)

































/-- The event model counts each explicitly instrumented primitive category once. -/
def heapEventWork (before after : Heap) : Nat :=
  let cost := Heap.cost before after
  cost "heap_operations" + cost "heap_comparisons" + cost "heap_links" +
    cost "heap_cuts" + cost "heap_root_scans" + cost "heap_degree_scans" + cost "heap_promotions"

















@[simp] theorem snapshot_tick (heap : Heap) (layout : Layout) (clock : String) (amount : Nat) :
    snapshot (heap.tick clock amount) layout = snapshot heap layout := rfl















end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis






















end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis













@[simp] theorem rebuild_layout_refs (heap : Heap) (layout : Layout) (degree : Int) :
    (rebuildLayout heap layout degree).refs = layout.refs := by
  unfold rebuildLayout
  split
  · rfl
  · exact add_root_layout_refs _ _ _







end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis
open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap Algo.fibonacci_heap.Algo2LeanGenerated















end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis
open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap Algo.fibonacci_heap.Algo2LeanGenerated













end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis
open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap Algo.fibonacci_heap.Algo2LeanGenerated

/-- The complete set of clocks owned by the heap implementation. -/
def heapClocks : List String :=
  ["heap_operations", "heap_comparisons", "heap_links", "heap_cuts",
    "heap_root_scans", "heap_degree_scans", "heap_promotions"]

/-- Client bookkeeping clocks survive every queue call unchanged. -/
def PreservesOtherClocks (before after : Heap) : Prop :=
  ∀ clock, clock ∉ heapClocks → after.clocks clock = before.clocks clock



/-- A public update contract records the call, its local footprint, and its exact
    operation/cut/comparison cost. The forest proof supplies the snapshot. -/
structure UpdateContract (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (vertex key : Int) (cuts : Nat) : Prop where
  summary : FibonacciHeap.push_or_decrease.Call heap (queue, vertex, key) after ()
  valid : finalLayout.Valid after queue
  frame : heap.Modifies after layout.refs [queue]
  refs : finalLayout.refs = layout.refs
  clocks : ∃ comparisons, comparisons ≤ cuts + 3 ∧ ∀ clock,
    after.clocks clock = heap.clocks clock + Clocks.single "heap_operations" 1 clock +
      Clocks.single "heap_cuts" cuts clock + Clocks.single "heap_comparisons" comparisons clock













end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis
open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap Algo.fibonacci_heap.Algo2LeanGenerated









end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis





/-- Source effects after promotion, before the optional consolidation call. -/
def removeMinimumHeap (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout) (vertex : Int) : Heap :=
  set_FibonacciHeap_minimum (extractionHeap heap queue layout vertex) queue
    (if heap.read layout.right vertex = vertex then -1 else heap.read layout.right vertex)

def removeMinimumLayout (heap : Heap) (layout : Layout) (vertex : Int) : Layout :=
  {extractionLayout layout with minimum := if heap.read layout.right vertex = vertex then -1 else heap.read layout.right vertex}















/-- Public delete-min contract: exact entries, isolated mutation, and the
    amortized cost of the actual compiled call. -/
structure PopContract (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (forest : Algo2Lean.Fibonacci.Forest) (after : Heap) (finalLayout : Layout)
    (afterForest : Algo2Lean.Fibonacci.Forest) : Prop where
  execution : FibonacciHeap.pop_min.Call heap queue after layout.minimum
  represented : QueueRep after queue finalLayout afterForest
  contents : ((layout.minimum, heap.read layout.keys layout.minimum) :: afterForest.entries).Perm forest.entries
  frame : heap.Modifies after layout.refs [queue]
  refs : finalLayout.refs = layout.refs
  otherClocks : PreservesOtherClocks heap after
  amortized : heapEventWork heap after + Algo2Lean.Fibonacci.scaledPotential afterForest.counts ≤
    Algo2Lean.Fibonacci.scaledPotential forest.counts + 12 * (2 * forest.entries.length.log2 + 2)



end FibonacciModuleAnalysis


