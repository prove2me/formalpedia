-- Prove2me | Definitions.Def_Algo_kruskal_scan_Analysis
-- name    : Algo_kruskal_scan_Analysis
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:52:37.44729+00:00
-- url     : https://prove2.me/theorems/ed5739f6-3515-4af7-ab39-919f6f69d0d2
-- title:
--   Kruskal scan invariant, selection flags and local work
-- statement:
--   `ScanLayout` names the union-find object and endpoint, order and chosen arrays. `ScanInvariant` connects their allocated storage and alias-separation requirements to the pending/selected edge lists and the current partition model. `Order` relates the pending identifiers to their stored order prefix. `Flags values selected` says, for every integer index, that the flag is one exactly when a selected edge has that identifier, and zero otherwise.
--
--   The local `work` function sums `uf_init`, `uf_find`, `uf_compress`, `uf_union` and `kruskal`. `initialHeap` and `initialLayout` describe the singleton structure and zero flags used to start the scan. The separate `scan_contract` theorem carries the same represented model and potential through every call, allowing the union-find cost terms to telescope.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/kruskal/analysis/kruskal_scan.lean

import Definitions.Def_Algo_kruskal_Generated
import Definitions.Def_Algo_kruskal_Facts
import Definitions.Def_Algo_kruskal_Points
import Definitions.Def_Algo_union_find_init_Analysis
import Definitions.Def_Algo2LeanLib_KruskalMath
import Definitions.Def_Algo2LeanLib_Footprint

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Kruskal initializes singleton components, sorts edge identifiers, and compares
representatives before selecting an edge and applying the verified union.
The graph argument is independent of the storage and transition machinery.
-/

namespace KruskalAnalysis

open Algo2LeanCore Algo2LeanGenerated
open Algo.kruskal Algo.kruskal.Algo2LeanGenerated
open UnionFindAnalysis
open Algo2Lean.Kruskal

/-- An accepted edge is marked; a rejected edge leaves the flags unchanged. -/
def selectHeap (heap : Heap) (chosen : SeqRef) (edge : Int) (accepted : Bool) : Heap :=
  if accepted then heap.write chosen edge 1 else heap

/-- The four client arrays and the separately represented union-find object. -/
structure ScanLayout where
  sets : UnionFindAnalysis.Layout
  sources : SeqRef
  targets : SeqRef
  order : SeqRef
  chosen : SeqRef

/-- A flag array records exactly the selected edge identifiers. -/
def Flags (values : Seq) (selected : List Edge) : Prop :=
  ∀ id : Int, values id = (if selected.any (fun edge => (edge.id : Int) == id) then 1 else 0)

/-- The unprocessed suffix of the identifier array. -/
inductive Order (heap : Heap) (ref : SeqRef) : Int → List Edge → Prop where
  | nil (index : Int) : Order heap ref index []
  | cons {index : Int} {edge : Edge} {rest : List Edge}
      (head : heap.read ref index = (edge.id : Int))
      (tail : Order heap ref (index + 1) rest) : Order heap ref index (edge :: rest)

/-- Storage, graph connectivity, and output flags agree at a scan boundary. -/
structure ScanInvariant (n : Nat) (data : ScanLayout) (heap : Heap)
    (model : Algo2Lean.UnionFind.State n) (index : Int) (pending selected : List Edge) : Prop where
  representation : Rep heap data.sets model
  partition : ∀ u v : Fin n, Algo2Lean.UnionFind.Connected model u v ↔
    Connected selected (u.val : Int) (v.val : Int)
  bounded : ∀ edge ∈ pending,
    (0 ≤ edge.source ∧ edge.source < (n : Int)) ∧ (0 ≤ edge.target ∧ edge.target < (n : Int))
  sources : ∀ edge ∈ pending, heap.read data.sources edge.id = edge.source
  targets : ∀ edge ∈ pending, heap.read data.targets edge.id = edge.target
  ordered : Order heap data.order index pending
  flags : Flags (heap.read data.chosen) selected
  sourceAllocated : data.sources < heap.nextRef
  targetAllocated : data.targets < heap.nextRef
  orderAllocated : data.order < heap.nextRef
  chosenAllocated : data.chosen < heap.nextRef
  sourceProtected : data.sources ∉ [data.sets.parent, data.sets.rank, data.chosen]
  targetProtected : data.targets ∉ [data.sets.parent, data.sets.rank, data.chosen]
  orderProtected : data.order ∉ [data.sets.parent, data.sets.rank, data.chosen]
  chosenProtected : data.chosen ∉ [data.sets.parent, data.sets.rank]

/-- Work performed by the scan and its union-find calls. Sorting is accounted
    for separately by its reusable sorting contract. -/
def work (clocks : Clocks) : Nat := UnionFindAnalysis.work clocks + clocks "kruskal"












/-- Source-facing values needed at the edge-loop boundary. -/
structure ScanLocals (data : ScanLayout) (index count : Int) (state : Configuration) : Prop where
  location : kruskal.At.scan state
  sets : kruskal.Local.sets state = some data.sets.object
  sources : kruskal.Local.sources state = some data.sources
  targets : kruskal.Local.targets state = some data.targets
  order : kruskal.Local.order state = some data.order
  chosen : kruskal.Local.chosen state = some data.chosen
  index : kruskal.Local.index state = some index
  count : kruskal.Local.count state = some count

/-- Complete the edge loop from any configuration with these local values.
    The caller's stack and irrelevant temporary variables remain unrestricted. -/
def ScanCall (data : ScanLayout) (heap : Heap) (index count : Int) (final : Heap) : Prop :=
  ∀ state, ScanLocals data index count state → state.heap = heap →
    kruskal.CallFrom state final data.chosen



/-- Two representative lookups precede the conditional selection and union.
    The union result is intentionally ignored, as in textbook MST-KRUSKAL. -/
def EdgeCalls (data : ScanLayout) (heap final : Heap) (edge a b : Int) : Prop :=
  ∃ first second left right,
    Algo.union_find.UnionFind.find.Call (heap.tick "kruskal") (data.sets.object, a) first left ∧
    Algo.union_find.UnionFind.find.Call first (data.sets.object, b) second right ∧
    (if left ≠ right then ∃ result,
      Algo.union_find.UnionFind.union.Call (second.write data.chosen edge 1)
        (data.sets.object, a, b) final result else final = second) ∧
    data.chosen < second.nextRef
















/-- The empty edge set is allocated before initializing singleton components. -/
def initialHeap (heap : Heap) (size : Nat) : Heap :=
  newHeap (heap.allocate (fun _ => 0)) size

/-- The result and disjoint-set arrays precede the freshly sorted edge order. -/
def initialLayout (heap : Heap) (_size : Nat) (sources targets order : SeqRef) : ScanLayout :=
  ⟨newLayout (heap.allocate (fun _ => 0)), sources, targets, order, heap.nextRef⟩











end KruskalAnalysis


