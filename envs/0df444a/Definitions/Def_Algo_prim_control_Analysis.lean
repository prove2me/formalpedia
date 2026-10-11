-- Prove2me | Definitions.Def_Algo_prim_control_Analysis
-- name    : Algo_prim_control_Analysis
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-11T01:10:18.786313+00:00
-- url     : https://prove2.me/theorems/94000f31-dfe3-48af-a883-fb5d5eae2f24
-- title:
--   Algo.prim.control.Analysis definitions
-- statement:
--   Definitions and required structural lemmas from `Algo.prim.control.Analysis`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/d832a5655d7cac6d032e728a4798128147b27922/examples/analysis/prim/control.lean

import Definitions.Def_Algo_prim_prim_Generated
import Definitions.Def_Algo_prim_prim_Points
import Definitions.Def_Algo_prim_prim_Facts

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Local execution rules for Prim's two loops. Each lemma describes public
    named locations and source variables. Queue calls are supplied as contracts;
    their representation and balancing details do not enter these proofs. -/

namespace PrimControl

open Algo2LeanCore Algo2LeanGenerated
open Algo.prim.graph.Algo2LeanGenerated
open Algo.prim.prim
open Algo.dijkstra.priority_queue

@[simp] theorem edge_target_tick (heap : Heap) (clock : String) (amount : Nat) (edge : Ref_Edge) :
    field_Edge_target (heap.tick clock amount) edge = field_Edge_target heap edge := rfl
@[simp] theorem edge_weight_tick (heap : Heap) (clock : String) (amount : Nat) (edge : Ref_Edge) :
    field_Edge_weight (heap.tick clock amount) edge = field_Edge_weight heap edge := rfl
@[simp] theorem edge_next_tick (heap : Heap) (clock : String) (amount : Nat) (edge : Ref_Edge) :
    field_Edge_next (heap.tick clock amount) edge = field_Edge_next heap edge := rfl

variable (dependencies : Dependencies)

/-- The adjacency loop is described by its named source location and live variables.
    Temporary values from earlier iterations impose no obligations on the caller. -/
def AtScan (state : Algo.prim.prim.Algo2LeanGenerated.Configuration dependencies)
    (heap : Heap) (queue : ObjectRef) (key parent selected : SeqRef)
    (vertex : Int) (edge : Option Ref_Edge) : Prop :=
  scan_edges.At.scan dependencies state ∧ state.heap = heap ∧
  scan_edges.Local.queue dependencies state = some queue ∧
  scan_edges.Local.key dependencies state = some key ∧
  scan_edges.Local.parent dependencies state = some parent ∧
  scan_edges.Local.selected dependencies state = some selected ∧
  scan_edges.Local.vertex dependencies state = some vertex ∧
  scan_edges.Local.edge dependencies state = some edge

/-- Finish the adjacency loop from any local state with these source variables. -/
def ScanLoop (heap : Heap) (queue : ObjectRef) (key parent selected : SeqRef)
    (vertex : Int) (edge : Option Ref_Edge) (finalHeap : Heap) : Prop :=
  ∀ state, AtScan dependencies state heap queue key parent selected vertex edge →
    scan_edges.CallFrom dependencies state finalHeap ()

/-- The main loop needs only the graph, queue, and three client sequences. The
    initialized root and previous iteration's temporary values are irrelevant. -/
def AtExtract (state : Algo.prim.prim.Algo2LeanGenerated.Configuration dependencies)
    (heap : Heap) (graph : Ref_Graph) (queue : ObjectRef) (key parent selected : SeqRef) : Prop :=
  prim.At.extract dependencies state ∧ state.heap = heap ∧
  prim.Local.graph dependencies state = some graph ∧
  prim.Local.queue dependencies state = some queue ∧
  prim.Local.key dependencies state = some key ∧
  prim.Local.parent dependencies state = some parent ∧
  prim.Local.selected dependencies state = some selected

/-- Finish the main loop after counting its next emptiness test. This local
    continuation is independent of the code that initialized the search. -/
def ExtractLoop (heap : Heap) (graph : Ref_Graph) (queue : ObjectRef)
    (key parent selected : SeqRef) (finalHeap : Heap) : Prop :=
  ∀ state, AtExtract dependencies state (heap.tick "queue_empty_checks") graph queue key parent selected →
    prim.CallFrom dependencies state finalHeap parent


















end PrimControl


