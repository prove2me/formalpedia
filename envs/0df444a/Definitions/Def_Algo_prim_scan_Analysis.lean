-- Prove2me | Definitions.Def_Algo_prim_scan_Analysis
-- name    : Algo_prim_scan_Analysis
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-11T01:11:36.768659+00:00
-- url     : https://prove2.me/theorems/128f2b6d-1917-498b-91be-af357ba6336f
-- title:
--   Algo.prim.scan.Analysis definitions
-- statement:
--   Definitions and required structural lemmas from `Algo.prim.scan.Analysis`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/d832a5655d7cac6d032e728a4798128147b27922/examples/analysis/prim/scan.lean

import Definitions.Def_Algo_prim_support_Analysis
import Definitions.Def_Algo_prim_math_Analysis

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Prim's adjacency scan preserves queue contents, parent pointers, and keys.
Every queue update uses only the imported operation contract. -/
namespace PrimAnalysis
open Algo2LeanCore Algo2LeanGenerated Algo2Lean.Dijkstra
open Algo2Lean.Prim
open Algo.prim.graph.Algo2LeanGenerated
open Algo.prim.prim Algo.dijkstra.priority_queue
open PriorityQueueAnalysis PrimGraph PrimControl

variable {dependencies : Dependencies} {client : Client}
variable (model : Model dependencies.PriorityQueue client.queue client.protection)
variable (contracts : Contracts model reservedClocks)
include contracts

structure EdgeAdvanced (before after : QueueState model)
    (vertex target weight : Int) (edge : Ref_Edge) (next : Option Ref_Edge) : Prop where
  storage : Storage model after
  matching : QueueMatches model after
  selected : after.heap.read client.selected = before.heap.read client.selected
  scan : KeyScan (fun v => before.heap.read client.selected v ≠ 0) vertex
    [(target,weight)] (before.heap.read client.key) (before.heap.read client.parent)
    (after.heap.read client.key) (after.heap.read client.parent)
  costs : CostBounds model before after 0 1
  frame : GraphFrame before.heap after.heap client.graph client.heads
  execution : ∀ finalHeap,
    ScanLoop dependencies after.heap client.queue client.key client.parent client.selected vertex next finalHeap →
    ScanLoop dependencies before.heap client.queue client.key client.parent client.selected vertex (some edge) finalHeap

structure AdjacencyScanned (before after : QueueState model)
    (vertex : Int) (head : Option Ref_Edge) (edges : List (Int × Int)) : Prop where
  storage : Storage model after
  matching : QueueMatches model after
  selected : after.heap.read client.selected = before.heap.read client.selected
  scan : KeyScan (fun v => before.heap.read client.selected v ≠ 0) vertex edges
    (before.heap.read client.key) (before.heap.read client.parent)
    (after.heap.read client.key) (after.heap.read client.parent)
  costs : CostBounds model before after 0 edges.length
  frame : GraphFrame before.heap after.heap client.graph client.heads
  execution : ScanLoop dependencies before.heap client.queue client.key client.parent client.selected vertex head after.heap





end PrimAnalysis


