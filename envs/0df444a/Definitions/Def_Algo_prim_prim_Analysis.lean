-- Prove2me | Definitions.Def_Algo_prim_prim_Analysis
-- name    : Algo_prim_prim_Analysis
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-11T01:12:47.612546+00:00
-- url     : https://prove2.me/theorems/ad1ab4ec-58a0-4917-a3f9-e4fb96461ffb
-- title:
--   Algo.prim.prim.Analysis definitions
-- statement:
--   Definitions and required structural lemmas from `Algo.prim.prim.Analysis`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/d832a5655d7cac6d032e728a4798128147b27922/examples/analysis/prim/prim.lean

import Definitions.Def_Algo_prim_scan_Analysis
import Definitions.Def_Algo_prim_invariant_Analysis

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Prim's algorithm with an abstract mutable priority queue. The proof connects
local source transitions, the cut-property invariant, and amortized operation
contracts. The Fibonacci instantiation reuses this analysis unchanged. -/
namespace PrimAnalysis
open Algo2LeanCore Algo2LeanGenerated Algo2Lean.Dijkstra
open Algo2Lean.Prim
open Algo.prim.graph.Algo2LeanGenerated
open Algo.prim.prim Algo.dijkstra.priority_queue
open PriorityQueueAnalysis PrimGraph PrimControl

/-- Predecessors describe a minimum spanning tree on the declared vertex range. -/
abbrev MinimumSpanningParents (size : Int) (adjacency : Adjacency) (root : Int) (parent : Seq) : Prop :=
  SpanningParents size.toNat (inputEdges size adjacency) root parent

variable {dependencies : Dependencies} {client : Client}
variable (model : Model dependencies.PriorityQueue client.queue client.protection)

structure LoopInvariant (state : QueueState model) (remaining : List Int) : Prop where
  storage : Storage model state
  matching : QueueMatches model state
  rootRange : 0 ≤ client.root ∧ client.root < client.size
  unique : remaining.Nodup
  members : ∀ vertex, vertex ∈ remaining ↔
    0 ≤ vertex ∧ vertex < client.size ∧ state.heap.read client.selected vertex = 0
  mathematical : ∃ chosen, Algo2Lean.Prim.Invariant (inputEdges client.size client.adjacency) client.root
    (fun vertex => state.heap.read client.selected vertex ≠ 0)
    (state.heap.read client.key) (state.heap.read client.parent) chosen

/-- A successful extraction consumes one remaining vertex and exactly its list. -/
structure Iteration (before after : QueueState model) (remaining : List Int) (vertex : Int) : Prop where
  member : vertex ∈ remaining
  invariant : LoopInvariant model after (remaining.erase vertex)
  costs : CostBounds model before after 1 (client.adjacency vertex).length
  execution : ∀ finalHeap,
    ExtractLoop dependencies after.heap client.graph client.queue client.key client.parent client.selected finalHeap →
    ExtractLoop dependencies before.heap client.graph client.queue client.key client.parent client.selected finalHeap

variable (contracts : Contracts model reservedClocks)
include contracts



/-- A finished loop retains the mathematical invariant and accumulated cost. -/
structure Completed (before after : QueueState model) (remaining : List Int) : Prop where
  invariant : ∃ pending, LoopInvariant model after pending
  empty : after.entries model = []
  costs : CostBounds model before after remaining.length (edgeBudget client.adjacency remaining)
  execution : ExtractLoop dependencies before.heap client.graph client.queue client.key client.parent client.selected
    (after.heap.tick "queue_empty_checks")



/-- Counts of actual source ticks, measured relative to arbitrary initial clocks. -/
structure OperationCounts (before after : Heap) (vertices edges : Nat) : Prop where
  updates : Heap.cost before after "queue_updates" ≤ edges + 1
  pops : Heap.cost before after "queue_pops" ≤ vertices
  checks : Heap.cost before after "queue_empty_checks" ≤ vertices + 1
  visits : Heap.cost before after "edges" ≤ edges
  improvements : Heap.cost before after "improvements" ≤ edges
  settlements : Heap.cost before after "settlements" ≤ vertices



end PrimAnalysis


