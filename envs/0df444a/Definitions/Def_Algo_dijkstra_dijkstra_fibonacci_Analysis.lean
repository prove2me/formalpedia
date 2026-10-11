-- Prove2me | Definitions.Def_Algo_dijkstra_dijkstra_fibonacci_Analysis
-- name    : Algo_dijkstra_dijkstra_fibonacci_Analysis
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:53:20.807978+00:00
-- url     : https://prove2.me/theorems/656b1bf5-87e3-4773-b1b7-76e50818153c
-- title:
--   Algo.dijkstra.dijkstra_fibonacci.Analysis definitions
-- statement:
--   Definitions and required structural lemmas from `Algo.dijkstra.dijkstra_fibonacci.Analysis`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/analysis/dijkstra/dijkstra_fibonacci.lean

import Definitions.Def_Algo_dijkstra_dijkstra_fibonacci_Generated
import Definitions.Def_Algo_dijkstra_dijkstra_fibonacci_Facts
import Definitions.Def_Algo_dijkstra_dijkstra_Analysis
import Definitions.Def_Algo_dijkstra_support_fibonacci_queue_Analysis

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! The concrete wrapper constructs a queue and client arrays, then applies the
    unchanged generic Dijkstra theorem and the independent queue contract. -/

namespace FibonacciDijkstraAnalysis

open Algo2LeanCore Algo2LeanGenerated Algo2Lean.Dijkstra
open Algo.graph.Algo2LeanGenerated
open Algo.dijkstra.dijkstra_fibonacci
open ComposableDijkstraAnalysis

/-- Generated binding theorems connect independently compiled source methods. -/
def bridge : FibonacciQueueAnalysis.Bridge FibonacciHeap_as_PriorityQueue where
  valid := by intro heap ref; simp [FibonacciHeap_as_PriorityQueue]
  is_empty := FibonacciHeap_as_PriorityQueue_summary_is_empty
  update := FibonacciHeap_as_PriorityQueue_summary_push_or_decrease
  extract := FibonacciHeap_as_PriorityQueue_summary_pop_min





/-- Every explicit backend and client counter occurs once in this metric. -/
def clockWork (costs : Clocks) : Nat :=
  Clocks.weighted FibonacciQueueAnalysis.metric costs + costs "queue_updates" + costs "queue_pops" +
    costs "queue_empty_checks" + costs "edges" + costs "improvements" + costs "settlements"

def runtimeBound (size : Int) (adjacency : Adjacency) : Nat :=
  (20 + 3) * (edgeBudget adjacency (vertexRange size) + 1) + ((12 * (2 * size.toNat.log2 + 2)) + 3) * size.toNat







-- Main result: Correctness and running time






end FibonacciDijkstraAnalysis


