-- Prove2me | Definitions.Def_Algo_prim_prim_fibonacci_Analysis
-- name    : Algo_prim_prim_fibonacci_Analysis
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-11T01:15:38.985985+00:00
-- url     : https://prove2.me/theorems/5948aad0-fba9-40cb-a14f-54edeaece22f
-- title:
--   Algo.prim.prim_fibonacci.Analysis definitions
-- statement:
--   Definitions and required structural lemmas from `Algo.prim.prim_fibonacci.Analysis`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/d832a5655d7cac6d032e728a4798128147b27922/examples/analysis/prim/prim_fibonacci.lean

import Definitions.Def_Algo_prim_prim_fibonacci_Generated
import Definitions.Def_Algo_prim_prim_fibonacci_Facts
import Definitions.Def_Algo_prim_prim_Analysis
import Definitions.Def_Algo_dijkstra_support_fibonacci_queue_Analysis

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Fibonacci-heap Prim constructs three private client sequences and one queue.
    The wrapper links the generic Prim call contract to the existing Fibonacci
    heap contract, preserving the original caller's storage and clock values. -/

namespace FibonacciPrimAnalysis

open Algo2LeanCore Algo2LeanGenerated Algo2Lean.Dijkstra
open Algo.prim.graph.Algo2LeanGenerated
open Algo.prim.prim_fibonacci
open PrimGraph PrimAnalysis

/-- Compiler-generated bindings connect the unchanged heap implementation to
    Prim's abstract queue interface. -/
theorem bridge : FibonacciQueueAnalysis.Bridge FibonacciHeap_as_PriorityQueue := {
  valid := by intro heap ref; simp [FibonacciHeap_as_PriorityQueue]
  is_empty := FibonacciHeap_as_PriorityQueue_summary_is_empty
  update := FibonacciHeap_as_PriorityQueue_summary_push_or_decrease
  extract := FibonacciHeap_as_PriorityQueue_summary_pop_min
}





/-- Each explicit heap event and Prim bookkeeping clock is counted once. -/
def clockWork (costs : Clocks) : Nat :=
  Clocks.weighted FibonacciQueueAnalysis.metric costs + costs "queue_updates" + costs "queue_pops" +
    costs "queue_empty_checks" + costs "edges" + costs "improvements" + costs "settlements"

/-- An explicit reusable bound in directed adjacency occurrences and vertices. -/
def runtimeBound (size : Int) (adjacency : Adjacency) : Nat :=
  (20 + 3) * (edgeBudget adjacency (vertexRange size) + 1) +
    ((12 * (2 * size.toNat.log2 + 2)) + 3) * size.toNat

/-- The usual Fibonacci-heap complexity scale, retaining one logarithmic unit
    for single-vertex inputs. Edges count directed adjacency occurrences. -/
def runtimeScale (size : Int) (adjacency : Adjacency) : Nat :=
  edgeBudget adjacency (vertexRange size) + size.toNat * (size.toNat.log2 + 1)





 abbrev allocatedHeap (heap : Heap) : Heap :=
  ((heap.allocate (fun _ => -1)).allocate (fun _ => 0)).allocate (fun _ => 0)

 abbrev client (heap : Heap) (graph : Ref_Graph) (size root : Int)
    (heads : CollectionRef) (adjacency : Adjacency) : Client :=
  ⟨graph,size,heads,adjacency,heap.nextRef+1,heap.nextRef,root,heap.nextRef+2,heap.nextObject,heap⟩

 abbrev queueModel (heap : Heap) (graph : Ref_Graph) (size root : Int)
    (heads : CollectionRef) (adjacency : Adjacency) :
    PriorityQueueAnalysis.Model use_prim_prim_0.PriorityQueue heap.nextObject
      (client heap graph size root heads adjacency).protection :=
  FibonacciQueueAnalysis.model FibonacciHeap_as_PriorityQueue bridge heap.nextObject
    (client heap graph size root heads adjacency).protection size

 abbrev initial (heap : Heap) (graph : Ref_Graph) (size root : Int)
    (heads : CollectionRef) (adjacency : Adjacency) :
    QueueState (dependencies := use_prim_prim_0)
      (client := client heap graph size root heads adjacency)
      (queueModel heap graph size root heads adjacency) :=
  ⟨FibonacciModuleAnalysis.newHeap (allocatedHeap heap),
    FibonacciQueueAnalysis.initialState (allocatedHeap heap)⟩











-- Main result: Correctness and running time


end FibonacciPrimAnalysis


