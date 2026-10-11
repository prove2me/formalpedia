-- Prove2me | Definitions.Def_Algo_dijkstra_support_fibonacci_queue_Analysis
-- name    : Algo_dijkstra_support_fibonacci_queue_Analysis
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:51:34.466316+00:00
-- url     : https://prove2.me/theorems/e600ed99-2410-44a2-9d62-68970f5afd6f
-- title:
--   Algo.dijkstra.support.fibonacci_queue.Analysis definitions
-- statement:
--   Definitions and required structural lemmas from `Algo.dijkstra.support.fibonacci_queue.Analysis`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/analysis/dijkstra/support/fibonacci_queue.lean

import Definitions.Def_Algo_dijkstra_support_fibonacci_heap_Analysis
import Definitions.Def_Algo_dijkstra_priority_queue_Analysis

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! The Fibonacci implementation supplies the abstract queue contract once.
    The bridge is instantiated by generated interface-binding theorems; neither
    this module nor the heap proof imports a graph algorithm. -/

namespace FibonacciQueueAnalysis

open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap
open Algo.fibonacci_heap.Algo2LeanGenerated
open Algo.dijkstra.priority_queue
open FibonacciModuleAnalysis PriorityQueueAnalysis

/-- A generated binding transfers public heap summaries to interface summaries. -/
structure Bridge (code : PriorityQueue.Code) : Prop where
  valid : ∀ heap queue, code.valid heap queue = true ↔ is_FibonacciHeap heap queue
  is_empty : ∀ {before after queue result},
    FibonacciHeap.is_empty.Call before queue after result →
    PriorityQueue.is_empty.Call code before queue after result
  update : ∀ {before after queue vertex key},
    FibonacciHeap.push_or_decrease.Call before (queue, vertex, key) after () →
    PriorityQueue.push_or_decrease.Call code before (queue, vertex, key) after ()
  extract : ∀ {before after queue vertex},
    FibonacciHeap.pop_min.Call before queue after vertex →
    PriorityQueue.pop_min.Call code before queue after vertex

structure State where
  layout : Layout
  forest : Algo2Lean.Fibonacci.Forest

/-- Protected client sequences are separate from the queue's private storage. -/
structure Rep (queue : ObjectRef) (protection : Protected) (capacity : Int)
    (heap : Heap) (state : State) : Prop where
  represented : QueueRep heap queue state.layout state.forest
  separate : ∀ ref ∈ protection.sequences, ref ∉ state.layout.refs
  bounded : ∀ vertex key, (vertex, key) ∈ state.forest.entries → 0 ≤ vertex ∧ vertex < capacity
  callerPreserved : protection.caller.Footprint heap [] [] []
  privateSequences : ∀ ref ∈ state.layout.refs, protection.caller.nextRef ≤ ref
  privateObject : protection.caller.nextObject ≤ queue
  clientSequences : ∀ ref ∈ protection.sequences, protection.caller.nextRef ≤ ref

theorem Rep.tick {queue protection capacity heap state}
    (rep : Rep queue protection capacity heap state) (clock : String) (amount : Nat) :
    Rep queue protection capacity (heap.tick clock amount) state := by
  refine ⟨⟨Layout.Valid.tick _ _ _ rep.represented.layoutValid _ _, ?_⟩, rep.separate, rep.bounded, rep.callerPreserved.tick clock amount,
    rep.privateSequences, rep.privateObject, rep.clientSequences⟩
  simpa only [snapshot_tick] using rep.represented.represented

theorem Rep.write {queue protection capacity heap state}
    (rep : Rep queue protection capacity heap state) (ref : SeqRef) (guarded : ref ∈ protection.sequences)
    (index value : Int) : Rep queue protection capacity (heap.write ref index value) state := by
  have outside := rep.separate ref guarded
  have read (target : SeqRef) (member : target ∈ state.layout.refs) :
      (heap.write ref index value).read target = heap.read target := by
    funext position
    apply Heap.read_write_other_ref
    intro same
    exact outside (same ▸ member)
  have unchanged : snapshot (heap.write ref index value) state.layout = snapshot heap state.layout := by
    unfold snapshot
    congr 1 <;> apply read <;> simp [Layout.refs]
  refine ⟨⟨Layout.Valid.write _ _ _ rep.represented.layoutValid _ _ _, ?_⟩, rep.separate, rep.bounded,
    rep.callerPreserved.write ref index value (Or.inr (rep.clientSequences ref guarded)),
    rep.privateSequences, rep.privateObject, rep.clientSequences⟩
  rw [unchanged]
  exact rep.represented.represented

/-- The seven instrumented heap event categories, each with unit weight. -/
def metric : List (String × Nat) := heapClocks.map fun name => (name, 1)



def model (code : PriorityQueue.Code) (bridge : Bridge code) (queue : ObjectRef)
    (protection : Protected) (capacity : Int) : Model code queue protection where
  State := State
  entries := fun state => state.forest.entries
  Rep := Rep queue protection capacity
  capacity := capacity
  callerPreserved := Rep.callerPreserved
  unique := fun rep => rep.represented.represented.valid.1
  bounded := fun rep => rep.bounded
  metric := metric
  potential := fun state => Algo2Lean.Fibonacci.scaledPotential state.forest.counts
  updateBudget := 20
  popBudget := 12 * (2 * capacity.toNat.log2 + 2)
  valid := fun rep => (bridge.valid _ _).mpr rep.represented.layoutValid.object
  tick := Rep.tick
  write := Rep.write








/-- The constructor gives an empty abstract state with fresh private sequences. -/
def initialState (heap : Heap) : State := ⟨emptyLayout heap, []⟩













end FibonacciQueueAnalysis


