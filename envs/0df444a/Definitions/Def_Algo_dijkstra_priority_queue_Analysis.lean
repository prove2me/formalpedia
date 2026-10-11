-- Prove2me | Definitions.Def_Algo_dijkstra_priority_queue_Analysis
-- name    : Algo_dijkstra_priority_queue_Analysis
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:40:23.177475+00:00
-- url     : https://prove2.me/theorems/54a07b95-96eb-4b8b-9479-f72d83a2574c
-- title:
--   Algo.dijkstra.priority_queue.Analysis definitions
-- statement:
--   Definitions and required structural lemmas from `Algo.dijkstra.priority_queue.Analysis`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/analysis/dijkstra/priority_queue.lean

import Definitions.Def_Algo_dijkstra_priority_queue_Generated
import Definitions.Def_Algo2LeanLib_CallCost
import Definitions.Def_Algo2LeanLib_Footprint

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
The priority-queue contract mentions only public operations, abstract contents,
and protected client storage. A backend chooses its own ghost state and
representation. No queue layout, balancing invariant, or implementation clock
is part of this interface.
-/

namespace PriorityQueueAnalysis

open Algo2LeanGenerated
open Algo.dijkstra.priority_queue

/-- Queue calls preserve the listed client locations. The caller snapshot marks
    all storage that existed before the private queue and work arrays were
    allocated; its contents remain an invariant of the represented queue. -/
structure Protected where
  sequences : List SeqRef
  objectClasses : List String
  collections : List CollectionRef
  caller : Heap := {}

/-- Allocation is allowed; every previously allocated protected value survives. -/
structure Frame (protection : Protected) (before after : Heap) : Prop where
  nextRef : before.nextRef ≤ after.nextRef
  nextObject : before.nextObject ≤ after.nextObject
  nextCollection : before.nextCollection ≤ after.nextCollection
  classes : ∀ ref, ref < before.nextObject → after.objectClass ref = before.objectClass ref
  types : ∀ ref, ref < before.nextCollection → after.sequenceType ref = before.sequenceType ref
  sequences : ∀ ref ∈ protection.sequences, ref < before.nextRef → after.read ref = before.read ref
  objects : ∀ ref className, ref < before.nextObject → before.objectClass ref = some className →
    className ∈ protection.objectClasses →
    after.objects ref = before.objects ref
  collections : ∀ ref ∈ protection.collections, ref < before.nextCollection →
    after.collections ref = before.collections ref

/-- One interface instance and its abstract contents. The protected sequence
    writes belong to the caller, so they cannot invalidate the queue. -/
structure Model (code : PriorityQueue.Code) (queue : ObjectRef) (protection : Protected) where
  State : Type
  entries : State → List (Int × Int)
  Rep : Heap → State → Prop
  capacity : Int
  /-- Representation invariants retain every location from the caller snapshot. -/
  callerPreserved : ∀ {heap state}, Rep heap state → protection.caller.Footprint heap [] [] []
  unique : ∀ {heap state}, Rep heap state → (entries state |>.map Prod.fst).Nodup
  bounded : ∀ {heap state}, Rep heap state → ∀ vertex key, (vertex,key) ∈ entries state →
    0 ≤ vertex ∧ vertex < capacity
  metric : List (String × Nat) := []
  potential : State → Nat := fun _ => 0
  updateBudget : Nat := 0
  popBudget : Nat := 0
  valid : ∀ {heap state}, Rep heap state → code.valid heap queue = true
  tick : ∀ {heap state}, Rep heap state → ∀ clock amount, Rep (heap.tick clock amount) state
  write : ∀ {heap state}, Rep heap state → ∀ ref ∈ protection.sequences,
    ∀ index value, Rep (heap.write ref index value) state

/-- Each call preserves the caller's reserved clocks. Queue implementation
    clocks are deliberately unrestricted and may be analyzed independently. -/
def PreservesClocks (reserved : List String) (before after : Heap) : Prop :=
  ∀ name ∈ reserved, after.clocks name = before.clocks name

structure Updated {code : PriorityQueue.Code} {queue : ObjectRef} {protection : Protected}
    (model : Model code queue protection) (reserved : List String)
    (before after : Heap) (state next : model.State) (vertex key : Int) : Prop where
  execution : PriorityQueue.push_or_decrease.Call code before (queue, vertex, key) after ()
  represented : model.Rep after next
  contents : ∀ v k, (v,k) ∈ model.entries next ↔
    (v = vertex ∧ k = key) ∨ (v ≠ vertex ∧ (v,k) ∈ model.entries state)
  frame : Frame protection before after
  clocks : PreservesClocks reserved before after
  amortized : Clocks.weighted model.metric (Heap.cost before after) + model.potential next ≤
    model.potential state + model.updateBudget

structure Extracted {code : PriorityQueue.Code} {queue : ObjectRef} {protection : Protected}
    (model : Model code queue protection) (reserved : List String)
    (before after : Heap) (state next : model.State) (vertex key : Int) : Prop where
  execution : PriorityQueue.pop_min.Call code before queue after vertex
  represented : model.Rep after next
  selected : (vertex,key) ∈ model.entries state
  least : ∀ v k, (v,k) ∈ model.entries state → key ≤ k
  contents : ∀ v k, (v,k) ∈ model.entries next ↔ v ≠ vertex ∧ (v,k) ∈ model.entries state
  frame : Frame protection before after
  clocks : PreservesClocks reserved before after
  amortized : Clocks.weighted model.metric (Heap.cost before after) + model.potential next ≤
    model.potential state + model.popBudget

/-- Local terminating call contracts. No field assumes a Dijkstra run,
    shortest-path correctness, or a whole-program complexity bound. -/
structure Contracts {code : PriorityQueue.Code} {queue : ObjectRef} {protection : Protected}
    (model : Model code queue protection) (reserved : List String) : Prop where
  metricReserved : ∀ name ∈ reserved, ∀ item ∈ model.metric, item.1 ≠ name
  is_empty : ∀ heap state, model.Rep heap state →
    PriorityQueue.is_empty.Call code heap queue heap (model.entries state).isEmpty
  update : ∀ heap state vertex key, model.Rep heap state → 0 ≤ vertex → vertex < model.capacity →
    (∀ old, (vertex,old) ∈ model.entries state → key < old) →
    ∃ after next, Updated model reserved heap after state next vertex key
  extract : ∀ heap state, model.Rep heap state → model.entries state ≠ [] →
    ∃ after next vertex key, Extracted model reserved heap after state next vertex key





end PriorityQueueAnalysis


