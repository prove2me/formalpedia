-- Prove2me | Definitions.Def_Algo_prim_support_Analysis
-- name    : Algo_prim_support_Analysis
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-11T01:10:56.495096+00:00
-- url     : https://prove2.me/theorems/2b806f68-5c27-43bf-be78-91cff5435397
-- title:
--   Algo.prim.support.Analysis definitions
-- statement:
--   Definitions and required structural lemmas from `Algo.prim.support.Analysis`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/d832a5655d7cac6d032e728a4798128147b27922/examples/analysis/prim/support.lean

import Definitions.Def_Algo_prim_control_Analysis
import Definitions.Def_Algo_prim_graph_Analysis
import Definitions.Def_Algo_dijkstra_priority_queue_Analysis

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Queue storage and compositional clock accounting for Prim. The queue backend
is abstract, and its amortized potential is carried through actual calls. -/
namespace PrimAnalysis
open Algo2LeanCore Algo2LeanGenerated Algo2Lean.Dijkstra
open Algo.prim.graph.Algo2LeanGenerated
open Algo.prim.prim Algo.dijkstra.priority_queue
open PriorityQueueAnalysis PrimGraph PrimControl
variable (dependencies : Dependencies)

/-- The graph and initialized client sequences are supplied by the caller. -/
structure Client where
  graph : Ref_Graph
  size : Int
  heads : CollectionRef
  adjacency : Adjacency
  key : SeqRef
  parent : SeqRef
  root : Int
  selected : SeqRef
  queue : ObjectRef
  caller : Heap := {}

def Client.protection (client : Client) : Protected :=
  ⟨[client.key, client.parent, client.selected], ["prim.graph.Graph", "prim.graph.Edge"], [client.heads], client.caller⟩

def reservedClocks : List String :=
  ["queue_updates", "queue_pops", "queue_empty_checks", "edges", "improvements", "settlements"]

variable {dependencies}
variable {client : Client}
variable (model : Model dependencies.PriorityQueue client.queue client.protection)

structure QueueState where
  heap : Heap
  queueState : model.State

namespace QueueState

def tick (state : QueueState model) (name : String) : QueueState model :=
  {state with heap := state.heap.tick name}
def write (state : QueueState model) (ref : SeqRef) (index value : Int) : QueueState model :=
  {state with heap := state.heap.write ref index value}
abbrev entries (state : QueueState model) := model.entries state.queueState
abbrev potential (state : QueueState model) := model.potential state.queueState

end QueueState

structure Storage (state : QueueState model) : Prop where
  graph : GraphRep state.heap client.graph client.size client.heads client.adjacency
  queue : model.Rep state.heap state.queueState
  keyAllocated : client.key < state.heap.nextRef
  parentAllocated : client.parent < state.heap.nextRef
  selectedAllocated : client.selected < state.heap.nextRef
  keyParent : client.key ≠ client.parent
  parentSelected : client.parent ≠ client.selected
  separate : client.key ≠ client.selected









def QueueMatches (state : QueueState model) : Prop :=
  ∀ vertex key, (vertex,key) ∈ state.entries model ↔
    state.heap.read client.selected vertex = 0 ∧
    (vertex = client.root ∨ 0 ≤ state.heap.read client.parent vertex) ∧ key = state.heap.read client.key vertex

/-- Weighted implementation-clock work is independent of the six client clocks. -/
def work (before after : Heap) : Nat := Clocks.weighted model.metric (Heap.cost before after)



structure CostBounds (before after : QueueState model) (vertices edges : Nat) : Prop where
  updates : Heap.cost before.heap after.heap "queue_updates" ≤ edges
  pops : Heap.cost before.heap after.heap "queue_pops" ≤ vertices
  checks : Heap.cost before.heap after.heap "queue_empty_checks" ≤ vertices
  visits : Heap.cost before.heap after.heap "edges" ≤ edges
  improvements : Heap.cost before.heap after.heap "improvements" ≤ edges
  settlements : Heap.cost before.heap after.heap "settlements" ≤ vertices
  amortized : work model before.heap after.heap + after.potential model ≤
    before.potential model + model.updateBudget * edges + model.popBudget * vertices







variable (contracts : Contracts model reservedClocks)
include contracts





structure QueueUpdated (before after : QueueState model) (vertex key : Int) : Prop where
  execution : PriorityQueue.push_or_decrease.Call dependencies.PriorityQueue before.heap
    (client.queue,vertex,key) after.heap ()
  storage : Storage model after
  contents : ∀ v k, (v,k) ∈ after.entries model ↔
    (v = vertex ∧ k = key) ∨ (v ≠ vertex ∧ (v,k) ∈ before.entries model)
  key : after.heap.read client.key = before.heap.read client.key
  parent : after.heap.read client.parent = before.heap.read client.parent
  selected : after.heap.read client.selected = before.heap.read client.selected
  frame : GraphFrame before.heap after.heap client.graph client.heads
  bookkeeping : PreservesClocks reservedClocks before.heap after.heap
  amortized : work model before.heap after.heap + after.potential model ≤
    before.potential model + model.updateBudget

structure QueueExtracted (before after : QueueState model) (vertex key : Int) : Prop where
  execution : PriorityQueue.pop_min.Call dependencies.PriorityQueue before.heap client.queue after.heap vertex
  storage : Storage model after
  member : (vertex,key) ∈ before.entries model
  least : ∀ v k, (v,k) ∈ before.entries model → key ≤ k
  contents : ∀ v k, (v,k) ∈ after.entries model ↔ v ≠ vertex ∧ (v,k) ∈ before.entries model
  key : after.heap.read client.key = before.heap.read client.key
  parent : after.heap.read client.parent = before.heap.read client.parent
  selected : after.heap.read client.selected = before.heap.read client.selected
  frame : GraphFrame before.heap after.heap client.graph client.heads
  bookkeeping : PreservesClocks reservedClocks before.heap after.heap
  amortized : work model before.heap after.heap + after.potential model ≤
    before.potential model + model.popBudget












end PrimAnalysis


