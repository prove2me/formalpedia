-- Prove2me | Definitions.Def_Algo_dijkstra_dijkstra_Analysis
-- name    : Algo_dijkstra_dijkstra_Analysis
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:51:06.602705+00:00
-- url     : https://prove2.me/theorems/b285208a-24be-42de-97b8-6a6235c9b2f8
-- title:
--   Algo.dijkstra.dijkstra.Analysis definitions
-- statement:
--   Definitions and required structural lemmas from `Algo.dijkstra.dijkstra.Analysis`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/analysis/dijkstra/dijkstra.lean

import Definitions.Def_Algo_dijkstra_dijkstra_Generated
import Definitions.Def_Algo_dijkstra_dijkstra_Points
import Definitions.Def_Algo_dijkstra_dijkstra_Facts
import Definitions.Def_Algo_dijkstra_priority_queue_Analysis
import Definitions.Def_Algo2LeanLib_DijkstraExecution

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Analysis outline:
- `dijkstra_correct`: Reusable generic Dijkstra contract.
- `dijkstra_output_exists`: Termination, shortest paths, and queue costs.
- `every_execution`: Correctness and runtime for every execution.
-/

namespace ComposableDijkstraAnalysis

open Algo2LeanCore Algo2LeanGenerated Algo2Lean.Dijkstra
open Algo.graph.Algo2LeanGenerated
open Algo.dijkstra.dijkstra
open Algo.dijkstra.priority_queue
open PriorityQueueAnalysis

/-! The graph source is imported unchanged. These finite adjacency observations
    use its public interface; all shortest-path mathematics remains shared. -/

inductive AdjacencyChain (heap : Heap) (size : Int) :
    Option Ref_Edge → List (Int × Int) → Prop where
  | empty : AdjacencyChain heap size none []
  | cons (edge : Ref_Edge) (target weight : Int) (next : Option Ref_Edge)
      (tail : List (Int × Int))
      (valid : is_Edge heap edge)
      (readTarget : field_Edge_target heap edge = some target)
      (readWeight : field_Edge_weight heap edge = some weight)
      (readNext : field_Edge_next heap edge = some next)
      (targetNonnegative : 0 ≤ target) (targetBound : target < size)
      (weightNonnegative : 0 ≤ weight)
      (remaining : AdjacencyChain heap size next tail) :
      AdjacencyChain heap size (some edge) ((target, weight) :: tail)

/-- The public graph fields represent one finite adjacency list per vertex.
    Parallel edges, zero weights, self-loops, and shared suffixes are allowed. -/
structure GraphRep (heap : Heap) (graph : Ref_Graph) (size : Int) (heads : CollectionRef)
    (adjacency : Adjacency) : Prop where
  valid : is_Graph heap graph
  sizeNonnegative : 0 ≤ size
  readSize : field_Graph_size heap graph = some size
  readHeads : field_Graph_heads heap graph = some heads
  headsValid : seq_Edge_optional.valid heap heads
  chains : ∀ vertex, 0 ≤ vertex → vertex < size →
    ∃ head, seq_Edge_optional.get heap heads vertex = some head ∧
      AdjacencyChain heap size head (adjacency vertex)




def EdgeFieldsUnchanged (before after : Heap) : Prop :=
  ∀ ref, is_Edge before ref → is_Edge after ref ∧
    field_Edge_target after ref = field_Edge_target before ref ∧
    field_Edge_weight after ref = field_Edge_weight before ref ∧
    field_Edge_next after ref = field_Edge_next before ref










structure GraphFrame (before after : Heap) (graph : Ref_Graph) (heads : CollectionRef) : Prop where
  valid : is_Graph before graph → is_Graph after graph
  size : field_Graph_size after graph = field_Graph_size before graph
  headsField : field_Graph_heads after graph = field_Graph_heads before graph
  headsValid : seq_Edge_optional.valid before heads → seq_Edge_optional.valid after heads
  entries : ∀ vertex, seq_Edge_optional.get after heads vertex = seq_Edge_optional.get before heads vertex
  edges : EdgeFieldsUnchanged before after















@[simp] theorem edge_target_tick (heap : Heap) (clock : String) (amount : Nat) (edge : Ref_Edge) :
    field_Edge_target (heap.tick clock amount) edge = field_Edge_target heap edge := rfl
@[simp] theorem edge_weight_tick (heap : Heap) (clock : String) (amount : Nat) (edge : Ref_Edge) :
    field_Edge_weight (heap.tick clock amount) edge = field_Edge_weight heap edge := rfl
@[simp] theorem edge_next_tick (heap : Heap) (clock : String) (amount : Nat) (edge : Ref_Edge) :
    field_Edge_next (heap.tick clock amount) edge = field_Edge_next heap edge := rfl

variable (dependencies : Dependencies)

/-- The adjacency loop is described by its named source location and live variables.
    Temporary values from earlier iterations impose no obligations on the caller. -/
def AtScan (state : Algo.dijkstra.dijkstra.Algo2LeanGenerated.Configuration dependencies)
    (heap : Heap) (queue : ObjectRef) (distance settled : SeqRef)
    (vertex : Int) (edge : Option Ref_Edge) : Prop :=
  scan_edges.At.scan dependencies state ∧ state.heap = heap ∧
  scan_edges.Local.queue dependencies state = some queue ∧
  scan_edges.Local.distance dependencies state = some distance ∧
  scan_edges.Local.settled dependencies state = some settled ∧
  scan_edges.Local.vertex dependencies state = some vertex ∧
  scan_edges.Local.edge dependencies state = some edge

/-- Finish the adjacency loop from any local state with these source variables. -/
def ScanLoop (heap : Heap) (queue : ObjectRef) (distance settled : SeqRef)
    (vertex : Int) (edge : Option Ref_Edge) (finalHeap : Heap) : Prop :=
  ∀ state, AtScan dependencies state heap queue distance settled vertex edge →
    scan_edges.CallFrom dependencies state finalHeap ()

/-- The main loop needs only the graph, queue, and two client sequences. The
    initialized source and previous iteration's temporary values are irrelevant. -/
def AtExtract (state : Algo.dijkstra.dijkstra.Algo2LeanGenerated.Configuration dependencies)
    (heap : Heap) (graph : Ref_Graph) (queue : ObjectRef) (distance settled : SeqRef) : Prop :=
  dijkstra.At.extract dependencies state ∧ state.heap = heap ∧
  dijkstra.Local.graph dependencies state = some graph ∧
  dijkstra.Local.queue dependencies state = some queue ∧
  dijkstra.Local.distance dependencies state = some distance ∧
  dijkstra.Local.settled dependencies state = some settled

/-- Finish the main loop after counting its next emptiness test. This local
    continuation is independent of the code that initialized the search. -/
def ExtractLoop (heap : Heap) (graph : Ref_Graph) (queue : ObjectRef)
    (distance settled : SeqRef) (finalHeap : Heap) : Prop :=
  ∀ state, AtExtract dependencies state (heap.tick "queue_empty_checks") graph queue distance settled →
    dijkstra.CallFrom dependencies state finalHeap distance

















/-- The graph and initialized client sequences are supplied by the caller. -/
structure Client where
  graph : Ref_Graph
  size : Int
  heads : CollectionRef
  adjacency : Adjacency
  distance : SeqRef
  settled : SeqRef
  queue : ObjectRef
  caller : Heap := {}

def Client.protection (client : Client) : Protected :=
  ⟨[client.distance, client.settled], ["graph.Graph", "graph.Edge"], [client.heads], client.caller⟩

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
  distanceAllocated : client.distance < state.heap.nextRef
  settledAllocated : client.settled < state.heap.nextRef
  separate : client.distance ≠ client.settled









def QueueMatches (state : QueueState model) : Prop :=
  ∀ vertex key, (vertex,key) ∈ state.entries model ↔
    state.heap.read client.settled vertex = 0 ∧
    0 ≤ state.heap.read client.distance vertex ∧ key = state.heap.read client.distance vertex

structure LoopInvariant (state : QueueState model) (remaining : List Int) : Prop where
  storage : Storage model state
  matching : QueueMatches model state
  finiteInRange : ∀ vertex, 0 ≤ state.heap.read client.distance vertex →
    0 ≤ vertex ∧ vertex < client.size
  unique : remaining.Nodup
  members : ∀ vertex, vertex ∈ remaining ↔
    0 ≤ vertex ∧ vertex < client.size ∧ state.heap.read client.settled vertex = 0

/-- Weighted implementation-clock work is independent of the six client clocks. -/
def work (before after : Heap) : Nat := Clocks.weighted model.metric (Heap.cost before after)

theorem work_triangle (a b c : Heap) : work model a c ≤ work model a b + work model b c := by
  rw [work,work,work,← Clocks.weighted_add]
  apply Clocks.weighted_le
  intro name
  simp only [Heap.cost,Clocks.add]
  omega

structure CostBounds (before after : QueueState model) (vertices edges : Nat) : Prop where
  updates : Heap.cost before.heap after.heap "queue_updates" ≤ edges
  pops : Heap.cost before.heap after.heap "queue_pops" ≤ vertices
  checks : Heap.cost before.heap after.heap "queue_empty_checks" ≤ vertices
  visits : Heap.cost before.heap after.heap "edges" ≤ edges
  improvements : Heap.cost before.heap after.heap "improvements" ≤ edges
  settlements : Heap.cost before.heap after.heap "settlements" ≤ vertices
  amortized : work model before.heap after.heap + after.potential model ≤
    before.potential model + model.updateBudget * edges + model.popBudget * vertices

theorem CostBounds.refl (state : QueueState model) : CostBounds model state state 0 0 := by
  have zero : Heap.cost state.heap state.heap = (fun _ => 0) := by
    funext name
    simp [Heap.cost]
  constructor <;> simp [zero,work]

theorem CostBounds.trans {a b c : QueueState model} {v e v' e' : Nat}
    (one : CostBounds model a b v e) (two : CostBounds model b c v' e') :
    CostBounds model a c (v+v') (e+e') := by
  have cost (name : String) : Heap.cost a.heap c.heap name ≤
      Heap.cost a.heap b.heap name + Heap.cost b.heap c.heap name := by
    simp only [Heap.cost]
    omega
  refine ⟨Nat.le_trans (cost _) (Nat.add_le_add one.updates two.updates),
    Nat.le_trans (cost _) (Nat.add_le_add one.pops two.pops),
    Nat.le_trans (cost _) (Nat.add_le_add one.checks two.checks),
    Nat.le_trans (cost _) (Nat.add_le_add one.visits two.visits),
    Nat.le_trans (cost _) (Nat.add_le_add one.improvements two.improvements),
    Nat.le_trans (cost _) (Nat.add_le_add one.settlements two.settlements), ?_⟩
  have triangle := work_triangle model a.heap b.heap c.heap
  have first := one.amortized
  have second := two.amortized
  simp only [Nat.mul_add]
  omega

theorem CostBounds.weaken {a b : QueueState model} {v e v' e' : Nat}
    (one : CostBounds model a b v e) (vertices : v ≤ v') (edges : e ≤ e') :
    CostBounds model a b v' e' := by
  refine ⟨Nat.le_trans one.updates edges,Nat.le_trans one.pops vertices,Nat.le_trans one.checks vertices,
    Nat.le_trans one.visits edges,Nat.le_trans one.improvements edges,Nat.le_trans one.settlements vertices,?_⟩
  exact Nat.le_trans one.amortized (Nat.add_le_add
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ edges) _)
    (Nat.mul_le_mul_left _ vertices))

variable (contracts : Contracts model reservedClocks)
include contracts





structure QueueUpdated (before after : QueueState model) (vertex key : Int) : Prop where
  execution : PriorityQueue.push_or_decrease.Call dependencies.PriorityQueue before.heap
    (client.queue,vertex,key) after.heap ()
  storage : Storage model after
  contents : ∀ v k, (v,k) ∈ after.entries model ↔
    (v = vertex ∧ k = key) ∨ (v ≠ vertex ∧ (v,k) ∈ before.entries model)
  distance : after.heap.read client.distance = before.heap.read client.distance
  settled : after.heap.read client.settled = before.heap.read client.settled
  frame : GraphFrame before.heap after.heap client.graph client.heads
  bookkeeping : PreservesClocks reservedClocks before.heap after.heap
  amortized : work model before.heap after.heap + after.potential model ≤
    before.potential model + model.updateBudget

structure QueueExtracted (before after : QueueState model) (vertex key : Int) : Prop where
  execution : PriorityQueue.pop_min.Call dependencies.PriorityQueue before.heap client.queue after.heap vertex
  storage : Storage model after
  selected : (vertex,key) ∈ before.entries model
  least : ∀ v k, (v,k) ∈ before.entries model → key ≤ k
  contents : ∀ v k, (v,k) ∈ after.entries model ↔ v ≠ vertex ∧ (v,k) ∈ before.entries model
  distance : after.heap.read client.distance = before.heap.read client.distance
  settled : after.heap.read client.settled = before.heap.read client.settled
  frame : GraphFrame before.heap after.heap client.graph client.heads
  bookkeeping : PreservesClocks reservedClocks before.heap after.heap
  amortized : work model before.heap after.heap + after.potential model ≤
    before.potential model + model.popBudget











structure EdgeAdvanced (before after : QueueState model)
    (selected target weight : Int) (edge : Ref_Edge) (next : Option Ref_Edge) : Prop where
  storage : Storage model after
  matching : QueueMatches model after
  settled : after.heap.read client.settled = before.heap.read client.settled
  range : ∀ vertex, 0 ≤ after.heap.read client.distance vertex → 0 ≤ vertex ∧ vertex < client.size
  scan : RelaxScan (fun vertex => before.heap.read client.settled vertex ≠ 0)
    selected [(target,weight)] (before.heap.read client.distance) (after.heap.read client.distance)
  costs : CostBounds model before after 0 1
  frame : GraphFrame before.heap after.heap client.graph client.heads
  execution : ∀ finalHeap,
    ScanLoop dependencies after.heap client.queue client.distance client.settled selected next finalHeap →
    ScanLoop dependencies before.heap client.queue client.distance client.settled selected (some edge) finalHeap

structure AdjacencyScanned (before after : QueueState model)
    (selected : Int) (head : Option Ref_Edge) (edges : List (Int × Int)) : Prop where
  storage : Storage model after
  matching : QueueMatches model after
  settled : after.heap.read client.settled = before.heap.read client.settled
  range : ∀ vertex, 0 ≤ after.heap.read client.distance vertex → 0 ≤ vertex ∧ vertex < client.size
  scan : RelaxScan (fun vertex => before.heap.read client.settled vertex ≠ 0)
    selected edges (before.heap.read client.distance) (after.heap.read client.distance)
  costs : CostBounds model before after 0 edges.length
  frame : GraphFrame before.heap after.heap client.graph client.heads
  execution : ScanLoop dependencies before.heap client.queue client.distance client.settled selected head after.heap





/-- The common finite driver accounts for each successful extraction. The one
    final empty check is appended to the final heap exactly once. -/
def executionInterface : Algo2Lean.Dijkstra.Execution.Interface (QueueState model) := {
  distance := fun state => state.heap.read client.distance
  settled := fun state vertex => state.heap.read client.settled vertex ≠ 0
  invariant := LoopInvariant model
  completion := fun before after => ExtractLoop dependencies before.heap client.graph client.queue client.distance client.settled
    (after.heap.tick "queue_empty_checks") ∧ client.distance < after.heap.nextRef
  accounting := fun before after vertices edges => CostBounds model before after vertices edges
  zero := fun state => CostBounds.refl model state
  compose := fun first second => first.trans model second
  weaken := fun costs vertices edges => costs.weaken model vertices edges }





/-- Counts of actual source ticks, measured relative to arbitrary initial clocks. -/
structure OperationCounts (before after : Heap) (vertices edges : Nat) : Prop where
  updates : Heap.cost before after "queue_updates" ≤ edges + 1
  pops : Heap.cost before after "queue_pops" ≤ vertices
  checks : Heap.cost before after "queue_empty_checks" ≤ vertices + 1
  visits : Heap.cost before after "edges" ≤ edges
  improvements : Heap.cost before after "improvements" ≤ edges
  settlements : Heap.cost before after "settlements" ≤ vertices







-- Main result: Correctness and running time


end ComposableDijkstraAnalysis


