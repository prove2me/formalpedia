-- Prove2me | Definitions.Def_Algo_prim_graph_Analysis
-- name    : Algo_prim_graph_Analysis
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-11T01:08:32.415642+00:00
-- url     : https://prove2.me/theorems/26286742-efa4-4ddc-87f5-ca8b32b9477d
-- title:
--   Algo.prim.graph.Analysis definitions
-- statement:
--   Definitions and required structural lemmas from `Algo.prim.graph.Analysis`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/d832a5655d7cac6d032e728a4798128147b27922/examples/analysis/prim/graph.lean

import Definitions.Def_Algo_prim_graph_Generated
import Definitions.Def_Algo2LeanLib_Dijkstra
import Definitions.Def_Algo2LeanLib_KruskalMath_PrimExtension

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Representation and preservation of finite adjacency lists with signed weights. -/
namespace PrimGraph
open Algo2LeanCore Algo2LeanGenerated Algo2Lean.Dijkstra
open Algo.prim.graph.Algo2LeanGenerated

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
      (remaining : AdjacencyChain heap size next tail) :
      AdjacencyChain heap size (some edge) ((target, weight) :: tail)

/-- The public graph fields represent one finite adjacency list per vertex.
    Parallel edges, signed weights, self-loops, and shared suffixes are allowed. -/
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


/-- Adjacency occurrences are ordered first by source vertex, then by their
    order in its adjacency list. Both orientations of an undirected edge remain
    distinct occurrences, including when endpoints and weights are equal. -/
def adjacencyEntries (size : Int) (adjacency : Adjacency) : List (Int × Int × Int) :=
  (vertexRange size).flatMap fun source =>
    (adjacency source).map fun entry => (source, entry)

/-- The finite mathematical input assigns each adjacency occurrence its position
    as a unique edge identity. These identities are ghost data used in proofs. -/
def inputEdges (size : Int) (adjacency : Adjacency) : List Algo2Lean.Kruskal.Edge :=
  (adjacencyEntries size adjacency).zipIdx.map fun item =>
    ⟨item.2, item.1.1, item.1.2.1, item.1.2.2⟩













/-- Each directed adjacency observation has an observation with reversed
    endpoints and the same weight. Parallel-edge multiplicities are irrelevant
    to this condition; individual occurrences keep their distinct identities. -/
def Symmetric (size : Int) (adjacency : Adjacency) : Prop :=
  ∀ source target weight, 0 ≤ source → source < size →
    (target,weight) ∈ adjacency source → (source,weight) ∈ adjacency target



end PrimGraph


