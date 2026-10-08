-- Prove2me | Definitions.Def_BarnetteHamiltonian
-- name    : BarnetteHamiltonian
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:01.191843+00:00
-- url     : https://prove2.me/theorems/cb545727-307e-4ef9-9002-7bf3473ca502
-- statement:
--   A plane embedding of a simple graph assigns distinct points of ℝ² to its vertices and an injective continuous path to each oriented edge. Reversing the orientation reverses the path; an edge path meets a vertex point only at its corresponding endpoint; and interiors of paths for different undirected edges are disjoint. These are requirements of the embedding structure. A graph is planar when such an embedding exists. For a finite graph, three-vertex-connectivity means that it has at least four vertices and that deleting any set of at most two vertices, together with their incident edges, leaves a connected induced graph. Having a Hamiltonian cycle means that there is a closed walk based at some vertex which is a single cycle visiting every vertex exactly once before returning to its starting vertex. MainStatement is the defined proposition that every finite simple graph in which each vertex has degree three, whose vertices can be partitioned into two parts with every edge joining the parts, and which is planar and three-vertex-connected has a Hamiltonian cycle. The proposition is defined here, rather than proved.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BarnetteHamiltonian.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BarnetteHamiltonian.lean; bytes 16..1881
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace Barnette

universe u

/-- A topological plane drawing of a simple graph, with no crossings. -/
structure PlaneEmbedding {V : Type u} (G : SimpleGraph V) where
  point : V → ℝ × ℝ
  point_injective : Function.Injective point
  arc : ∀ (v w : V), G.Adj v w → Path (point v) (point w)
  arc_injective : ∀ (v w : V) (h : G.Adj v w),
    Function.Injective (arc v w h)
  arc_reverse : ∀ (v w : V) (h : G.Adj v w),
    arc w v h.symm = (arc v w h).symm
  arc_avoids_vertices : ∀ (v w : V) (h : G.Adj v w)
    (t : unitInterval) (z : V),
    arc v w h t = point z →
      (t = 0 ∧ z = v) ∨ (t = 1 ∧ z = w)
  interiors_disjoint : ∀ (v w x y : V) (h : G.Adj v w) (k : G.Adj x y)
    (t s : unitInterval),
    t ≠ 0 → t ≠ 1 → s ≠ 0 → s ≠ 1 →
    arc v w h t = arc x y k s →
      (v = x ∧ w = y) ∨ (v = y ∧ w = x)

/-- Planarity means existence of a crossing-free topological plane embedding. -/
def Planar {V : Type u} (G : SimpleGraph V) : Prop :=
  Nonempty (PlaneEmbedding G)

/-- Deleting any set of at most two vertices leaves a connected graph of order at least two. -/
def ThreeVertexConnected {V : Type u} [Fintype V] (G : SimpleGraph V) : Prop :=
  4 ≤ Fintype.card V ∧
    ∀ S : Finset V, S.card ≤ 2 → (G.induce {v | v ∉ S}).Connected

/-- A single spanning cycle, not a possibly disconnected spanning 2-factor. -/
def HasHamiltonianCycle {V : Type u} [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ v : V, ∃ p : G.Walk v v, p.IsHamiltonianCycle

/-- Cubic bipartite three-vertex-connected plane graphs have a Hamiltonian cycle. -/
def MainStatement : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj],
    G.IsRegularOfDegree 3 → G.IsBipartite → Planar G →
      ThreeVertexConnected G → HasHamiltonianCycle G



end Barnette
end OAI


