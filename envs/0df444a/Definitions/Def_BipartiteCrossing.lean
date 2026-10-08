-- Prove2me | Definitions.Def_BipartiteCrossing
-- name    : BipartiteCrossing
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:02.073772+00:00
-- url     : https://prove2.me/theorems/fb45933e-e028-4aab-be51-ad05a6bbb447
-- statement:
--   For a nonnegative integer r, axisPairs(r) is ⌊r/2⌋⌊(r−1)/2⌋, with subtraction truncated at zero. The plane is ℝ², and the complete bipartite graph with parts of sizes m and n has vertices in the disjoint union of two finite index sets and one edge for each pair of indices from opposite parts. A continuous drawing assigns distinct plane points to all vertices and an injective continuous path to each edge, joining its assigned endpoints; every interior point of an edge avoids all vertices. The interior of an edge is the image of path parameters strictly between zero and one. Two subsets have a proper crossing at x if an open local coordinate homeomorphism sends x to the origin and sends their portions in its domain exactly onto the horizontal and vertical axes within its image. Crossing points are points belonging to the interiors of two distinct edges. An admissible drawing additionally assumes that the crossing-point set is finite, every intersection of distinct edge interiors is a proper crossing, and no point lies in three distinct edge interiors. Its crossing count is the number of distinct crossing points. MainTarget is the defined proposition that, for every positive m and n, an admissible drawing exists with exactly axisPairs(m)axisPairs(n) crossings, and every admissible drawing has at least this many crossings.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BipartiteCrossing.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BipartiteCrossing.lean; bytes 330..2469
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Topology.Path
import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Util.CompileInductive

namespace OAI

noncomputable section

namespace Zarankiewicz

def axisPairs (r : ℕ) : ℕ := (r/2) * ((r-1)/2)


abbrev Plane := ℝ × ℝ
abbrev BipartiteVertex (m n : ℕ) := Fin m ⊕ Fin n
abbrev BipartiteEdge (m n : ℕ) := Fin m × Fin n

structure ContinuousDrawing (m n : ℕ) where
  vertex : BipartiteVertex m n → Plane
  vertex_injective : Function.Injective vertex
  edge : ∀ e : BipartiteEdge m n, Path (vertex (.inl e.1)) (vertex (.inr e.2))
  edge_injective : ∀ e, Function.Injective (edge e)
  interior_avoids_vertices : ∀ e t, t ∈ Set.Ioo (0 : unitInterval) 1 →
    ∀ v, edge e t ≠ vertex v

def edgeInterior {m n : ℕ} (D : ContinuousDrawing m n) (e : BipartiteEdge m n) : Set Plane :=
  D.edge e '' Set.Ioo (0 : unitInterval) 1

def ProperCrossing (A B : Set Plane) (x : Plane) : Prop :=
  ∃ chart : OpenPartialHomeomorph Plane Plane,
    x ∈ chart.source ∧ chart x = (0,0) ∧
    chart '' (chart.source ∩ A) = chart.target ∩ {y | y.2 = 0} ∧
    chart '' (chart.source ∩ B) = chart.target ∩ {y | y.1 = 0}

def crossingPoints {m n : ℕ} (D : ContinuousDrawing m n) : Set Plane :=
  {x | ∃ e f : BipartiteEdge m n, e ≠ f ∧ x ∈ edgeInterior D e ∧ x ∈ edgeInterior D f}

structure AdmissibleDrawing (m n : ℕ) extends ContinuousDrawing m n where
  crossings_finite : (crossingPoints toContinuousDrawing).Finite
  crossings_proper : ∀ e f, e ≠ f → ∀ x,
    x ∈ edgeInterior toContinuousDrawing e → x ∈ edgeInterior toContinuousDrawing f →
    ProperCrossing (edgeInterior toContinuousDrawing e) (edgeInterior toContinuousDrawing f) x
  no_triples : ∀ e f g, e ≠ f → e ≠ g → f ≠ g →
    edgeInterior toContinuousDrawing e ∩ edgeInterior toContinuousDrawing f ∩
      edgeInterior toContinuousDrawing g = ∅

def crossingCount {m n : ℕ} (D : AdmissibleDrawing m n) : ℕ := D.crossings_finite.toFinset.card

def MainTarget : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n →
    (∃ D : AdmissibleDrawing m n, crossingCount D = axisPairs m * axisPairs n) ∧
    (∀ D : AdmissibleDrawing m n, axisPairs m * axisPairs n ≤ crossingCount D)



end Zarankiewicz
end
end OAI


