-- Prove2me | Definitions.Def_PlanarL1
-- name    : PlanarL1
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:04.679067+00:00
-- url     : https://prove2.me/theorems/a98ce3a8-467a-4253-93fe-b02bcfb050e3
-- statement:
--   IsPlanar(G) says that a simple graph G on a vertex type V admits a drawing in the plane ℝ×ℝ: there are an injective placement of vertices as points, and for every adjacent ordered pair (u,v) a continuous injective arc from the unit interval into the plane running from the point of u at parameter 0 to the point of v at parameter 1, such that no interior point of any arc (parameter strictly between 0 and 1) coincides with any vertex point, and any two arc interior points that coincide must come from arcs of the same unoriented edge, meaning (u,v)=(x,y) or (u,v)=(y,x). walkLength(length,p) sums the given edge-length function along the edges of a graph walk p, and graphDistance(G,length,u,v) is the infimum of these walk lengths over all walks from u to v in G. MainStatement is a defined proposition, not an established theorem. It asserts that there is a constant C ≥ 1 such that for every n, every simple graph G on Fin n that is connected and planar, and every real function length on pairs of vertices that is symmetric and strictly positive on adjacent pairs, there exist a measurable space Ω, a measure μ on it, and an assignment of each vertex i to an element f(i) of the real L¹(μ) space, such that for all vertices x and y the graph distance d_G(x,y) is at most ‖f(x)−f(y)‖₁ and ‖f(x)−f(y)‖₁ is at most C·d_G(x,y).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PlanarL1.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PlanarL1.lean; bytes 16..2085
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace PlanarL1

/-- A topological drawing by simple plane arcs, with injective vertex placement,
no vertex in an edge interior, and disjoint interiors for distinct unoriented edges. -/
def IsPlanar {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ (point : V → ℝ × ℝ) (arc : ∀ u v : V, G.Adj u v → C(unitInterval, ℝ × ℝ)),
    Function.Injective point ∧
    (∀ u v h, (arc u v h) 0 = point u ∧ (arc u v h) 1 = point v) ∧
    (∀ u v h, Function.Injective (arc u v h)) ∧
    (∀ u v h (t : unitInterval) w, 0 < (t : ℝ) → (t : ℝ) < 1 →
      (arc u v h) t ≠ point w) ∧
    (∀ u v h x y k (s t : unitInterval),
      0 < (s : ℝ) → (s : ℝ) < 1 → 0 < (t : ℝ) → (t : ℝ) < 1 →
      (arc u v h) s = (arc x y k) t →
      (u = x ∧ v = y) ∨ (u = y ∧ v = x))

/-- The sum of edge lengths along a finite graph walk. -/
def walkLength {V : Type} {G : SimpleGraph V} (length : V → V → ℝ)
    {u v : V} : G.Walk u v → ℝ
  | .nil => 0
  | @SimpleGraph.Walk.cons _ _ u w _ _ p => length u w + walkLength length p

/-- The infimum of lengths of actual walks between the two vertices. -/
noncomputable def graphDistance {V : Type} (G : SimpleGraph V)
    (length : V → V → ℝ) (u v : V) : ℝ :=
  sInf (Set.range (fun p : G.Walk u v => walkLength length p))

/-- One universal distortion bound for finite connected planar graphs with
arbitrary symmetric positive edge lengths, realized in a real `L¹` space. -/
def MainStatement : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (length : Fin n → Fin n → ℝ),
      G.Connected → IsPlanar G →
      (∀ u v, length u v = length v u) →
      (∀ u v, G.Adj u v → 0 < length u v) →
      ∃ (Ω : Type) (measurable : MeasurableSpace Ω)
          (μ : @MeasureTheory.Measure Ω measurable)
          (f : Fin n → @MeasureTheory.Lp Ω ℝ measurable _ 1 μ),
        ∀ x y, graphDistance G length x y ≤ ‖f x - f y‖ ∧
          ‖f x - f y‖ ≤ C * graphDistance G length x y



end PlanarL1
end OAI


