-- Prove2me | Definitions.Def_ClassicalON
-- name    : ClassicalON
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:03.987689+00:00
-- url     : https://prove2.me/theorems/8ab5b86b-ab86-4114-893b-ac0b4f29b225
-- statement:
--   Sites are points of the square lattice ℤ². A lattice graph consists of finitely many sites and selected ordered edges whose endpoint is one unit east or north of its starting point. For a nonnegative integer n, a spin is a unit vector in ℝⁿ, and a configuration assigns one spin to every vertex. The sphere measure is normalized by multiplying surface measure by the reciprocal of its total mass; the reference measure on configurations is the product of these measures over the vertices. Given real edge couplings b, the interaction of a configuration σ is the sum, over edges (u,v), of b(u,v)⟨σ(u),σ(v)⟩. The partition function is the reference-measure integral of the exponential of this interaction. The correlation between vertices x and y is the integral of ⟨σ(x),σ(y)⟩ times that same exponential, divided by the partition function. Site distance is ordinary Euclidean distance in ℝ². ExponentialDecay is the defined proposition that, for every integer n ≥ 3 and every real β > 0, there exist real constants A and m with m > 0 such that, uniformly over all such finite lattice graphs, all edge couplings satisfying 0 ≤ b(e) ≤ β, and every pair of vertices x,y, the correlation is nonnegative and at most A exp(−m|x−y|). The constants may depend on n and β; no explicit positivity condition is imposed on A.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ClassicalON.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ClassicalON.lean; bytes 16..1884
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace ClassicalON

abbrev Site := ℤ × ℤ

def PositiveNeighbor (x y : Site) : Prop :=
  (y.1 = x.1 + 1 ∧ y.2 = x.2) ∨ (y.1 = x.1 ∧ y.2 = x.2 + 1)

structure LatticeGraph where
  vertices : Finset Site
  edges : Finset (vertices × vertices)
  nearest : ∀ e ∈ edges, PositiveNeighbor e.1.val e.2.val

abbrev Spin (n : ℕ) := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
abbrev Configuration (n : ℕ) (G : LatticeGraph) := G.vertices → Spin n

def sphereProbability (n : ℕ) : Measure (Spin n) :=
  let surface := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
  (surface Set.univ)⁻¹ • surface

def referenceLaw (n : ℕ) (G : LatticeGraph) : Measure (Configuration n G) :=
  Measure.pi (fun _ => sphereProbability n)

def interaction (n : ℕ) (G : LatticeGraph) (b : G.edges → ℝ)
    (σ : Configuration n G) : ℝ :=
  ∑ e : G.edges, b e * ⟪(σ e.val.1).val, (σ e.val.2).val⟫_ℝ

def partition (n : ℕ) (G : LatticeGraph) (b : G.edges → ℝ) : ℝ :=
  ∫ σ, Real.exp (interaction n G b σ) ∂referenceLaw n G

def correlation (n : ℕ) (G : LatticeGraph) (b : G.edges → ℝ)
    (x y : G.vertices) : ℝ :=
  (∫ σ, ⟪(σ x).val, (σ y).val⟫_ℝ * Real.exp (interaction n G b σ)
    ∂referenceLaw n G) / partition n G b

def siteDistance (x y : Site) : ℝ :=
  Real.sqrt (((x.1 : ℝ) - (y.1 : ℝ)) ^ 2 + ((x.2 : ℝ) - (y.2 : ℝ)) ^ 2)

def ExponentialDecay : Prop :=
  ∀ (n : ℕ), 3 ≤ n → ∀ (β : ℝ), 0 < β →
    ∃ A m : ℝ, 0 < m ∧ ∀ (G : LatticeGraph) (b : G.edges → ℝ),
      (∀ e, 0 ≤ b e ∧ b e ≤ β) → ∀ x y : G.vertices,
        0 ≤ correlation n G b x y ∧
          correlation n G b x y ≤ A * Real.exp (-m * siteDistance x.val y.val)



end ClassicalON
end
end OAI


