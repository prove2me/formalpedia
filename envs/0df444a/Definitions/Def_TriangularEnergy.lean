-- Prove2me | Definitions.Def_TriangularEnergy
-- name    : TriangularEnergy
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:22.097029+00:00
-- url     : https://prove2.me/theorems/c844ce8e-6d5f-4094-babf-b09e44ef8911
-- statement:
--   The block works in the Euclidean plane Plane = ℝ². A set C of plane points is called LocallyFinite if its intersection with every closed disk centred at the origin of radius R is finite. For such a set, diskPoints(C,R) is the finite set of points of C in the closed disk of radius R (the empty set if that intersection is infinite), and diskCount(C,R) is its cardinality. DensityOne(C) means that diskCount(C,R)/(πR²) tends to 1 as R tends to infinity. A function g : ℝ → ℝ is an AdmissiblePotential if it is infinitely differentiable on (0,∞), takes nonnegative values for t>0, and satisfies (−1)^r times the rth iterated derivative of g is nonnegative at every t>0 for every natural number r, so g is completely monotone on the positive reals. The diskEnergy of g on C at radius R is the extended nonnegative real obtained by summing ofReal(g(‖x−y‖²)) over all ordered pairs of distinct points x,y in diskPoints(C,R) and multiplying by the inverse of diskCount(C,R). The energy of g on C is the liminf of diskEnergy as R tends to infinity. In the AtomicTriangular namespace, with b = √3/2, triangularPoint(j,k) for integers j,k is (√b)⁻¹ times the vector (j+k/2, k·b), and A is the set of all these points, the triangular lattice. The definitions above are re-exported under the same names, and latticeEnergy(g) is the sum, in the extended nonnegative reals and so permitted to diverge, of ofReal(g(‖a‖²)) over all lattice points a in A other than the origin. No theorem is proved in this block; it only sets up these definitions.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TriangularEnergy.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TriangularEnergy.lean; bytes 16..2143
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators Topology ENNReal
open Classical Filter

namespace TriangularUniversal

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def LocallyFinite (C : Set Plane) : Prop :=
  ∀ R : ℝ, (C ∩ Metric.closedBall (0 : Plane) R).Finite

def diskPoints (C : Set Plane) (R : ℝ) : Finset Plane :=
  if h : (C ∩ Metric.closedBall (0 : Plane) R).Finite then h.toFinset else ∅

def diskCount (C : Set Plane) (R : ℝ) : ℕ := (diskPoints C R).card

def DensityOne (C : Set Plane) : Prop :=
  Tendsto (fun R : ℝ => (diskCount C R : ℝ) / (Real.pi * R ^ 2))
    atTop (𝓝 1)

def AdmissiblePotential (g : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) g (Set.Ioi 0) ∧
  (∀ t : ℝ, 0 < t → 0 ≤ g t) ∧
  ∀ (r : ℕ) (t : ℝ), 0 < t → 0 ≤ (-1 : ℝ) ^ r * iteratedDeriv r g t

def diskEnergy (g : ℝ → ℝ) (C : Set Plane) (R : ℝ) : ℝ≥0∞ :=
  (diskCount C R : ℝ≥0∞)⁻¹ *
    ∑ x ∈ diskPoints C R, ∑ y ∈ (diskPoints C R).erase x,
      ENNReal.ofReal (g (‖x - y‖ ^ 2))

def energy (g : ℝ → ℝ) (C : Set Plane) : ℝ≥0∞ :=
  Filter.liminf (diskEnergy g C) atTop

end TriangularUniversal

namespace AtomicTriangular

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def b : ℝ := Real.sqrt 3 / 2

def triangularPoint (jk : ℤ × ℤ) : Plane :=
  (Real.sqrt b)⁻¹ •
    (EuclideanSpace.single 0 ((jk.1 : ℝ) + (jk.2 : ℝ) / 2) +
      EuclideanSpace.single 1 ((jk.2 : ℝ) * b))

def A : Set Plane := Set.range triangularPoint

abbrev LocallyFinite := TriangularUniversal.LocallyFinite
abbrev diskPoints := TriangularUniversal.diskPoints
abbrev diskCount := TriangularUniversal.diskCount
abbrev DensityOne := TriangularUniversal.DensityOne
abbrev AdmissiblePotential := TriangularUniversal.AdmissiblePotential
abbrev diskEnergy := TriangularUniversal.diskEnergy
abbrev energy := TriangularUniversal.energy

/-- The full nonzero-lattice energy, allowing a divergent series. -/
def latticeEnergy (g : ℝ → ℝ) : ℝ≥0∞ :=
  ∑' a : {x : Plane // x ∈ A ∧ x ≠ 0}, ENNReal.ofReal (g (‖a.val‖ ^ 2))



end AtomicTriangular
end
end OAI


