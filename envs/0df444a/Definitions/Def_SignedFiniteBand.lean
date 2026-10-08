-- Prove2me | Definitions.Def_SignedFiniteBand
-- name    : SignedFiniteBand
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:21.509441+00:00
-- url     : https://prove2.me/theorems/fbf1984e-4fe4-4180-9551-b76d060e7cee
-- statement:
--   On the Euclidean plane ℝ², diskAverage(f,x,r) is the integral of f over the open ball of radius r about x divided by πr². For a smooth test function φ, testPartial(φ,i,x) is its ith coordinate partial derivative at x. HasWeakGradient(f,g) says that a vector-valued g is a distributional gradient of f: for every compactly supported C^∞ function φ and each coordinate i∈{0,1}, ∫ f·∂ᵢφ = −∫ gᵢ·φ over the whole plane. gradientNorm(g) is the integral over the plane of the Euclidean norm ‖g(x)‖. signedBand(f,a,b)(x) is the supremum of the disk averages diskAverage(f,x,r) over all real radii r in the closed interval [a,b], endpoints included; no absolute value is taken. SignedFiniteBandStatement is a defined proposition, not an established theorem. It asserts that there is a constant C≥0 such that for every compactly supported C^∞ function f on the plane, every a>0 and every natural number m, the function signedBand(f,a,2^m·a) is locally integrable and has an integrable weak gradient G with gradientNorm(G) ≤ C·gradientNorm(∇f). The constant C does not depend on f, a or m.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SignedFiniteBand.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SignedFiniteBand.lean; bytes 16..1623
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

namespace SignedDisk

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff

namespace CenteredDiskEndpoint

/-- The Euclidean plane, with its Euclidean norm. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

def diskAverage (f : Plane → ℝ) (x : Plane) (r : ℝ) : ℝ :=
  (∫ y in Metric.ball x r, f y) / (Real.pi * r ^ 2)

/-- The i-th coordinate derivative of a smooth test function. -/
def testPartial (φ : Plane → ℝ) (i : Fin 2) (x : Plane) : ℝ :=
  fderiv ℝ φ x (EuclideanSpace.single i 1)

/-- Distributional first derivatives represented by a vector-valued function. -/
def HasWeakGradient (f : Plane → ℝ) (g : Plane → Plane) : Prop :=
  ∀ (φ : Plane → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
    ∀ i : Fin 2, (∫ x, f x * testPartial φ i x) = -∫ x, g x i * φ x

/-- The gradient L1 norm in Euclidean norm. -/
def gradientNorm (g : Plane → Plane) : ℝ := ∫ x, ‖g x‖

/-- Signed envelope over all real radii in the closed band, including its endpoints. -/
def signedBand (f : Plane → ℝ) (a b : ℝ) (x : Plane) : ℝ :=
  sSup ((fun r => diskAverage f x r) '' Icc a b)

def SignedFiniteBandStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (f : Plane → ℝ), ContDiff ℝ ∞ f → HasCompactSupport f →
    ∀ (a : ℝ), 0 < a → ∀ m : ℕ,
      LocallyIntegrable (signedBand f a ((2 : ℝ)^m * a)) ∧
      ∃ G : Plane → Plane, Integrable G ∧
        HasWeakGradient (signedBand f a ((2 : ℝ)^m * a)) G ∧
        gradientNorm G ≤ C * gradientNorm (gradient f)



end CenteredDiskEndpoint
end SignedDisk
end
end OAI


