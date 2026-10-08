-- Prove2me | Definitions.Def_DiskMaximal
-- name    : DiskMaximal
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:08.236776+00:00
-- url     : https://prove2.me/theorems/184e810a-004c-4e0c-9981-c0d39591852d
-- statement:
--   On the Euclidean plane ℝ² with Lebesgue measure, the absolute disk average of a real-valued function f at x and radius r is (πr²)⁻¹ times the integral of |f| over the open disk centered at x, interpreted in the extended nonnegative reals. The centered disk maximal function Mf(x) is the supremum of these averages over every real radius r>0. Its real representative is obtained by converting extended values to real numbers, with infinity converted to zero. For a smooth test function φ, its ith partial derivative is its Fréchet derivative applied to the ith coordinate unit vector. A vector-valued function g is a weak gradient of f when ∫f ∂ᵢφ = −∫gᵢφ for every smooth compactly supported φ and each coordinate i. Membership in local W¹,¹ means local integrability together with the existence of a locally integrable weak gradient; the gradient norm is ∫‖g‖ using the Euclidean norm. EndpointStatement is the defined proposition that there exists a constant C≥0 such that, for every integrable f and integrable weak gradient g of f, Mf is finite almost everywhere, its real representative is locally integrable and belongs to local W¹,¹, and it has an integrable weak gradient G satisfying ∫‖G‖≤C∫‖g‖.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DiskMaximal.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DiskMaximal.lean; bytes 16..2335
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff

noncomputable section
namespace CenteredDiskEndpoint

/-- The Euclidean plane, not the product space with its max norm. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Absolute disk average, retaining possible infinite values. -/
def absoluteDiskAverage (f : Plane → ℝ) (x : Plane) (r : ℝ) : ℝ≥0∞ :=
  (∫⁻ y in Metric.ball x r, ENNReal.ofReal |f y|) /
    ENNReal.ofReal (Real.pi * r ^ 2)

/-- The actual centered disk maximal function, over every positive real radius. -/
def maximal (f : Plane → ℝ) (x : Plane) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r), absoluteDiskAverage f x r

/-- Real representative; the endpoint also asserts that `maximal f` is finite a.e. -/
def maximalReal (f : Plane → ℝ) (x : Plane) : ℝ := (maximal f x).toReal

/-- The i-th coordinate derivative of a smooth test function. -/
def testPartial (φ : Plane → ℝ) (i : Fin 2) (x : Plane) : ℝ :=
  fderiv ℝ φ x (EuclideanSpace.single i 1)

/-- Distributional first derivatives represented by a vector-valued function. -/
def HasWeakGradient (f : Plane → ℝ) (g : Plane → Plane) : Prop :=
  ∀ (φ : Plane → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
    ∀ i : Fin 2, (∫ x, f x * testPartial φ i x) = -∫ x, g x i * φ x

/-- Local W^(1,1), expressed using the same distributional gradient convention. -/
def InW11Loc (f : Plane → ℝ) : Prop :=
  LocallyIntegrable f ∧
    ∃ g : Plane → Plane, LocallyIntegrable g ∧ HasWeakGradient f g

/-- The gradient L1 norm in Euclidean norm. -/
def gradientNorm (g : Plane → Plane) : ℝ := ∫ x, ‖g x‖

/-- Exact endpoint, including finiteness before passing to the real representative.
Quantifying the input gradient makes the norm bound independent of a choice of
representative of its weak derivatives. -/
def EndpointStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (f : Plane → ℝ) (g : Plane → Plane),
      Integrable f → Integrable g → HasWeakGradient f g →
      (∀ᵐ x, maximal f x ≠ ⊤) ∧
      LocallyIntegrable (maximalReal f) ∧
      InW11Loc (maximalReal f) ∧
      ∃ G : Plane → Plane, Integrable G ∧
        HasWeakGradient (maximalReal f) G ∧ gradientNorm G ≤ C * gradientNorm g



end CenteredDiskEndpoint
end
end OAI


