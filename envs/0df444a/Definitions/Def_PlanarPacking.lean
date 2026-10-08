-- Prove2me | Definitions.Def_PlanarPacking
-- name    : PlanarPacking
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:41.516902+00:00
-- url     : https://prove2.me/theorems/6450b9a1-7894-4bd7-a2d8-2aa66cb0367c
-- statement:
--   The block fixes the Euclidean plane Plane = ℝ² and three notions for real functions on it. Radial(f) means that f x = f y whenever ‖x‖ = ‖y‖, so f depends only on the distance from the origin. The Fourier transform fourier(f)(ξ) is the integral over the plane of f(x)·exp(−2πi⟪x,ξ⟫) dx, a complex number, using the Lebesgue (volume) measure. For a Schwartz function f on the plane, SharpCertificate(f) is a defined proposition, described as a normalized sharp certificate for disks of radius one half, asserting five conditions together: f is radial; the Fourier transform at 0 equals 1; f(0) = 2/√3; for every ξ, the Fourier transform of f at ξ has imaginary part 0 and nonnegative real part; and f(x) ≤ 0 for every x with ‖x‖ ≥ 1. No theorem about the existence of such an f or any packing consequence is stated in the block.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PlanarPacking.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PlanarPacking.lean; bytes 16..1013
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-!
# A sharp Fourier certificate for planar circle packing

The normalization and Fourier convention are those of
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open MeasureTheory

namespace SharpPlanar

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Radiality of a real function on the Euclidean plane. -/
def Radial (f : Plane → ℝ) : Prop :=
  ∀ x y, ‖x‖ = ‖y‖ → f x = f y

/-- Fourier transformation with kernel `exp (-2πi⟪x, ξ⟫)`. -/
noncomputable def fourier (f : Plane → ℝ) (ξ : Plane) : ℂ :=
  ∫ x : Plane, (f x : ℂ) *
    Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I)

/-- A normalized sharp certificate for disks of radius one half. -/
def SharpCertificate (f : SchwartzMap Plane ℝ) : Prop :=
  Radial f ∧ fourier f 0 = 1 ∧ f 0 = 2 / Real.sqrt 3 ∧
    (∀ ξ, (fourier f ξ).im = 0 ∧ 0 ≤ (fourier f ξ).re) ∧
    (∀ x, 1 ≤ ‖x‖ → f x ≤ 0)

end SharpPlanar



end OAI


