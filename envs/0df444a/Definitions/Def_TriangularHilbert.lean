-- Prove2me | Definitions.Def_TriangularHilbert
-- name    : TriangularHilbert
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:35.088506+00:00
-- url     : https://prove2.me/theorems/7e52c722-bc1f-4288-acf7-2969808e9dbb
-- statement:
--   On the plane ℝ×ℝ, an Endpoints record consists of real numbers lower and upper with 0 < lower < upper, and annulus(ε,R) is the set of real t with ε < |t| < R. For complex-valued functions F and G on the plane, the integrand at a point z=(x,y) and a real t is F(x+t,y)·G(x,y+t)/t. The truncation for endpoints E is the Lebesgue integral of this integrand over t in annulus(E.lower,E.upper). A point z is GoodPoint if for every natural number n the integrand is integrable on annulus(1/(n+2), n+2). The maximal function at z is 0 if z is not a good point, and otherwise is the supremum over all Endpoints E of the extended-nonnegative-real value of the norm of the truncation at z. The maximalNorm of the pair (F,G) is the L^{3/2} norm of this maximal function over the plane, computed as the lower integral of maximal^{3/2} raised to the power 2/3. MainEstimate is a defined proposition, not an established theorem: it asserts that there exists a constant C ≥ 0 such that for all F and G in L^3 of Lebesgue measure on the plane, almost every point is a good point, the maximal function is almost-everywhere measurable, and maximalNorm(F,G) ≤ C·‖F‖_{L^3}·‖G‖_{L^3}.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TriangularHilbert.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TriangularHilbert.lean; bytes 16..1383
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace TriangularHilbert

abbrev Plane := ℝ × ℝ

structure Endpoints where
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  lower_lt_upper : lower < upper

def annulus (ε R : ℝ) : Set ℝ := {t | ε < |t| ∧ |t| < R}

def integrand (F G : Plane → ℂ) (z : Plane) (t : ℝ) : ℂ :=
  F (z.1 + t, z.2) * G (z.1, z.2 + t) / (t : ℂ)

def truncation (F G : Plane → ℂ) (E : Endpoints) (z : Plane) : ℂ :=
  ∫ t in annulus E.lower E.upper, integrand F G z t

def GoodPoint (F G : Plane → ℂ) (z : Plane) : Prop :=
  ∀ n : ℕ, IntegrableOn (integrand F G z)
    (annulus (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2))

def maximal (F G : Plane → ℂ) (z : Plane) : ℝ≥0∞ := by
  classical
  exact if GoodPoint F G z then
    ⨆ E : Endpoints, ENNReal.ofReal ‖truncation F G E z‖ else 0

def maximalNorm (F G : Plane → ℂ) : ℝ≥0∞ :=
  (∫⁻ z : Plane, maximal F G z ^ ((3 : ℝ) / 2)) ^ ((2 : ℝ) / 3)

def MainEstimate : Prop :=
  ∃ C : ℝ≥0, ∀ F G : Plane → ℂ,
    MemLp F 3 volume → MemLp G 3 volume →
    (∀ᵐ z ∂volume, GoodPoint F G z) ∧
    AEMeasurable (maximal F G) volume ∧
    maximalNorm F G ≤ (C : ℝ≥0∞) * eLpNorm F 3 volume * eLpNorm G 3 volume

open MeasureTheory Filter
open scoped ENNReal



end TriangularHilbert
end
end OAI


