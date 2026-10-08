-- Prove2me | Definitions.Def_SubpolynomialLp
-- name    : SubpolynomialLp
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:27.275922+00:00
-- url     : https://prove2.me/theorems/22136206-75a2-4769-aad4-97b15fd17393
-- statement:
--   For a real exponent p and vectors x, y in R^d indexed by Fin d, coordinateDistance(p,x,y) is the ℓ^p-type expression (Σ_a |x_a − y_a|^p)^(1/p), with no assumption in the definition that p ≥ 1. GoodDimension(p,n,D,d) is a proposition saying that, for every measurable space Ω (in the fixed universe u) with a measure μ, and every injective family x of n points of Lp(μ) taken with exponent ENNReal.ofReal(p), there exist n points y_i in R^d and a scale s > 0 such that for all indices i and j, s·‖x_i − x_j‖ ≤ coordinateDistance(p, y_i, y_j) ≤ D·s·‖x_i − x_j‖; that is, the n points embed into d-dimensional coordinate space with distortion at most D up to rescaling. dimension(p,n,D) is the natural number given by the infimum (sInf) of all d for which GoodDimension holds, so it is the least such d when that set is nonempty, and the Lean convention sInf ∅ = 0 would apply otherwise. Finally gamma(p) is the real number 2 − p if p < 2, and 1 − 2/p otherwise.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SubpolynomialLp.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SubpolynomialLp.lean; bytes 16..1082
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
universe u

namespace SubpolynomialLp

def coordinateDistance (p : ℝ) {d : ℕ} (x y : Fin d → ℝ) : ℝ :=
  (∑ a, |x a - y a| ^ p) ^ (1 / p)

/-- The universal property used in the definition of d_p(n,D). -/
def GoodDimension (p : ℝ) (n : ℕ) (D : ℝ) (d : ℕ) : Prop :=
  ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ)
    (x : Fin n → @Lp Ω ℝ mΩ _ (ENNReal.ofReal p) μ),
    Function.Injective x →
    ∃ (y : Fin n → Fin d → ℝ) (s : ℝ), 0 < s ∧
      ∀ i j, s * ‖x i - x j‖ ≤ coordinateDistance p (y i) (y j) ∧
        coordinateDistance p (y i) (y j) ≤ D * s * ‖x i - x j‖

/-- The least universal coordinate dimension. The theorem also asserts that
this least dimension has the defining property, ruling out an empty infimum. -/
def dimension (p : ℝ) (n : ℕ) (D : ℝ) : ℕ :=
  sInf {d : ℕ | GoodDimension.{u} p n D d}

def gamma (p : ℝ) : ℝ := if p < 2 then 2 - p else 1 - 2 / p



end SubpolynomialLp
end
end OAI


