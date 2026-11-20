-- Prove2me | Definitions.Def_SourceProof_9d62612e2dce26cbc374ccfb
-- name    : SourceProof_9d62612e2dce26cbc374ccfb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:15:09.743679+00:00
-- url     : https://prove2.me/theorems/c0ccd692-bf27-4df4-8f0f-a87ec6002ae9
-- title:
--   LevyStochCalc source module: SourceProof_9d62612e2dce26cbc374ccfb
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.lintegral_count_eq_referenceIntensity` comes from the `LevyStochCalc.Poisson.CompensatedIsometry` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Batteries.Tactic.OpenPrivate
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometry_F000

open private poissonMeasure_integral_id from Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometry_F000
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Second moments and L²-isometry of the simple compensated-Poisson integral

The mean-zero / second-moment (variance) identities for the compensated Poisson
measure `Ñ(B) = N(B) − ν̂(B)`, and the diagonal / off-diagonal computation for
`simpleIntegral` (orthogonality of disjoint compensated-Poisson increments) that
they feed, culminating in the simple-integrand L²-isometry `simpleIntegral_isometry`
and L²-membership `simpleIntegral_memLp_compensated`. Builds on the integrand
definitions in `Poisson/CompensatedSimple.lean`.

This module carries the moment layer: the factorial-series identities
`∑' n, rⁿ / n! · n = r · exp r` and `∑' n, rⁿ / n! · n² = (r² + r) · exp r`, the mean,
second moment and variance of `poissonMeasure r` they give, and the transport of these
along `poisson_law` to `Ñ(B)`.

## Downstream modules

* `LevyStochCalc.Poisson.CompensatedIsometryOrthogonality` — the diagonal identity
  `∫⁻ ‖ξ_i · Ñ(B_i)‖² ∂P = ν̂(B_i) · ∫⁻ ‖ξ_i‖² ∂P` and the off-diagonal vanishing
  `∫ (ξ_i · Ñ(B_i)) · (ξ_j · Ñ(B_j)) ∂P = 0` for `i < j`.
* `LevyStochCalc.Poisson.CompensatedIsometryL2` — the Bochner expansion of
  `(∑_i ξ_i · Ñ(B_i))²`, the isometry `simpleIntegral_isometry` with its sum form, and
  the membership `simpleIntegral_memLp_compensated`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]


theorem _root_.Prove2MeSourceProof.h_9d62612e2dce26cbc374ccfb
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B)
    (h_finite : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤) :
    ∫⁻ ω, N.N ω B ∂P = LevyStochCalc.Poisson.referenceIntensity ν B := by
  set r : ℝ≥0 := (LevyStochCalc.Poisson.referenceIntensity ν B).toNNReal with hr_def
  have h_NB_meas : Measurable (fun ω => N.N ω B) := N.measurable_eval hB
  have h_int_id : MeasureTheory.Integrable
      (fun n : ℕ => (n : ℝ)) (ProbabilityTheory.poissonMeasure r) := by
    rw [ProbabilityTheory.integrable_poissonMeasure_iff]
    have h_norm : ∀ n : ℕ, ‖((n : ℝ))‖ = (n : ℝ) := fun n => by
      rw [Real.norm_eq_abs]; exact abs_of_nonneg (Nat.cast_nonneg n)
    simp_rw [h_norm]
    have h_eq : ∀ n : ℕ,
        Real.exp (-(↑r : ℝ)) * (↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)
        = Real.exp (-(↑r : ℝ))
          * ((↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)) := by
      intro n; ring
    simp_rw [h_eq]
    exact (LevyStochCalc.Poisson.Compensated.summable_pow_div_factorial_mul_nat (↑r)).mul_left _
  have hmap : ∫⁻ x, x ∂(P.map (fun ω => N.N ω B)) = ∫⁻ ω, N.N ω B ∂P :=
    lintegral_map (f := fun x : ℝ≥0∞ => x) measurable_id' h_NB_meas
  rw [← hmap, N.poisson_law hB h_finite]
  change ∫⁻ x, x ∂((ProbabilityTheory.poissonMeasure r).map (fun n : ℕ => (n : ℝ≥0∞))) = _
  rw [lintegral_map (f := fun x : ℝ≥0∞ => x) measurable_id' measurable_from_nat]
  have hcast : (fun n : ℕ => ((n : ℝ≥0∞))) = fun n : ℕ => ENNReal.ofReal ((n : ℝ)) := by
    funext n
    rw [ENNReal.ofReal_natCast]
  rw [hcast, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_id
    (Filter.Eventually.of_forall fun n => Nat.cast_nonneg n), poissonMeasure_integral_id,
    ENNReal.ofReal_coe_nnreal, hr_def, ENNReal.coe_toNNReal h_finite]
end LevyStochCalc.Poisson.Compensated


