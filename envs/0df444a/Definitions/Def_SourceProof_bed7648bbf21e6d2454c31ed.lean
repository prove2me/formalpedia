-- Prove2me | Definitions.Def_SourceProof_bed7648bbf21e6d2454c31ed
-- name    : SourceProof_bed7648bbf21e6d2454c31ed
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:18:43.208342+00:00
-- url     : https://prove2.me/theorems/4594e936-bc27-4927-9999-af9116971472
-- title:
--   LevyStochCalc source module: SourceProof_bed7648bbf21e6d2454c31ed
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.compensated_mean_zero` comes from the `LevyStochCalc.Poisson.CompensatedIsometry` module. The staged Lean declaration includes its source proof and dependency references.
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

set_option maxHeartbeats 400000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.

theorem _root_.Prove2MeSourceProof.h_bed7648bbf21e6d2454c31ed
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B)
    (h_finite : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤) :
    ∫ ω, N.compensated B ω ∂P = 0 := by
  set c : ℝ := (LevyStochCalc.Poisson.referenceIntensity ν B).toReal with hc_def
  set r : ℝ≥0 := (LevyStochCalc.Poisson.referenceIntensity ν B).toNNReal with hr_def
  have h_c_eq_r : c = (r : ℝ) := by
    rw [hc_def, hr_def, ENNReal.coe_toNNReal_eq_toReal]
  have h_NB_meas : Measurable (fun ω => N.N ω B) := N.measurable_eval hB
  -- compensated B ω = (·.toReal - c) ∘ (N.N · B)
  have h_compensated_eq : (fun ω => N.compensated B ω) =
      (fun x : ℝ≥0∞ => x.toReal - c) ∘ (fun ω => N.N ω B) := by
    funext ω
    rfl
  rw [h_compensated_eq]
  -- Pushforward via integral_map
  rw [show (∫ ω, ((fun x : ℝ≥0∞ => x.toReal - c) ∘ (fun ω => N.N ω B)) ω ∂P)
      = ∫ x, (x.toReal - c) ∂(P.map (fun ω => N.N ω B)) from
    (MeasureTheory.integral_map h_NB_meas.aemeasurable
      (ENNReal.measurable_toReal.sub_const _).aestronglyMeasurable).symm]
  -- Apply poisson_law
  rw [N.poisson_law hB h_finite]
  -- Unfold poissonMeasureENN
  change ∫ x, (x.toReal - c) ∂((ProbabilityTheory.poissonMeasure r).map
    (fun n : ℕ => (n : ℝ≥0∞))) = 0
  rw [MeasureTheory.integral_map measurable_from_nat.aemeasurable
    (ENNReal.measurable_toReal.sub_const _).aestronglyMeasurable]
  -- Simplify the cast (n : ℝ≥0∞).toReal = (n : ℝ)
  have h_phi_cast : ∀ n : ℕ, ((n : ℝ≥0∞)).toReal - c = (n : ℝ) - c := by
    intro n
    rw [show ((n : ℝ≥0∞)).toReal = (n : ℝ) from by simp]
  simp_rw [h_phi_cast]
  -- Now goal: ∫ n, (n : ℝ) - c ∂(poissonMeasure r) = 0
  -- Establish integrability of (n : ℝ) w.r.t. poissonMeasure r
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
  have h_int_const : MeasureTheory.Integrable
      (fun _ : ℕ => c) (ProbabilityTheory.poissonMeasure r) :=
    MeasureTheory.integrable_const _
  rw [MeasureTheory.integral_sub h_int_id h_int_const]
  rw [poissonMeasure_integral_id, MeasureTheory.integral_const]
  -- Goal: (↑r : ℝ) - (Measure.real (poissonMeasure r) Set.univ) • c = 0
  rw [show ((ProbabilityTheory.poissonMeasure r).real Set.univ : ℝ) = 1 from by
    rw [MeasureTheory.measureReal_def]
    simp [MeasureTheory.measure_univ]]
  rw [← h_c_eq_r]
  simp
end LevyStochCalc.Poisson.Compensated


