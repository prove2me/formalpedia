-- Prove2me | Definitions.Def_SourceProof_e0e24eaf49ef31dab57f4745
-- name    : SourceProof_e0e24eaf49ef31dab57f4745
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:27:18.542676+00:00
-- url     : https://prove2.me/theorems/9a31a4a0-a85a-465d-9190-2eef17e8df42
-- title:
--   LevyStochCalc source module: SourceProof_e0e24eaf49ef31dab57f4745
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.compensated_sq_integrable` comes from the `LevyStochCalc.Poisson.CompensatedIsometry` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometry_F001

open private integrable_id_poissonMeasure integrable_id_sq_poissonMeasure from Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometry_F001
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


theorem _root_.Prove2MeSourceProof.h_e0e24eaf49ef31dab57f4745
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B)
    (h_finite : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤) :
    MeasureTheory.Integrable (fun ω => (N.compensated B ω)^2) P := by
  set c : ℝ := (LevyStochCalc.Poisson.referenceIntensity ν B).toReal with hc_def
  set r : ℝ≥0 := (LevyStochCalc.Poisson.referenceIntensity ν B).toNNReal with hr_def
  have h_c_eq_r : c = (r : ℝ) := by
    rw [hc_def, hr_def, ENNReal.coe_toNNReal_eq_toReal]
  have h_NB_meas : Measurable (fun ω => N.N ω B) := N.measurable_eval hB
  have h_meas_phi_sq : Measurable (fun x : ℝ≥0∞ => (x.toReal - c)^2) :=
    (ENNReal.measurable_toReal.sub_const _).pow_const 2
  -- (compensated B)² = ((·).toReal - c)² ∘ (N.N · B). Lift through pushforwards.
  rw [show (fun ω => (N.compensated B ω)^2) =
      (fun x : ℝ≥0∞ => (x.toReal - c)^2) ∘ (fun ω => N.N ω B) from rfl]
  -- Step 1: convert Integrable (g ∘ f) P → Integrable g (P.map f) via the iff.
  rw [← MeasureTheory.integrable_map_measure (μ := P) (f := fun ω => N.N ω B)
      h_meas_phi_sq.aestronglyMeasurable h_NB_meas.aemeasurable]
  -- Step 2: replace P.map with poissonMeasureENN via poisson_law.
  rw [N.poisson_law hB h_finite]
  -- Step 3: unfold poissonMeasureENN = (poissonMeasure r).map Nat.cast.
  change MeasureTheory.Integrable (fun x : ℝ≥0∞ => (x.toReal - c)^2)
    ((ProbabilityTheory.poissonMeasure r).map (fun n : ℕ => (n : ℝ≥0∞)))
  -- Step 4: convert Integrable g (μ.map f) → Integrable (g ∘ f) μ.
  rw [MeasureTheory.integrable_map_measure
      (μ := ProbabilityTheory.poissonMeasure r) (f := fun n : ℕ => (n : ℝ≥0∞))
      h_meas_phi_sq.aestronglyMeasurable measurable_from_nat.aemeasurable]
  -- Now goal: Integrable ((fun x => (x.toReal - c)^2) ∘ Nat.cast) (poissonMeasure r)
  -- Simplify (↑n : ℝ≥0∞).toReal = (n : ℝ); use c = (r : ℝ).
  have h_simp : ((fun x : ℝ≥0∞ => (x.toReal - c)^2) ∘ (fun n : ℕ => (n : ℝ≥0∞)))
              = fun n : ℕ => ((n : ℝ) - (r : ℝ))^2 := by
    funext n
    change (((n : ℝ≥0∞)).toReal - c)^2 = ((n : ℝ) - (r : ℝ))^2
    rw [show ((n : ℝ≥0∞)).toReal = (n : ℝ) from by simp, h_c_eq_r]
  rw [h_simp]
  -- Expand (n - r)² = (n² - 2rn) + r².
  have h_eq : (fun n : ℕ => ((n : ℝ) - (r : ℝ))^2)
            = fun n : ℕ => (((n : ℝ)^2) - (2 * (r : ℝ) * (n : ℝ))) + (r : ℝ)^2 := by
    funext n; ring
  rw [h_eq]
  have h_int_n := integrable_id_poissonMeasure r
  have h_int_nsq := integrable_id_sq_poissonMeasure r
  have h_int_const : MeasureTheory.Integrable
      (fun _ : ℕ => (r : ℝ)^2) (ProbabilityTheory.poissonMeasure r) :=
    MeasureTheory.integrable_const _
  have h_int_2rn : MeasureTheory.Integrable
      (fun n : ℕ => 2 * (r : ℝ) * (n : ℝ)) (ProbabilityTheory.poissonMeasure r) :=
    h_int_n.const_mul (2 * (r : ℝ))
  exact (h_int_nsq.sub h_int_2rn).add h_int_const
end LevyStochCalc.Poisson.Compensated


