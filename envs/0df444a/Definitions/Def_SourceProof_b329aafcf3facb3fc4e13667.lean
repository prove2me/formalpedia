-- Prove2me | Definitions.Def_SourceProof_b329aafcf3facb3fc4e13667
-- name    : SourceProof_b329aafcf3facb3fc4e13667
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:25:27.171713+00:00
-- url     : https://prove2.me/theorems/26e29146-bf91-461e-9561-7e9238ec8143
-- title:
--   LevyStochCalc source module: SourceProof_b329aafcf3facb3fc4e13667
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.compensated_second_moment` comes from the `LevyStochCalc.Poisson.CompensatedIsometry` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometry_F001

open private poissonMeasure_variance from Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometry_F001
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
theorem _root_.Prove2MeSourceProof.h_b329aafcf3facb3fc4e13667
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B)
    (h_finite : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤) :
    ∫ ω, (N.compensated B ω)^2 ∂P
      = (LevyStochCalc.Poisson.referenceIntensity ν B).toReal := by
  set c : ℝ := (LevyStochCalc.Poisson.referenceIntensity ν B).toReal with hc_def
  set r : ℝ≥0 := (LevyStochCalc.Poisson.referenceIntensity ν B).toNNReal with hr_def
  have h_c_eq_r : c = (r : ℝ) := by
    rw [hc_def, hr_def, ENNReal.coe_toNNReal_eq_toReal]
  have h_NB_meas : Measurable (fun ω => N.N ω B) := N.measurable_eval hB
  have h_meas_phi : Measurable (fun x : ℝ≥0∞ => (x.toReal - c)^2) :=
    (ENNReal.measurable_toReal.sub_const _).pow_const 2
  -- (Ñ(B,ω))² = ((·).toReal - c)² ∘ (N.N · B)
  have h_compensated_sq_eq : (fun ω => (N.compensated B ω)^2) =
      (fun x : ℝ≥0∞ => (x.toReal - c)^2) ∘ (fun ω => N.N ω B) := by
    funext ω; rfl
  rw [h_compensated_sq_eq]
  rw [show (∫ ω, ((fun x : ℝ≥0∞ => (x.toReal - c)^2) ∘ (fun ω => N.N ω B)) ω ∂P)
      = ∫ x, (x.toReal - c)^2 ∂(P.map (fun ω => N.N ω B)) from
    (MeasureTheory.integral_map h_NB_meas.aemeasurable
      h_meas_phi.aestronglyMeasurable).symm]
  rw [N.poisson_law hB h_finite]
  change ∫ x, (x.toReal - c)^2 ∂((ProbabilityTheory.poissonMeasure r).map
    (fun n : ℕ => (n : ℝ≥0∞))) = c
  rw [MeasureTheory.integral_map measurable_from_nat.aemeasurable
    h_meas_phi.aestronglyMeasurable]
  have h_phi_cast :
      ∀ n : ℕ, (((n : ℝ≥0∞)).toReal - c) ^ 2 = ((n : ℝ) - (r : ℝ)) ^ 2 := by
    intro n
    rw [show ((n : ℝ≥0∞)).toReal = (n : ℝ) from by simp, h_c_eq_r]
  simp_rw [h_phi_cast]
  rw [poissonMeasure_variance r]
  exact h_c_eq_r.symm
end LevyStochCalc.Poisson.Compensated


