-- Prove2me | Definitions.Def_SourceProof_bfd78118d51ae0bbee2cf99f
-- name    : SourceProof_bfd78118d51ae0bbee2cf99f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T07:27:21.466794+00:00
-- url     : https://prove2.me/theorems/3735aecb-16b2-4775-8afd-57a876561d96
-- title:
--   LevyStochCalc source module: SourceProof_bfd78118d51ae0bbee2cf99f
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.simpleIntegral_diagonal_bochner` comes from the `LevyStochCalc.Brownian.ItoSimpleMoments` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_0d5475ecda5b11387d030812
import Definitions.Def_SourceProof_2ce5e97adb181ad2712fdce6

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Second moments of the terms of the elementary Brownian integral

For an adapted simple predictable integrand the diagonal term satisfies
`E[(ξ_i · ΔW_i) ^ 2] = (t_{i+1} - t_i) · E[ξ_i ^ 2]`, where
`ΔW_i = W_{t_{i+1}} - W_{t_i}`, since `ΔW_i` is independent of `ℱ_{t_i}` and centred Gaussian
with variance `t_{i+1} - t_i`, while for `i < j` the off-diagonal term vanishes,
`E[(ξ_i · ΔW_i) · (ξ_j · ΔW_j)] = 0`. Both rest on the integrability of the squared increments
and of the cross products.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_bfd78118d51ae0bbee2cf99f
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T) (i : Fin H.N)
    (h_part_nn : 0 ≤ H.partition i.castSucc)
    (h_adapt : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i)) :
    ∫ ω, (H.ξ i ω * (W.W (H.partition i.succ) ω
                    - W.W (H.partition i.castSucc) ω))^2 ∂P
      = (H.partition i.succ - H.partition i.castSucc) *
        ∫ ω, (H.ξ i ω)^2 ∂P := by
  have hst : H.partition i.castSucc < H.partition i.succ :=
    H.partition_strictMono Fin.castSucc_lt_succ
  -- Common identity.
  have h_norm_sq_eq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞)^2 = ENNReal.ofReal (x^2) := fun x => by
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from ofReal_norm x |>.symm]
    rw [← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [show ‖x‖^2 = x^2 from by rw [Real.norm_eq_abs, sq_abs]]
  have h_lint := _root_.Prove2MeSourceProof.h_2ce5e97adb181ad2712fdce6 W ℱ hℱ H i h_part_nn h_adapt
  rw [show (∫⁻ ω, (‖H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω)‖₊ : ℝ≥0∞)^2 ∂P)
        = ∫⁻ ω, ENNReal.ofReal ((H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω))^2) ∂P from
    MeasureTheory.lintegral_congr (fun ω => h_norm_sq_eq _)] at h_lint
  rw [show (∫⁻ ω, (‖H.ξ i ω‖₊ : ℝ≥0∞)^2 ∂P)
        = ∫⁻ ω, ENNReal.ofReal ((H.ξ i ω)^2) ∂P from
    MeasureTheory.lintegral_congr (fun ω => h_norm_sq_eq _)] at h_lint
  -- Integrabilities.
  obtain ⟨M, hM⟩ := H.ξ_bounded i
  have h_xi_sq_bound : ∀ ω : Ω, (H.ξ i ω)^2 ≤ M^2 := fun ω =>
    sq_le_sq' (neg_le_of_abs_le (hM ω)) (le_of_abs_le (hM ω))
  have h_int_xi_sq : MeasureTheory.Integrable (fun ω => (H.ξ i ω)^2) P := by
    refine MeasureTheory.Integrable.mono' (g := fun _ : Ω => M^2)
      (MeasureTheory.integrable_const _) ?_ ?_
    · exact ((H.ξ_measurable i).pow_const 2).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact h_xi_sq_bound ω
  have h_int_ΔW_sq : MeasureTheory.Integrable
      (fun ω => (W.W (H.partition i.succ) ω
                - W.W (H.partition i.castSucc) ω)^2) P :=
    _root_.Prove2MeSourceProof.h_0d5475ecda5b11387d030812 W h_part_nn hst
  have h_int_aN_sq : MeasureTheory.Integrable
      (fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                - W.W (H.partition i.castSucc) ω))^2) P := by
    have h_eq : ∀ ω, (H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω))^2
              = (H.ξ i ω)^2 *
                (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω)^2 := fun ω => by ring
    rw [show (fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω))^2)
            = fun ω => (H.ξ i ω)^2 *
                (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω)^2 from funext h_eq]
    refine MeasureTheory.Integrable.bdd_mul (c := M^2) h_int_ΔW_sq
      ((H.ξ_measurable i).pow_const 2).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact h_xi_sq_bound ω
  have h_nn_xi_sq : 0 ≤ᵐ[P] fun ω => (H.ξ i ω)^2 := by
    filter_upwards with ω; positivity
  have h_nn_aN_sq : 0 ≤ᵐ[P] fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω))^2 := by
    filter_upwards with ω; positivity
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_aN_sq h_nn_aN_sq] at h_lint
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_xi_sq h_nn_xi_sq] at h_lint
  -- Combine ENNReal.ofReal of constant * ofReal of integral.
  have h_xi_int_nn : 0 ≤ ∫ ω, (H.ξ i ω)^2 ∂P :=
    MeasureTheory.integral_nonneg (fun ω => sq_nonneg _)
  have h_aN_int_nn : 0 ≤ ∫ ω, (H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω))^2 ∂P :=
    MeasureTheory.integral_nonneg (fun ω => sq_nonneg _)
  have h_dt_nn : 0 ≤ H.partition i.succ - H.partition i.castSucc := sub_nonneg.mpr (le_of_lt hst)
  rw [show ENNReal.ofReal (H.partition i.succ - H.partition i.castSucc) *
          ENNReal.ofReal (∫ ω, (H.ξ i ω)^2 ∂P)
          = ENNReal.ofReal
              ((H.partition i.succ - H.partition i.castSucc) *
                ∫ ω, (H.ξ i ω)^2 ∂P) from
    (ENNReal.ofReal_mul h_dt_nn).symm] at h_lint
  have h_rhs_nn : 0 ≤ (H.partition i.succ - H.partition i.castSucc) *
                      ∫ ω, (H.ξ i ω)^2 ∂P :=
    mul_nonneg h_dt_nn h_xi_int_nn
  exact (ENNReal.ofReal_eq_ofReal_iff h_aN_int_nn h_rhs_nn).mp h_lint
end LevyStochCalc.Brownian.Ito


