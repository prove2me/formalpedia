-- Prove2me | Definitions.Def_SourceProof_cd0c957e24cb795d7143dc2e
-- name    : SourceProof_cd0c957e24cb795d7143dc2e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:09:54.169112+00:00
-- url     : https://prove2.me/theorems/d88f0157-8920-4fdb-ac7e-106f74717e09
-- title:
--   LevyStochCalc source module: SourceProof_cd0c957e24cb795d7143dc2e
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.lintegral_sq_eval_tendsto_of_diff_tendsto_zero_brownian` comes from the `LevyStochCalc.Brownian.ItoDensityUnbounded` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Batteries.Tactic.OpenPrivate
import Definitions.Def_LevyStochCalc_Brownian_ItoDensityUnbounded_F000

open private eLpNorm_tendsto_of_eLpNorm_sub_tendsto_zero from Definitions.Def_LevyStochCalc_Brownian_ItoDensityUnbounded_F000
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Density of the simple predictable processes in `L²`

Removal of the boundedness restriction by truncation: the `eLpNorm`/`lintegral`
dictionary on the product measure, and the density results `simplePredictable_dense_L2`
and `adaptedSimple_dense_L2_brownian` for an arbitrary square-integrable integrand.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_cd0c957e24cb795d7143dc2e
    {μ : Measure Ω} [SFinite μ]
    {T : ℝ}
    (H : Ω → ℝ → ℝ) (h_H_meas : Measurable (Function.uncurry H))
    (ev : ℕ → ℝ → Ω → ℝ)
    (h_ev_meas : ∀ n, Measurable (fun (p : Ω × ℝ) => ev n p.2 p.1))
    (h_L2_diff : Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - ev n s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖ev n s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ)
      Filter.atTop
      (nhds (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ)) := by
  set μν := μ.prod (volume.restrict (Set.Icc (0 : ℝ) T)) with hμν
  set F : Ω × ℝ → ℝ := fun p => H p.1 p.2 with hF_def
  set Fn : ℕ → Ω × ℝ → ℝ := fun n p => ev n p.2 p.1 with hFn_def
  have h_F_meas : Measurable F := h_H_meas
  have h_Fn_meas : ∀ n, Measurable (Fn n) := h_ev_meas
  have h_F_aestrong : MeasureTheory.AEStronglyMeasurable F μν :=
    h_F_meas.stronglyMeasurable.aestronglyMeasurable
  have h_Fn_aestrong : ∀ n, MeasureTheory.AEStronglyMeasurable (Fn n) μν :=
    fun n => (h_Fn_meas n).stronglyMeasurable.aestronglyMeasurable
  have h_diff_meas : ∀ n, Measurable (F - Fn n) := fun n => h_F_meas.sub (h_Fn_meas n)
  -- Bridge each lintegral_sq form to its eLpNorm² counterpart.
  have h_F_bridge : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ
        = MeasureTheory.eLpNorm F 2 μν ^ (2 : ℝ) :=
    LevyStochCalc.Brownian.Ito.lintegral_sq_eq_eLpNorm_sq_on_prod_brownian (μ := μ) F h_F_meas
  have h_Fn_bridge : ∀ n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖ev n s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ
        = MeasureTheory.eLpNorm (Fn n) 2 μν ^ (2 : ℝ) := fun n =>
    LevyStochCalc.Brownian.Ito.lintegral_sq_eq_eLpNorm_sq_on_prod_brownian (μ := μ) (Fn n) (h_Fn_meas n)
  have h_diff_bridge : ∀ n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s - ev n s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ
        = MeasureTheory.eLpNorm (F - Fn n) 2 μν ^ (2 : ℝ) := fun n =>
    LevyStochCalc.Brownian.Ito.lintegral_sq_eq_eLpNorm_sq_on_prod_brownian (μ := μ) (T := T)
      (F - Fn n) (h_diff_meas n)
  -- Convert L²-converges (lintegral form) into eLpNorm² → 0.
  have h_eLpNorm_sq_diff_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (F - Fn n) 2 μν ^ (2 : ℝ))
      Filter.atTop (nhds 0) := by
    have h_eq : (fun n => MeasureTheory.eLpNorm (F - Fn n) 2 μν ^ (2 : ℝ))
        = (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖H ω s - ev n s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ) := by
      funext n
      exact (h_diff_bridge n).symm
    rw [h_eq]
    exact h_L2_diff
  -- Square root: eLpNorm² → 0 ⟹ eLpNorm → 0 (via rpow continuity at 0).
  have h_eLpNorm_diff_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (F - Fn n) 2 μν)
      Filter.atTop (nhds 0) := by
    have h_rpow : (fun n => MeasureTheory.eLpNorm (F - Fn n) 2 μν)
        = (fun n => (MeasureTheory.eLpNorm (F - Fn n) 2 μν ^ (2 : ℝ)) ^ ((1 / 2 : ℝ))) := by
      funext n
      rw [← ENNReal.rpow_mul, show ((2 : ℝ) * (1 / 2)) = 1 from by norm_num,
          ENNReal.rpow_one]
    rw [h_rpow]
    have h := h_eLpNorm_sq_diff_tendsto.ennrpow_const (1 / 2 : ℝ)
    simpa [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using h
  -- Reverse triangle continuity: eLpNorm (Fn n - F) → 0 ⟹ eLpNorm Fn n → eLpNorm F.
  have h_diff_swap : ∀ n,
      MeasureTheory.eLpNorm (Fn n - F) 2 μν
        = MeasureTheory.eLpNorm (F - Fn n) 2 μν := by
    intro n
    have h_neg : Fn n - F = -(F - Fn n) := by ext p; simp [sub_eq_neg_add]
    rw [h_neg, MeasureTheory.eLpNorm_neg]
  have h_eLpNorm_diff_swap_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (Fn n - F) 2 μν)
      Filter.atTop (nhds 0) := by
    have h_eq : (fun n => MeasureTheory.eLpNorm (Fn n - F) 2 μν)
        = (fun n => MeasureTheory.eLpNorm (F - Fn n) 2 μν) := funext h_diff_swap
    rw [h_eq]
    exact h_eLpNorm_diff_tendsto
  have h_eLpNorm_Fn_tendsto :=
    eLpNorm_tendsto_of_eLpNorm_sub_tendsto_zero
      (one_le_two : (1 : ℝ≥0∞) ≤ 2) h_F_aestrong h_Fn_aestrong h_eLpNorm_diff_swap_tendsto
  -- Square back: eLpNorm Fn n → eLpNorm F ⟹ eLpNorm² Fn n → eLpNorm² F.
  have h_eLpNorm_sq_Fn_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (Fn n) 2 μν ^ (2 : ℝ))
      Filter.atTop (nhds (MeasureTheory.eLpNorm F 2 μν ^ (2 : ℝ))) :=
    h_eLpNorm_Fn_tendsto.ennrpow_const 2
  -- Convert back to lintegral form via the bridges.
  have h_eq_func : (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖ev n s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ)
      = (fun n => MeasureTheory.eLpNorm (Fn n) 2 μν ^ (2 : ℝ)) := funext h_Fn_bridge
  rw [h_eq_func, h_F_bridge]
  exact h_eLpNorm_sq_Fn_tendsto
-- maxHeartbeats: triangle-inequality lift through nested lintegrals + Tonelli.

-- maxHeartbeats: triangle-inequality lift through nested lintegrals + Tonelli.

end LevyStochCalc.Brownian.Ito


