-- Prove2me | Definitions.Def_SourceProof_4090f5760db323e17cd5fcca
-- name    : SourceProof_4090f5760db323e17cd5fcca
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:56:22.166096+00:00
-- url     : https://prove2.me/theorems/d46264cb-4ce4-427d-929c-88996af2b4ff
-- title:
--   LevyStochCalc source module: SourceProof_4090f5760db323e17cd5fcca
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Martingale.brownian_martingale_rightCont` comes from the `LevyStochCalc.Brownian.MartingaleRightCont` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_MartingaleQuadVar_F001
import Definitions.Def_SourceProof_35156ff6984aa5b4b399bdef
import Definitions.Def_SourceProof_650b7098f620aa4310e44016

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian motion under the right-continuous natural filtration

The martingale property of Brownian motion passes to the right-continuation `ℱ₊` of its natural
filtration `ℱ`, `ℱ₊ t = ⨅ s > t, ℱ s` (no null sets are added), and `ℱ₊` is itself
right-continuous; the passage uses the right `L²`-continuity `𝔼|W_r − W_s|² = r − s → 0` of the
time slices.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Martingale

universe u

section RightContinuous
variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_4090f5760db323e17cd5fcca
    {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) :
    MeasureTheory.Martingale (fun t : ℝ => W.W t)
      (LevyStochCalc.Brownian.Martingale.naturalFiltration W).rightCont P := by
  refine _root_.Prove2MeSourceProof.h_35156ff6984aa5b4b399bdef
    (_root_.Prove2MeSourceProof.h_a157dd277ff36750db5f28f0 W) fun s => ?_
  rcases le_or_gt 0 s with hs | hs
  · have hsq : ∀ r, s < r → ∫⁻ ω, (‖W.W r ω - W.W s ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        = ENNReal.ofReal (r - s) := by
      intro r hsr
      have h_meas_diff : Measurable (fun ω => W.W r ω - W.W s ω) :=
        (W.measurable_eval r).sub (W.measurable_eval s)
      have h_int : MeasureTheory.Integrable (fun ω => (W.W r ω - W.W s ω) ^ 2) P :=
        ((_root_.Prove2MeSourceProof.h_650b7098f620aa4310e44016 W r).sub (_root_.Prove2MeSourceProof.h_650b7098f620aa4310e44016 W s)).integrable_sq
      have h_mom : ∫ ω, (W.W r ω - W.W s ω) ^ 2 ∂P = r - s := by
        rw [← MeasureTheory.integral_map h_meas_diff.aemeasurable
          (by fun_prop : MeasureTheory.AEStronglyMeasurable (fun x : ℝ => x ^ 2)
            (P.map (fun ω => W.W r ω - W.W s ω))),
          W.increment_gaussian hs hsr]
        exact LevyStochCalc.Brownian.Martingale.gaussianReal_second_moment (⟨r - s, by linarith⟩ : NNReal)
      rw [← h_mom, MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int
        (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
      refine lintegral_congr fun ω => ?_
      rw [show (‖W.W r ω - W.W s ω‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖W.W r ω - W.W s ω‖ from
        (ofReal_norm _).symm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
    have h2 : Filter.Tendsto (fun r => MeasureTheory.eLpNorm (W.W r - W.W s) 2 P)
        (nhdsWithin s (Set.Ioi s)) (nhds 0) := by
      have hsq' : Filter.Tendsto (fun r => MeasureTheory.eLpNorm (W.W r - W.W s) 2 P ^ (2 : ℝ))
          (nhdsWithin s (Set.Ioi s)) (nhds 0) := by
        have h0 : Filter.Tendsto (fun r => ENNReal.ofReal (r - s))
            (nhdsWithin s (Set.Ioi s)) (nhds 0) := by
          have h1 : Filter.Tendsto (fun r => r - s) (nhdsWithin s (Set.Ioi s)) (nhds 0) := by
            have := ((continuous_sub_right s).tendsto s).mono_left
              (nhdsWithin_le_nhds (s := Set.Ioi s))
            rwa [sub_self] at this
          have := (ENNReal.continuous_ofReal.tendsto 0).comp h1
          rwa [ENNReal.ofReal_zero] at this
        refine h0.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with r hr
        rw [← hsq r hr]
        have h := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral (μ := P) (p := (2 : NNReal))
          (f := W.W r - W.W s) (by norm_num)
        rw [show ((2 : NNReal) : ℝ≥0∞) = (2 : ℝ≥0∞) from by simp,
          show ((2 : NNReal) : ℝ) = (2 : ℝ) from by norm_num] at h
        rw [h]
        refine lintegral_congr fun ω => ?_
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
        rfl
      have h := hsq'.ennrpow_const ((1 : ℝ) / 2)
      rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h
      refine h.congr fun r => ?_
      rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
      (Filter.Eventually.of_forall fun r => bot_le)
      (Filter.Eventually.of_forall fun r =>
        MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
          ((_root_.Prove2MeSourceProof.h_650b7098f620aa4310e44016 W r).sub (_root_.Prove2MeSourceProof.h_650b7098f620aa4310e44016 W s)).aestronglyMeasurable)
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioo_mem_nhdsGT hs] with r hr
    symm
    refine MeasureTheory.eLpNorm_eq_zero_of_ae_zero ?_
    filter_upwards [W.negative_zero r hr.2, W.negative_zero s hs] with ω hr0 hs0
    simp [hr0, hs0]
end RightContinuous

end LevyStochCalc.Brownian.Martingale


