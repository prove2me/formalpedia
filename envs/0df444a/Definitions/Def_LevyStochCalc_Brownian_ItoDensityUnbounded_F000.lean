-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoDensityUnbounded_F000
-- name    : LevyStochCalc_Brownian_ItoDensityUnbounded_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:44:56.736251+00:00
-- url     : https://prove2.me/theorems/27d15322-452e-4ff0-8b1b-62caa157f947
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoDensityUnbounded
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoDensityUnbounded. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityPredictableL2_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoDensityPredictableL2_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoDensityPredictableL2_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoDensityPredictableL2_F003

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

/-- **Reverse triangle for eLpNorm (tsub form).** Standard consequence of
`eLpNorm_add_le`: `eLpNorm f - eLpNorm g ≤ eLpNorm (f - g)` (ENNReal truncated). -/
private lemma eLpNorm_sub_eLpNorm_le_eLpNorm_sub
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {μ : Measure α}
    {f g : α → E}
    (hf : MeasureTheory.AEStronglyMeasurable f μ)
    (hg : MeasureTheory.AEStronglyMeasurable g μ) :
    MeasureTheory.eLpNorm f p μ - MeasureTheory.eLpNorm g p μ
      ≤ MeasureTheory.eLpNorm (f - g) p μ := by
  rw [tsub_le_iff_left]
  have h_decomp : f = g + (f - g) := by ext x; simp
  have h_meas_diff : MeasureTheory.AEStronglyMeasurable (f - g) μ := hf.sub hg
  conv_lhs => rw [h_decomp]
  exact MeasureTheory.eLpNorm_add_le hg h_meas_diff hp
/-- **L²-norm continuity from L²-difference vanishing.** If
`eLpNorm (fn n - f) p μ → 0`, then `eLpNorm (fn n) p μ → eLpNorm f p μ`.

Squeeze argument:
* upper bound `eLpNorm (fn n) ≤ eLpNorm f + eLpNorm (fn n - f)` from
  `fn n = f + (fn n - f)` plus triangle (`eLpNorm_add_le`);
* lower bound `eLpNorm f - eLpNorm (fn n - f) ≤ eLpNorm (fn n)` from
  the same decomposition with the role of `f` and `fn n` swapped.

Both bounds tend to `eLpNorm f` (upper via `Tendsto.const_add`, lower via
`ENNReal.Tendsto.sub`); squeeze closes the proof. -/
private lemma eLpNorm_tendsto_of_eLpNorm_sub_tendsto_zero
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {μ : Measure α}
    {f : α → E} {fn : ℕ → α → E}
    (hf : MeasureTheory.AEStronglyMeasurable f μ)
    (hfn : ∀ n, MeasureTheory.AEStronglyMeasurable (fn n) μ)
    (h_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (fn n - f) p μ) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (fn n) p μ) Filter.atTop
      (nhds (MeasureTheory.eLpNorm f p μ)) := by
  have h_upper : ∀ n, MeasureTheory.eLpNorm (fn n) p μ ≤
      MeasureTheory.eLpNorm f p μ + MeasureTheory.eLpNorm (fn n - f) p μ := by
    intro n
    have h_decomp : fn n = f + (fn n - f) := by ext x; simp
    have h_meas_diff : MeasureTheory.AEStronglyMeasurable (fn n - f) μ :=
      (hfn n).sub hf
    conv_lhs => rw [h_decomp]
    exact MeasureTheory.eLpNorm_add_le hf h_meas_diff hp
  have h_lower : ∀ n,
      MeasureTheory.eLpNorm f p μ - MeasureTheory.eLpNorm (fn n - f) p μ
        ≤ MeasureTheory.eLpNorm (fn n) p μ := by
    intro n
    rw [tsub_le_iff_right]
    have h_decomp : f = fn n + -(fn n - f) := by ext x; simp
    have h_meas_diff : MeasureTheory.AEStronglyMeasurable (fn n - f) μ :=
      (hfn n).sub hf
    have h_meas_neg_diff : MeasureTheory.AEStronglyMeasurable (-(fn n - f)) μ :=
      h_meas_diff.neg
    calc MeasureTheory.eLpNorm f p μ
        = MeasureTheory.eLpNorm (fn n + -(fn n - f)) p μ := by rw [← h_decomp]
      _ ≤ MeasureTheory.eLpNorm (fn n) p μ
            + MeasureTheory.eLpNorm (-(fn n - f)) p μ :=
          MeasureTheory.eLpNorm_add_le (hfn n) h_meas_neg_diff hp
      _ = MeasureTheory.eLpNorm (fn n) p μ
            + MeasureTheory.eLpNorm (fn n - f) p μ := by
          rw [MeasureTheory.eLpNorm_neg]
  have h_lower_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm f p μ - MeasureTheory.eLpNorm (fn n - f) p μ)
      Filter.atTop (nhds (MeasureTheory.eLpNorm f p μ)) := by
    have h := ENNReal.Tendsto.sub
      (tendsto_const_nhds (x := MeasureTheory.eLpNorm f p μ))
      h_tendsto (Or.inr ENNReal.zero_ne_top)
    simpa using h
  have h_upper_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm f p μ + MeasureTheory.eLpNorm (fn n - f) p μ)
      Filter.atTop (nhds (MeasureTheory.eLpNorm f p μ)) := by
    have h := h_tendsto.const_add (MeasureTheory.eLpNorm f p μ)
    simpa using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    h_lower_tendsto h_upper_tendsto h_lower h_upper
/-- **Bridge: nested-lintegral-of-squared-norm = `eLpNorm²` on product measure.**

For any `ℝ`-valued `h : Ω × ℝ → ℝ` measurable and `μ`-SFinite,
`∫⁻ ω, ∫⁻ s in Icc 0 T, ‖h (ω, s)‖₊² ∂vol ∂μ`
`  = eLpNorm h 2 (μ.prod (vol.restrict (Icc 0 T))) ^ 2`.
Tonelli + `eLpNorm_nnreal_pow_eq_lintegral` (instantiated at `p = 2`). -/
lemma lintegral_sq_eq_eLpNorm_sq_on_prod_brownian
    {μ : Measure Ω} [SFinite μ] {T : ℝ} (h : Ω × ℝ → ℝ) (hh : Measurable h) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖h (ω, s)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ
      = MeasureTheory.eLpNorm h 2
          (μ.prod (volume.restrict (Set.Icc (0 : ℝ) T))) ^ (2 : ℝ) := by
  set μν := μ.prod (volume.restrict (Set.Icc (0 : ℝ) T)) with hμν
  have h_aem_sq : AEMeasurable
      (fun p : Ω × ℝ => (‖h p‖₊ : ℝ≥0∞) ^ 2) μν :=
    (hh.enorm.pow_const 2).aemeasurable
  -- Tonelli on the squared integrand.
  have h_Tonelli :
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖h (ω, s)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ
        = ∫⁻ p, (‖h p‖₊ : ℝ≥0∞) ^ 2 ∂μν := by
    rw [MeasureTheory.lintegral_prod _ h_aem_sq]
  rw [h_Tonelli]
  -- Bridge: ∫⁻ p, (‖h p‖₊ : ℝ≥0∞)^2 ∂μν = eLpNorm h 2 μν ^ (2:ℝ).
  have h_pow_lemma := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral
    (μ := μν) (p := (2 : NNReal)) (f := h)
    (by norm_num : (2 : NNReal) ≠ 0)
  have h_two_R : ((2 : NNReal) : ℝ) = (2 : ℝ) := by norm_num
  have h_two_ENNReal : ((2 : NNReal) : ℝ≥0∞) = (2 : ℝ≥0∞) := by simp
  rw [h_two_ENNReal, h_two_R] at h_pow_lemma
  -- h_pow_lemma : eLpNorm h 2 μν ^ (2:ℝ) = ∫⁻ p, ‖h p‖ₑ ^ (2:ℝ) ∂μν
  rw [h_pow_lemma]
  -- Goal: ∫⁻ p, (‖h p‖₊ : ℝ≥0∞)^2 ∂μν
  --   = ∫⁻ p, ‖h p‖ₑ ^ (2:ℝ) ∂μν
  refine lintegral_congr (fun p => ?_)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  rfl
-- maxHeartbeats: triangle-inequality lift through nested lintegrals + Tonelli.

-- maxHeartbeats: triangle-inequality lift through nested lintegrals + Tonelli.

end LevyStochCalc.Brownian.Ito


