-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_PathwiseIdentity_F000
-- name    : LevyStochCalc_Poisson_PathwiseIdentity_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:09:40.60355+00:00
-- url     : https://prove2.me/theorems/7ef133f6-710e-4ba4-98b2-550f2e96c5a8
-- title:
--   Source declarations: LevyStochCalc.Poisson.PathwiseIdentity
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.PathwiseIdentity. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_Compensated_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatorL1_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatorL1_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatorL1_F002
import Definitions.Def_LevyStochCalc_Poisson_CompensatorL1_F003
import Definitions.Def_LevyStochCalc_Poisson_CompensatorL1_F004
import Definitions.Def_LevyStochCalc_Poisson_MarkStepPathwise_F001
import Definitions.Def_LevyStochCalc_Poisson_MarkStepPathwise_F002
import Definitions.Def_SourceProof_4e84e0944366bca12237e964
import Definitions.Def_SourceProof_64e5e836994ceb2ae7c553a4
import Definitions.Def_SourceProof_d1a830962090e7daf9e48a75
import Definitions.Def_SourceProof_d924d3c21257fe582c3c4d51

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated integral of a predictable integrand is pathwise

The compensated integral is an `L²` limit of the integrals of mark-step approximants. For a
predictable integrand carried by a window of finite intensity the approximants can be taken
inside that window, where the reference intensity compensates the counts, so their pathwise forms
converge in mean to the pathwise form of the integrand while their integrals converge in `L²` to
the compensated integral. The two limits therefore agree.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Assembly

variable (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : IsPoissonFiltration N ℱ) (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  {A : Set E} (hA : MeasurableSet A)

/-- The stage-`n` approximant with its marks cut down to `A`. -/
noncomputable def restrictedStage (n : ℕ) :
    MarkStep Ω E ν (TimeGrid.dyadic (stageHorizon n) (stageHorizon_pos n)
      (master N ℱ φ h_meas h_progMeas h_sq n).1) :=
  (master N ℱ φ h_meas h_progMeas h_sq n).2.restrictMarks hA
theorem restrictedStage_adapted (n : ℕ) :
    (restrictedStage N ℱ φ h_meas h_progMeas h_sq hA n).Adapted ℱ :=
  MarkStep.restrictMarks_adapted _ hA (master_adapted N ℱ φ h_meas h_progMeas h_sq n)
/-- The restricted approximant, cut at the horizon, vanishes off the window. -/
theorem evalTo_restrictedStage_eq_zero (n : ℕ) {T : ℝ}
    {q : ℝ × E} (hq : q ∉ Set.Ioc (0 : ℝ) T ×ˢ A) (ω : Ω) :
    (Set.Iic T).indicator (fun _ => (1 : ℝ)) q.1
        * (restrictedStage N ℱ φ h_meas h_progMeas h_sq hA n).eval q.1 q.2 ω = 0 := by
  rw [restrictedStage]
  by_cases he : q.2 ∈ A
  · have hq1 : q.1 ∉ Set.Ioc (0 : ℝ) T := fun h => hq (Set.mem_prod.mpr ⟨h, he⟩)
    rcases le_or_gt q.1 0 with h0 | h0
    · rw [MarkStep.eval_eq_zero_of_nonpos _ h0, mul_zero]
    · have hTq : T < q.1 := by
        by_contra hcon
        exact hq1 ⟨h0, not_lt.mp hcon⟩
      rw [Set.indicator_of_notMem (by simpa using not_le.mpr hTq), zero_mul]
  · rw [MarkStep.eval_restrictMarks_of_notMem _ hA _ he, mul_zero]
/-- **The restricted stage integral is the pathwise compensated integral over the window.** -/
theorem ae_restrictedStage_integral_eq (n : ℕ) (T : ℝ) :
    (fun ω => (restrictedStage N ℱ φ h_meas h_progMeas h_sq hA n).integral N T ω)
      =ᵐ[P] fun ω =>
        (∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, (Set.Iic T).indicator (fun _ => (1 : ℝ)) q.1
            * (restrictedStage N ℱ φ h_meas h_progMeas h_sq hA n).eval q.1 q.2 ω ∂(N.N ω))
          - ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, (Set.Iic T).indicator (fun _ => (1 : ℝ)) q.1
              * (restrictedStage N ℱ φ h_meas h_progMeas h_sq hA n).eval q.1 q.2 ω
              ∂(referenceIntensity ν) := by
  filter_upwards [MarkStep.ae_count_clamped_rect_ne_top N
    (restrictedStage N ℱ φ h_meas h_progMeas h_sq hA n) T] with ω hω
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun q hq =>
      evalTo_restrictedStage_eq_zero N ℱ φ h_meas h_progMeas h_sq hA n hq ω,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun q hq =>
      evalTo_restrictedStage_eq_zero N ℱ φ h_meas h_progMeas h_sq hA n hq ω]
  exact _root_.Prove2MeSourceProof.h_64e5e836994ceb2ae7c553a4 N _ T ω hω
/-- The window energy of the restricted approximant's error is at most the stage error. -/
theorem window_energy_le_stageErr (hsupp : ∀ ω s e, e ∉ A → φ ω s e = 0) (n : ℕ) {T : ℝ}
    (hT : T ≤ stageHorizon n) :
    (∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
        ‖(Set.Iic T).indicator (fun _ => (1 : ℝ)) q.1
          * (restrictedStage N ℱ φ h_meas h_progMeas h_sq hA n).eval q.1 q.2 ω
          - φ ω q.1 q.2‖ₑ ^ 2 ∂(referenceIntensity ν) ∂P)
      ≤ stageErr φ P n (master N ℱ φ h_meas h_progMeas h_sq n).2 := by
  set G := (master N ℱ φ h_meas h_progMeas h_sq n).2 with hGdef
  have hmeasq : ∀ ω : Ω, Measurable fun q : ℝ × E =>
      ‖(Set.Iic T).indicator (fun _ => (1 : ℝ)) q.1
        * (G.restrictMarks hA).eval q.1 q.2 ω - φ ω q.1 q.2‖ₑ ^ 2 := by
    intro ω
    refine (Measurable.enorm ?_).pow_const 2
    refine Measurable.sub (Measurable.mul ?_ ?_) (h_meas.comp measurable_prodMk_left)
    · exact (measurable_const.indicator measurableSet_Iic).comp measurable_fst
    · exact (G.restrictMarks hA).eval_measurable.comp
        (by fun_prop : Measurable fun q : ℝ × E => ((ω, q.1, q.2) : Ω × ℝ × E))
  rw [stageErr]
  refine lintegral_mono fun ω => ?_
  rw [show (restrictedStage N ℱ φ h_meas h_progMeas h_sq hA n) = G.restrictMarks hA from rfl,
    lintegral_referenceIntensity_window (hmeasq ω) A T]
  calc ∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e in A,
        ‖(Set.Iic T).indicator (fun _ => (1 : ℝ)) s
          * (G.restrictMarks hA).eval s e ω - φ ω s e‖ₑ ^ 2 ∂ν ∂volume
      ≤ ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          ‖(Set.Iic T).indicator (fun _ => (1 : ℝ)) s
            * (G.restrictMarks hA).eval s e ω - φ ω s e‖ₑ ^ 2 ∂ν ∂volume :=
        lintegral_mono' (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)
          (fun s => lintegral_mono' Measure.restrict_le_self le_rfl)
    _ ≤ ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume := by
        refine lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Icc fun s hs => ?_)
        refine lintegral_mono fun e => ?_
        rw [Set.indicator_of_mem (Set.mem_Iic.mpr hs.2), one_mul]
        refine pow_le_pow_left' ?_ 2
        change (‖(G.restrictMarks hA).eval s e ω - φ ω s e‖₊ : ℝ≥0∞)
          ≤ (‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞)
        refine ENNReal.coe_le_coe.mpr ?_
        rw [← nnnorm_neg, neg_sub]
        have habs := G.abs_sub_eval_restrictMarks_le hA hsupp ω s e
        rw [← Real.norm_eq_abs, ← Real.norm_eq_abs] at habs
        exact_mod_cast habs
    _ ≤ ∫⁻ s in Set.Icc (0 : ℝ) (stageHorizon n), ∫⁻ e,
          (‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume :=
        lintegral_mono' (Measure.restrict_mono (Set.Icc_subset_Icc_right hT) le_rfl) le_rfl
/-- The stage errors of the master sequence tend to zero. -/
theorem tendsto_stageErr :
    Tendsto (fun n => stageErr φ P n (master N ℱ φ h_meas h_progMeas h_sq n).2)
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ENNReal.tendsto_inv_nat_nhds_zero (fun n => bot_le)
      fun n => ENNReal.inv_le_inv.mpr le_self_add
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hinv (fun n => bot_le)
    fun n => (master_err N ℱ φ h_meas h_progMeas h_sq n).le
/-- The error of the clamped mark-restricted stage-`n` approximant against the integrand. -/
noncomputable def stageDefect (T : ℝ) (n : ℕ) (ω : Ω) (s : ℝ) (e : E) : ℝ :=
  (Set.Iic T).indicator (fun _ => (1 : ℝ)) s
      * (restrictedStage N ℱ φ h_meas h_progMeas h_sq hA n).eval s e ω - φ ω s e
theorem markedPredictable_stageDefect (hφpred : Probability.MarkedPredictable ℱ ν φ) (T : ℝ)
    (n : ℕ) :
    Probability.MarkedPredictable ℱ ν
      (stageDefect N ℱ φ h_meas h_progMeas h_sq hA T n) :=
  Measurable.sub (_root_.Prove2MeSourceProof.h_4e84e0944366bca12237e964 _
    (restrictedStage_adapted N ℱ φ h_meas h_progMeas h_sq hA n) T) hφpred
theorem measurable_stageDefect (T : ℝ) (n : ℕ) :
    Measurable fun p : Ω × ℝ × E =>
      stageDefect N ℱ φ h_meas h_progMeas h_sq hA T n p.1 p.2.1 p.2.2 := by
  refine Measurable.sub (Measurable.mul ?_ ?_) h_meas
  · exact (measurable_const.indicator measurableSet_Iic).comp (measurable_fst.comp measurable_snd)
  · exact (restrictedStage N ℱ φ h_meas h_progMeas h_sq hA n).eval_measurable
/-- The window energy of the stage defect is at most the stage error. -/
theorem window_energy_stageDefect_le (hsupp : ∀ ω s e, e ∉ A → φ ω s e = 0) (n : ℕ) {T : ℝ}
    (hT : T ≤ stageHorizon n) :
    (∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
        ‖stageDefect N ℱ φ h_meas h_progMeas h_sq hA T n ω q.1 q.2‖ₑ ^ 2
          ∂(referenceIntensity ν) ∂P)
      ≤ stageErr φ P n (master N ℱ φ h_meas h_progMeas h_sq n).2 :=
  window_energy_le_stageErr N ℱ φ h_meas h_progMeas h_sq hA hsupp n hT
theorem window_energy_stageDefect_ne_top (hsupp : ∀ ω s e, e ∉ A → φ ω s e = 0) (n : ℕ) {T : ℝ}
    (hT : T ≤ stageHorizon n) :
    (∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
        ‖stageDefect N ℱ φ h_meas h_progMeas h_sq hA T n ω q.1 q.2‖ₑ ^ 2
          ∂(referenceIntensity ν) ∂P) ≠ ⊤ :=
  ne_top_of_le_ne_top
    (lt_of_lt_of_le (master_err N ℱ φ h_meas h_progMeas h_sq n) le_top).ne
    (window_energy_stageDefect_le N ℱ φ h_meas h_progMeas h_sq hA hsupp n hT)
omit [IsProbabilityMeasure P] in
include h_meas h_sq in
/-- The energy of the integrand over a window of the reference intensity is finite. -/
theorem window_energy_ne_top {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
      ‖φ ω q.1 q.2‖ₑ ^ 2 ∂(referenceIntensity ν) ∂P ≠ ⊤ := by
  refine ne_top_of_le_ne_top (h_sq T hT).ne ?_
  refine lintegral_mono fun ω => ?_
  have hmφ : Measurable fun q : ℝ × E => ‖φ ω q.1 q.2‖ₑ ^ 2 :=
    (measurable_enorm.comp (h_meas.comp measurable_prodMk_left)).pow_const 2
  rw [lintegral_referenceIntensity_window hmφ A T]
  exact lintegral_mono' (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)
    fun s => lintegral_mono' Measure.restrict_le_self le_rfl
/-- The mark-restricted stage integrals converge to the compensated integral in mean. -/
theorem tendsto_lintegral_process_sub_restrictedStage
    (hsupp : ∀ ω s e, e ∉ A → φ ω s e = 0) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n => ∫⁻ ω,
      ‖process N ℱ hℱ φ h_meas h_progMeas h_sq T ω
        - (restrictedStage N ℱ φ h_meas h_progMeas h_sq hA n).integral N T ω‖ₑ ∂P)
      atTop (𝓝 0) := by
  have hev : ∀ᶠ n : ℕ in atTop, T ≤ stageHorizon n :=
    (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℝ)) (by norm_num)).eventually_ge_atTop T
  have hrpow : Tendsto (fun n =>
      (stageErr φ P n (master N ℱ φ h_meas h_progMeas h_sq n).2) ^ (2 : ℝ)⁻¹)
      atTop (𝓝 0) := by
    have hc := (ENNReal.continuous_rpow_const (y := (2 : ℝ)⁻¹)).tendsto 0
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hc
    exact hc.comp (tendsto_stageErr N ℱ φ h_meas h_progMeas h_sq)
  refine _root_.Prove2MeSourceProof.h_d1a830962090e7daf9e48a75
    (process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq T).aestronglyMeasurable
    (fun n => (memLp_stageIntegral N ℱ φ h_meas h_progMeas h_sq n T).aestronglyMeasurable)
    (fun n => (MarkStep.memLp_integral N
      (restrictedStage N ℱ φ h_meas h_progMeas h_sq hA n) T).aestronglyMeasurable)
    (_root_.Prove2MeSourceProof.h_d924d3c21257fe582c3c4d51 N ℱ hℱ φ h_meas h_progMeas h_sq T) ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrpow
    (Eventually.of_forall fun n => bot_le) ?_
  filter_upwards [hev] with n hn
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  set G := (master N ℱ φ h_meas h_progMeas h_sq n).2 with hGdef
  have hGad : G.Adapted ℱ := master_adapted N ℱ φ h_meas h_progMeas h_sq n
  have hw : Measurable fun p : Ω × ℝ × E =>
      (‖φ p.1 p.2.1 p.2.2 - G.eval p.2.1 p.2.2 p.1‖₊ : ℝ≥0∞) ^ 2 :=
    (ENNReal.continuous_coe.measurable.comp (h_meas.sub G.eval_measurable).nnnorm).pow_const 2
  refine le_trans (G.lintegral_integral_sub_restrictMarks_le N hℱ hGad hA hsupp hT.le) ?_
  calc ∫⁻ ω, ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P :=
        lintegral_congr fun ω =>
          lintegral_swap_es (fun ω s e => (‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2) hw ω
    _ ≤ stageErr φ P n G :=
        lintegral_mono fun ω => lintegral_mono_set (Set.Icc_subset_Icc_right hn)
end Assembly

end LevyStochCalc.Poisson.Compensated


