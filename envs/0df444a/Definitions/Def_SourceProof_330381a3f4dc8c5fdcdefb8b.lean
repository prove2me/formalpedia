-- Prove2me | Definitions.Def_SourceProof_330381a3f4dc8c5fdcdefb8b
-- name    : SourceProof_330381a3f4dc8c5fdcdefb8b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:06:36.414189+00:00
-- url     : https://prove2.me/theorems/f50a5f68-6e27-4172-a77b-d557a3421a8c
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Poisson.integral_mul_charCompensator
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterFubini_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The pairing with the compensator as a time integral of the pairings with the characters

The chain rule's integrand for the family cut at `t` factors as a deterministic mark times the
predictable exponential. Pairing a weight with the compensator and swapping the two integrals
therefore leaves, at each point of the window, the mark times the pairing of the weight with the
character at that time.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Fubini

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in

theorem _root_.Prove2MeSourceProof.h_330381a3f4dc8c5fdcdefb8b (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) {r : Ω → ℝ} (hr1 : Integrable r P) (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) {t : ℝ} (htT : t ≤ T) :
    ∫ ω, (r ω : ℂ) * charCompensator N w Bfam A T t ω ∂P
      = ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A,
          charMark w Bfam t q * ∫ ω, (r ω : ℂ) * charAt N w Bfam q.1 ω ∂P
          ∂(referenceIntensity ν) := by
  set W : Set (ℝ × E) := Set.Ioc (0 : ℝ) T ×ˢ A with hW
  have hWm : MeasurableSet W := measurableSet_Ioc.prod hA
  have hWfin : LevyStochCalc.Poisson.referenceIntensity ν W ≠ ⊤ := LevyStochCalc.Poisson.referenceIntensity_Ioc_prod_ne_top hAν T
  haveI : IsFiniteMeasure ((LevyStochCalc.Poisson.referenceIntensity ν).restrict W) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hWfin⟩
  set F : Ω → ℝ × E → ℂ :=
    fun ω q => (r ω : ℂ) * LevyStochCalc.Poisson.charIntegrand N w (LevyStochCalc.Poisson.truncFam Bfam t) A T ω q.1 q.2 with hF
  have hCm : Measurable fun p : Ω × ℝ × E =>
      LevyStochCalc.Poisson.charIntegrand N w (LevyStochCalc.Poisson.truncFam Bfam t) A T p.1 p.2.1 p.2.2 :=
    (_root_.Prove2MeSourceProof.h_ac442bc7d640aae9c9b7360e N hℱ w (LevyStochCalc.Poisson.measurableSet_truncFam hBm t) hA hAν
      (LevyStochCalc.Poisson.truncFam_subset hBsub t)).mono (LevyStochCalc.Probability.markedPredictableSigma_le ℱ ν) le_rfl
  have hr' : AEStronglyMeasurable (fun ω => (r ω : ℂ)) P :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hr1.aestronglyMeasurable
  have hFm : AEStronglyMeasurable (Function.uncurry F)
      (P.prod ((LevyStochCalc.Poisson.referenceIntensity ν).restrict W)) :=
    hr'.comp_fst.mul hCm.aestronglyMeasurable
  have hF : Integrable (Function.uncurry F) (P.prod ((LevyStochCalc.Poisson.referenceIntensity ν).restrict W)) := by
    refine (integrable_prod_iff hFm).mpr ⟨Filter.Eventually.of_forall fun ω => ?_, ?_⟩
    · exact (LevyStochCalc.Poisson.integrableOn_charIntegrand N hℱ w (LevyStochCalc.Poisson.measurableSet_truncFam hBm t) hA hAν
        (LevyStochCalc.Poisson.truncFam_subset hBsub t) ω).const_mul (r ω : ℂ)
    · refine Integrable.mono'
        ((hr1.norm.const_mul 2).mul_const (((LevyStochCalc.Poisson.referenceIntensity ν).restrict W).real Set.univ))
        hFm.norm.integral_prod_right' (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun q => norm_nonneg _)]
      calc ∫ q, ‖F ω q‖ ∂((LevyStochCalc.Poisson.referenceIntensity ν).restrict W)
          ≤ ∫ _, 2 * ‖r ω‖ ∂((LevyStochCalc.Poisson.referenceIntensity ν).restrict W) := by
            refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun q => norm_nonneg _)
              (integrable_const _) (Filter.Eventually.of_forall fun q => ?_)
            simp only [hF, norm_mul, Complex.norm_real]
            calc ‖r ω‖ * ‖LevyStochCalc.Poisson.charIntegrand N w (LevyStochCalc.Poisson.truncFam Bfam t) A T ω q.1 q.2‖
                ≤ ‖r ω‖ * 2 := mul_le_mul_of_nonneg_left
                    (_root_.Prove2MeSourceProof.h_099fb631e9952e9258da9935 N w _ A T ω q.1 q.2) (norm_nonneg _)
              _ = 2 * ‖r ω‖ := mul_comm _ _
        _ = 2 * ‖r ω‖ * ((LevyStochCalc.Poisson.referenceIntensity ν).restrict W).real Set.univ := by
            rw [integral_const, smul_eq_mul, mul_comm]
  have hswap := integral_integral_swap hF
  have hL : ∫ ω, (r ω : ℂ) * LevyStochCalc.Poisson.charCompensator N w Bfam A T t ω ∂P
      = ∫ ω, ∫ q, F ω q ∂((LevyStochCalc.Poisson.referenceIntensity ν).restrict W) ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [LevyStochCalc.Poisson.charCompensator]
    rw [MeasureTheory.integral_const_mul]
  have hR : ∫ q, ∫ ω, F ω q ∂P ∂((LevyStochCalc.Poisson.referenceIntensity ν).restrict W)
      = ∫ q in W, LevyStochCalc.Poisson.charMark w Bfam t q * ∫ ω, (r ω : ℂ) * LevyStochCalc.Poisson.charAt N w Bfam q.1 ω ∂P
          ∂(LevyStochCalc.Poisson.referenceIntensity ν) := by
    refine setIntegral_congr_fun hWm fun q hq => ?_
    have hq1 : 0 < q.1 := hq.1.1
    have hq2 : q.2 ∈ A := hq.2
    have hfac : ∀ ω, F ω q = LevyStochCalc.Poisson.charMark w Bfam t q
        * ((r ω : ℂ) * Complex.exp
            (Complex.I * (LevyStochCalc.Poisson.predStrict N w (LevyStochCalc.Poisson.truncFam Bfam t) A T ω q.1 q.2 : ℂ))) := by
      intro ω
      change (r ω : ℂ) * LevyStochCalc.Poisson.charIntegrand N w (LevyStochCalc.Poisson.truncFam Bfam t) A T ω q.1 q.2 = _
      rw [LevyStochCalc.Poisson.charIntegrand_truncFam_eq]
      ring
    simp_rw [hfac]
    rw [MeasureTheory.integral_const_mul]
    rcases le_or_gt q.1 t with hqt | hqt
    · rw [LevyStochCalc.Poisson.integral_mul_exp_predStrict N w hBm hq1 hqt htT hq2]
    · rw [LevyStochCalc.Poisson.charMark_eq_zero w Bfam hqt, zero_mul, zero_mul]
  rw [hL, hswap, hR]
end Fubini

end LevyStochCalc.Poisson


