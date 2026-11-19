-- Prove2me | Definitions.Def_SourceProof_6b34c1879b36aa5cac429147
-- name    : SourceProof_6b34c1879b36aa5cac429147
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T17:01:21.239309+00:00
-- url     : https://prove2.me/theorems/b4228d94-756f-419e-b916-164f970e83f4
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.integral_mul_setIntegral_swap
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pairing an integrable weight against a time integral

For an integrable weight and a bounded jointly measurable process on a bounded time interval, the
expectation of the weight against the time integral of the process is the time integral of the
expectations.
-/

open MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

section Swap

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} [SFinite μ]


theorem _root_.Prove2MeSourceProof.h_6b34c1879b36aa5cac429147 {S : Set Y} (hSfin : μ S ≠ ⊤)
    {Z : Ω → ℝ} (hZ1 : Integrable Z P) {V : Ω → ℝ} (hVm : AEStronglyMeasurable V P)
    {Mv : ℝ} (hMv0 : 0 ≤ Mv) (hVb : ∀ ω, |V ω| ≤ Mv)
    {F : Ω → Y → ℝ} (hFm : Measurable (Function.uncurry F))
    {MF : ℝ} (hFb : ∀ ω y, |F ω y| ≤ MF) :
    ∫ ω, Z ω * V ω * (∫ y in S, F ω y ∂μ) ∂P
      = ∫ y in S, ∫ ω, Z ω * V ω * F ω y ∂P ∂μ := by
  haveI : IsFiniteMeasure (μ.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hSfin⟩
  have hZVm : AEStronglyMeasurable (fun ω => Z ω * V ω) P :=
    hZ1.aestronglyMeasurable.mul hVm
  have hGm : AEStronglyMeasurable (Function.uncurry fun ω y => Z ω * V ω * F ω y)
      (P.prod (μ.restrict S)) := hZVm.comp_fst.mul hFm.aestronglyMeasurable
  have hFω : ∀ ω, Measurable (F ω) := fun ω => hFm.comp (measurable_prodMk_left (x := ω))
  have hZV : ∀ ω, |Z ω * V ω| ≤ Mv * |Z ω| := by
    intro ω
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hVb ω) (abs_nonneg _)
  have hG : Integrable (Function.uncurry fun ω y => Z ω * V ω * F ω y)
      (P.prod (μ.restrict S)) := by
    refine (integrable_prod_iff hGm).mpr ⟨Filter.Eventually.of_forall fun ω => ?_, ?_⟩
    · change Integrable (fun y => Z ω * V ω * F ω y) (μ.restrict S)
      refine Integrable.mono' (integrable_const (|Z ω * V ω| * MF))
        (((hFω ω).aestronglyMeasurable).const_mul _)
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hFb ω y) (abs_nonneg _)
    · refine Integrable.mono'
        (((hZ1.norm.const_mul (MF * Mv)).mul_const ((μ.restrict S).real Set.univ)))
        hGm.norm.integral_prod_right' (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
      calc ∫ y, ‖Z ω * V ω * F ω y‖ ∂(μ.restrict S)
          ≤ ∫ _, MF * Mv * ‖Z ω‖ ∂(μ.restrict S) := by
            refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
              (integrable_const _) (Filter.Eventually.of_forall fun y => ?_)
            change ‖Z ω * V ω * F ω y‖ ≤ MF * Mv * ‖Z ω‖
            calc ‖Z ω * V ω * F ω y‖ = |Z ω * V ω| * |F ω y| := by
                  rw [Real.norm_eq_abs, abs_mul]
              _ ≤ Mv * |Z ω| * MF :=
                  mul_le_mul (hZV ω) (hFb ω y) (abs_nonneg _) (mul_nonneg hMv0 (abs_nonneg _))
              _ = MF * Mv * ‖Z ω‖ := by rw [Real.norm_eq_abs]; ring
        _ = MF * Mv * ‖Z ω‖ * ((μ.restrict S).real Set.univ) := by
            rw [integral_const, smul_eq_mul, mul_comm]
  have hL : ∫ ω, Z ω * V ω * (∫ y in S, F ω y ∂μ) ∂P
      = ∫ ω, ∫ y, Z ω * V ω * F ω y ∂(μ.restrict S) ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    change Z ω * V ω * (∫ y in S, F ω y ∂μ) = ∫ y in S, Z ω * V ω * F ω y ∂μ
    rw [MeasureTheory.integral_const_mul]
  rw [hL, integral_integral_swap hG]
end Swap

end LevyStochCalc.Probability


