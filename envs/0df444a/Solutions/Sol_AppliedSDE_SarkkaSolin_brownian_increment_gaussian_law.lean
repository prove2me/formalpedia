-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.brownian_increment_gaussian_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:50:48.633465+00:00
-- url     : https://prove2.me/submissions/c6a3262c-be94-4b13-8364-c59767974250

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MathlibBridge
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian
open scoped NNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : BrownianMotion P) (s t : ℝ≥0) (hst : s ≤ t) :
    HasLaw
      (fun ω => W.W (t : ℝ) ω - W.W (s : ℝ) ω)
      (gaussianReal 0 (t - s)) P := by
  rcases eq_or_lt_of_le hst with h | h
  · subst h
    have hfun : (fun ω => W.W (s : ℝ) ω - W.W (s : ℝ) ω) =
        fun _ : Ω => (0 : ℝ) := by
      funext ω
      ring
    rw [tsub_self, gaussianReal_zero_var, hfun]
    exact ⟨measurable_const.aemeasurable, by simp⟩
  · refine ⟨((W.measurable_eval _).sub (W.measurable_eval _)).aemeasurable, ?_⟩
    rw [W.increment_gaussian s.coe_nonneg (NNReal.coe_lt_coe.2 h)]
    congr 1
    apply NNReal.coe_injective
    change (t : ℝ) - (s : ℝ) = ((t - s : ℝ≥0) : ℝ)
    rw [NNReal.coe_sub hst]
