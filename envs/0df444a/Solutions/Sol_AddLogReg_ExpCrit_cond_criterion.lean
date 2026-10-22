-- Prove2me | solution 1 for AddLogReg.ExpCrit.cond_criterion
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:58:31.097911+00:00
-- url     : https://prove2.me/submissions/8dd8443d-325b-4e94-a2f0-a2f3f34bc6e8

import Mathlib
import Definitions.Def_AddLogReg_ExpCrit_Setting

set_option autoImplicit false
open MeasureTheory ProbabilityTheory AddLogReg.ExpCrit

theorem solution {X : Type*} [MeasurableSpace X] (ν : Measure (X × Bool))
    [IsProbabilityMeasure ν] :
    (∀ (x : X) (t : ℝ),
      condCrit ν x t = condProb ν true x * Real.exp (-t) + condProb ν false x * Real.exp t) ∧
    (∀ F : X → ℝ, Measurable F →
      J ν F = ∫⁻ x, ENNReal.ofReal (condCrit ν x (F x)) ∂ν.fst) := by
  refine ⟨?_, ?_⟩
  · intro x t
    unfold condCrit condProb
    rw [integral_fintype (Integrable.of_finite)]
    simp [Fintype.sum_bool, sgn, Measure.real]
  · intro F hF
    have hs : Measurable (fun z : X × Bool => sgn z.2) :=
      (measurable_of_countable sgn).comp measurable_snd
    have hmeas : Measurable (fun z : X × Bool => ENNReal.ofReal (Real.exp (-(sgn z.2 * F z.1)))) :=
      ENNReal.measurable_ofReal.comp
        (Real.measurable_exp.comp ((hs.mul (hF.comp measurable_fst)).neg))
    unfold J
    conv_lhs => rw [← Measure.disintegrate ν ν.condKernel]
    rw [Measure.lintegral_compProd hmeas]
    refine lintegral_congr (fun a => ?_)
    unfold condCrit
    rw [ofReal_integral_eq_lintegral_ofReal (Integrable.of_finite)
      (Filter.Eventually.of_forall (fun b => (Real.exp_pos _).le))]
