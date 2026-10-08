-- Prove2me | solution 1 for AddLogReg.Gentle.result_4
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:47:48.515533+00:00
-- url     : https://prove2.me/submissions/e9b352ed-a46c-41ec-b850-0cb9f9e356e3

import Mathlib
import Theorems.Thm_AddLogReg_Gentle_derivation_derivs
import Theorems.Thm_AddLogReg_Gentle_newton_update
open MeasureTheory ProbabilityTheory AddLogReg.Gentle


theorem solution {X : Type*} [MeasurableSpace X] (ν : Measure (X × Bool))
    [IsProbabilityMeasure ν] (F : X → ℝ) (x : X) :
    HasDerivAt (condCritAt ν F x)
        (-∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * F x)) * AddLogReg.ExpCrit.sgn b ∂(ν.condKernel x)) 0 ∧
      (∀ t : ℝ, HasDerivAt (condCritAt ν F x)
        (-∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * (F x + t))) * AddLogReg.ExpCrit.sgn b ∂(ν.condKernel x)) t) ∧
      HasDerivAt (fun t : ℝ => -∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * (F x + t))) * AddLogReg.ExpCrit.sgn b ∂(ν.condKernel x))
        (∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * F x)) ∂(ν.condKernel x)) 0 ∧
      0 < ∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * F x)) ∂(ν.condKernel x) ∧
      gentleStep ν F x =
        F x - (-∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * F x)) * AddLogReg.ExpCrit.sgn b ∂(ν.condKernel x)) /
          (∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * F x)) ∂(ν.condKernel x)) := by
  have hd := derivation_derivs ν F x
  refine ⟨hd.1, hd.2.1, ?_, ?_, ?_⟩
  · rw [← hd.2.2.2]
    exact hd.2.2.1
  · exact integral_exp_pos Integrable.of_finite
  · simpa only [gentleStep, neg_div, sub_neg_eq_add] using (newton_update ν F x).symm



#print axioms solution

