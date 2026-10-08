-- Prove2me | solution 1 for AddLogReg.LogitBoost.result_3
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:47:46.645892+00:00
-- url     : https://prove2.me/submissions/5c6c1918-28c3-414b-b0f9-c3f7a7ebc84a

import Mathlib
import Theorems.Thm_AddLogReg_LogitBoost_eq_33
import Theorems.Thm_AddLogReg_LogitBoost_eq_34_35
import Theorems.Thm_AddLogReg_LogitBoost_eq_36
open MeasureTheory ProbabilityTheory AddLogReg.LogitBoost


theorem solution {X : Type*} [MeasurableSpace X] (ν : Measure (X × Bool))
    [IsProbabilityMeasure ν] (F : X → ℝ) (x : X) :
    HasDerivAt (condLogLik ν F x)
        (2 * ∫ b, (ystar b - symLogistic (F x)) ∂(ν.condKernel x)) 0 ∧
      (∀ t : ℝ, HasDerivAt (condLogLik ν F x)
        (2 * ∫ b, (ystar b - symLogistic (F x + t)) ∂(ν.condKernel x)) t) ∧
      HasDerivAt (fun t : ℝ => 2 * ∫ b, (ystar b - symLogistic (F x + t)) ∂(ν.condKernel x))
        (-4 * ∫ _b, symLogistic (F x) * (1 - symLogistic (F x)) ∂(ν.condKernel x)) 0 ∧
      (-4 * ∫ _b, symLogistic (F x) * (1 - symLogistic (F x)) ∂(ν.condKernel x) ≠ 0) ∧
      logitBoostStep ν F x =
        F x - (2 * ∫ b, (ystar b - symLogistic (F x)) ∂(ν.condKernel x)) /
          (-4 * ∫ _b, symLogistic (F x) * (1 - symLogistic (F x)) ∂(ν.condKernel x)) := by
  have hd := eq_33 ν F x
  have hn := eq_34_35 ν F x
  refine ⟨?_, hd.1, hd.2, hn.1, ?_⟩
  · simpa only [add_zero] using hd.1 0
  · simpa only [sub_eq_add_neg] using (eq_36 ν F x).2.symm



#print axioms solution

