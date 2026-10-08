-- Prove2me | solution 1 for AddLogReg.Multiclass.def_1_two_class
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:03:48.581413+00:00
-- url     : https://prove2.me/submissions/19790d8c-fef3-4a37-82ac-c0e46e35be61

import Mathlib
import Definitions.Def_AddLogReg_Multiclass_Setting

open MeasureTheory ProbabilityTheory ENNReal

open AddLogReg.Multiclass


theorem solution (p : Fin 2 → ℝ) (hp_pos : ∀ j, 0 < p j) (hp_sum : ∑ j, p j = 1)
    (F : Fin 2 → ℝ) (hF : F 0 + F 1 = 0) :
    symMultiLogit p 0 = (1 / 2) * Real.log (p 0 / p 1) ∧
      symMultiLogit p 1 = -symMultiLogit p 0 ∧
      softmax F 0 = Real.exp (F 0) / (Real.exp (F 0) + Real.exp (-F 0)) ∧
      softmax F 1 = 1 - softmax F 0 := by
  have h1 : F 1 = -F 0 := by linarith
  have hd : Real.exp (F 0) + Real.exp (F 1) ≠ 0 := ne_of_gt (add_pos (Real.exp_pos _) (Real.exp_pos _))
  simp only [symMultiLogit, softmax, Fin.sum_univ_two, Nat.cast_ofNat]
  rw [Real.log_div (ne_of_gt (hp_pos 0)) (ne_of_gt (hp_pos 1))]
  refine ⟨by ring, by ring, by rw [h1], ?_⟩
  field_simp
  <;> ring

#print axioms solution
