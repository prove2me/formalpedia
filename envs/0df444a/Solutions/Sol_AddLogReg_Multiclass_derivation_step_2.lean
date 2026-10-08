-- Prove2me | solution 1 for AddLogReg.Multiclass.derivation_step_2
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:03:50.400737+00:00
-- url     : https://prove2.me/submissions/6efd4006-e6cb-4b8e-9d06-5755bb84a27b

import Mathlib
import Definitions.Def_AddLogReg_Multiclass_Setting

open MeasureTheory ProbabilityTheory ENNReal

open AddLogReg.Multiclass


theorem solution {J : ℕ} [NeZero J] (hJ : 2 ≤ J) {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Fin J)) [IsProbabilityMeasure ν] (F : X → Fin J → ℝ) (x : X) :
    (∀ j, hess F x j j ≠ 0) ∧
      ∀ b j, j ≠ b → diagStep ν F x b j =
        (∫ y, (ystar y j - softmax (F x) j) ∂(ν.condKernel x)) /
          (softmax (F x) j * (1 - softmax (F x) j)) := by
  classical
  constructor
  · intro j
    have hZ : 0 < ∑ k, Real.exp (F x k) :=
      Finset.sum_pos (fun k _ => Real.exp_pos _) Finset.univ_nonempty
    have hcard : 1 < Fintype.card (Fin J) := by simpa using (show 1 < J by omega)
    obtain ⟨k, hk⟩ := Fintype.exists_ne_of_one_lt_card hcard j
    have hlt : Real.exp (F x j) < ∑ k, Real.exp (F x k) := by
      exact Finset.single_lt_sum hk (Finset.mem_univ j) (Finset.mem_univ k) (Real.exp_pos _) (fun i _ _ => le_of_lt (Real.exp_pos _))
    have hp : 0 < softmax (F x) j := div_pos (Real.exp_pos _) hZ
    have hp1 : softmax (F x) j < 1 := (div_lt_one hZ).2 hlt
    simp only [hess, if_pos rfl, neg_ne_zero]
    exact mul_ne_zero (ne_of_gt hp) (ne_of_gt (sub_pos.mpr hp1))
  · intro b j hj
    simp [diagStep, hj, hess, score]

#print axioms solution
