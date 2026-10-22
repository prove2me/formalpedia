-- Prove2me | solution 1 for AddLogReg.Multiclass.derivation_step_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:19:14.472433+00:00
-- url     : https://prove2.me/submissions/9f1d191a-0b94-46b8-aa26-c8dd9ac6907b

import Mathlib
import Definitions.Def_AddLogReg_Multiclass_Setting
set_option autoImplicit false
open MeasureTheory ProbabilityTheory ENNReal
open AddLogReg.Multiclass

theorem solution {J : ℕ} [NeZero J] (hJ : 2 ≤ J) {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Fin J)) [IsProbabilityMeasure ν] (F : X → Fin J → ℝ) (x : X) (j : Fin J) :
    (1 / (J : ℝ)) * ∑ b, symmetrize (diagStep ν F x b) j =
      (((J : ℝ) - 1) / (J : ℝ)) *
        ((∫ y, (ystar y j - softmax (F x) j) ∂(ν.condKernel x)) /
            (softmax (F x) j * (1 - softmax (F x) j)) -
          (1 / (J : ℝ)) * ∑ k, (∫ y, (ystar y k - softmax (F x) k) ∂(ν.condKernel x)) /
            (softmax (F x) k * (1 - softmax (F x) k))) := by
  have hJ0 : (J : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ J := by exact_mod_cast hJ
    linarith
  set u : Fin J → ℝ := fun k => (∫ y, (ystar y k - softmax (F x) k) ∂(ν.condKernel x)) /
    (softmax (F x) k * (1 - softmax (F x) k)) with hu
  have hd : ∀ b k : Fin J, diagStep ν F x b k = if k = b then 0 else u k := by
    intro b k
    unfold diagStep
    split_ifs with h
    · rfl
    · unfold score hess
      simp only [if_true, hu]
      rw [neg_div_neg_eq]
  have hsymm : ∀ b : Fin J, symmetrize (diagStep ν F x b) j =
      (if j = b then 0 else u j) - (1 / (J : ℝ)) * (∑ k, u k - u b) := by
    intro b
    unfold symmetrize
    rw [hd]
    congr 2
    have : ∑ k, diagStep ν F x b k = ∑ k, (u k - if k = b then u k else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hd]
      split_ifs <;> simp
    rw [this, Finset.sum_sub_distrib, Finset.sum_ite_eq']
    simp
  simp_rw [hsymm]
  have h1 : ∑ b : Fin J, (if j = b then (0:ℝ) else u j) = ((J : ℝ) - 1) * u j := by
    have : ∀ b : Fin J, (if j = b then (0:ℝ) else u j) = u j - if j = b then u j else 0 := by
      intro b; split_ifs <;> simp
    simp_rw [this]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq]
    simp
    ring
  rw [Finset.sum_sub_distrib, h1, ← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← hu]
  field_simp
  ring
