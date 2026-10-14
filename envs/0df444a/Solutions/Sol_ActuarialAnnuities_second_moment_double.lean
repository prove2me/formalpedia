-- Prove2me | solution 1 for ActuarialAnnuities.second_moment_double
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T10:23:53.322011+00:00
-- url     : https://prove2.me/submissions/063ae0c8-8269-4c0a-9d57-ad809628b445

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSecondMoment
import Definitions.Def_actuarial_bProjectedSecondMoment
open ActuarialAnnuities

theorem solution(h a n g delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) : bSecondMoment h a n g delta v b p = bProjectedSecondMoment h a n g delta v b p := by
  have hE : ∀ j k, bEntitlement a g delta j k = bAlive k (bRequiredAge a g delta j) := by
    intro j k
    unfold bEntitlement bRequiredAge
    split_ifs <;> rfl
  have hA : ∀ k s t : ℕ, bAlive k s * bAlive k t = bAlive k (max s t) := by
    intro k s t
    unfold bAlive
    by_cases h1 : s ≤ k <;> by_cases h2 : t ≤ k <;> simp [h1, h2, max_le_iff]
  unfold bSecondMoment bProjectedSecondMoment bPathPV bSurvival
  simp_rw [hE, sq, Finset.sum_mul_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hi : (a ≤ i ∧ i < a+n) <;> by_cases hj : (a ≤ j ∧ j < a+n) <;> simp only [hi, hj, and_self, and_false, false_and, if_true, if_false, ite_true, ite_false, mul_zero, zero_mul, Finset.sum_const_zero, and_true, true_and]
  apply Finset.sum_congr rfl
  intro k _
  rw [← hA]
  ring
