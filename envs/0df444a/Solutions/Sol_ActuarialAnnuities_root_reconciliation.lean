-- Prove2me | solution 1 for ActuarialAnnuities.root_reconciliation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:12:44.933059+00:00
-- url     : https://prove2.me/submissions/5982eb4f-e5df-4bcb-8471-22c207cb7d68

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bTotal
import Definitions.Def_actuarial_bSurvival
import Definitions.Def_actuarial_bExpectedPV
import Definitions.Def_actuarial_bSurvivalPV
import Definitions.Def_actuarial_bGuaranteedPV
import Definitions.Def_actuarial_bPostGuaranteePV
import Definitions.Def_actuarial_bLevel

namespace ActuarialAnnuities

lemma aH_ex (h a n g δ : ℕ) (v : ℝ) (b p : ℕ → ℝ) :
    bExpectedPV h a n g δ v b p = bSurvivalPV h a n g δ v b p := by
  unfold bExpectedPV bPathPV bSurvivalPV bSurvival bEntitlement
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  by_cases hC : a ≤ j ∧ j < a + n
  · simp only [if_pos hC]
    by_cases hg : j < a + g
    · simp only [if_pos hg, Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
    · simp only [if_neg hg, Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
  · simp [if_neg hC]

lemma aH_gp (h a n g δ : ℕ) (v : ℝ) (b p : ℕ → ℝ) :
    bSurvivalPV h a n g δ v b p = bGuaranteedPV h a n g δ v b p + bPostGuaranteePV h a n g δ v b p := by
  unfold bSurvivalPV bGuaranteedPV bPostGuaranteePV
  rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _
  split_ifs <;> first | (exfalso; omega) | ring1 | simp_all

lemma aH_S_succ (h j : ℕ) (p : ℕ → ℝ) (hj : j ≤ h) :
    bSurvival h p j = p j + bSurvival h p (j+1) := by
  unfold bSurvival bAlive
  have e : ∀ k, p k * (if j ≤ k then (1:ℝ) else 0) =
      (if k = j then p k else 0) + p k * (if j+1 ≤ k then (1:ℝ) else 0) := by
    intro k; split_ifs <;> first | (exfalso; omega) | ring
  rw [Finset.sum_congr rfl (fun k _ => e k), Finset.sum_add_distrib, Finset.sum_ite_eq']
  rw [if_pos (by simp; omega)]

lemma aH_S0 (h : ℕ) (p : ℕ → ℝ) : bSurvival h p 0 = bTotal h p := by
  unfold bSurvival bTotal bAlive; simp

lemma aH_Sh (h : ℕ) (p : ℕ → ℝ) : bSurvival h p (h+1) = 0 := by
  unfold bSurvival bAlive; apply Finset.sum_eq_zero; intro k hk
  simp at hk; simp [show ¬ (h+1 ≤ k) by omega]

lemma aH_lvl (h δ : ℕ) (v : ℝ) (p : ℕ → ℝ) :
    bSurvivalPV h 0 h 0 δ v (bLevel 1) p = ∑ j ∈ Finset.range h, v^(j+δ) * bSurvival h p (j+δ) := by
  unfold bSurvivalPV bLevel; apply Finset.sum_congr rfl; intro j hj; simp at hj; simp [hj]


end ActuarialAnnuities

open ActuarialAnnuities

theorem solution (h a n g : ℕ) (v : ℝ) (b p : ℕ → ℝ) (hn : ∀ k, 0 ≤ p k) (hp : bTotal h p = 1) (hv : 0 < v) (hv1 : v ≤ 1) : (bExpectedPV h a n g 0 v b p = bSurvivalPV h a n g 0 v b p) ∧ (bExpectedPV h a n g 1 v b p = bSurvivalPV h a n g 1 v b p) ∧ (bSurvivalPV h a n g 0 v b p = bGuaranteedPV h a n g 0 v b p+bPostGuaranteePV h a n g 0 v b p) ∧ (bSurvivalPV h a n g 1 v b p = bGuaranteedPV h a n g 1 v b p+bPostGuaranteePV h a n g 1 v b p) ∧ (bExpectedPV h 0 h 0 0 v (bLevel 1) p-bExpectedPV h 0 h 0 1 v (bLevel 1) p=1-v^h*bSurvival h p h) := by
  refine ⟨aH_ex _ _ _ _ _ _ _ _, aH_ex _ _ _ _ _ _ _ _, aH_gp _ _ _ _ _ _ _ _, aH_gp _ _ _ _ _ _ _ _, ?_⟩
  · rw [aH_ex, aH_ex, aH_lvl, aH_lvl, ← Finset.sum_sub_distrib]
    simp only [add_zero]
    rw [Finset.sum_range_sub' (fun j => v^j * bSurvival h p j) h]
    simp only [pow_zero, one_mul]
    rw [aH_S0, hp]


