-- Prove2me | solution 1 for ActuarialAnnuities.root_full_reconciliation_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:12:59.319168+00:00
-- url     : https://prove2.me/submissions/543d4512-4dcf-4438-aa9d-685837d1d127

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bTotal
import Definitions.Def_actuarial_bExpectedPV
import Definitions.Def_actuarial_bSurvivalPV
import Definitions.Def_actuarial_bGuaranteedPV
import Definitions.Def_actuarial_bPostGuaranteePV
import Definitions.Def_actuarial_bLevel
import Definitions.Def_actuarial_bSecondMoment
import Definitions.Def_actuarial_bAssurancePV
import Definitions.Def_actuarial_bProjectedSecondMoment
import Definitions.Def_actuarial_bFractionalExpectedPV
import Definitions.Def_actuarial_bFractionalSurvivalPV

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
namespace ActuarialAnnuities

lemma aH_sm (h a n g δ : ℕ) (v : ℝ) (b p : ℕ → ℝ) :
    bSecondMoment h a n g δ v b p = bProjectedSecondMoment h a n g δ v b p := by
  have hE : ∀ i j k, bEntitlement a g δ i k * bEntitlement a g δ j k =
      bAlive k (max (bRequiredAge a g δ i) (bRequiredAge a g δ j)) := by
    intro i j k
    unfold bEntitlement bRequiredAge bAlive
    simp only [max_le_iff]
    split_ifs <;> first | (exfalso; omega) | norm_num | simp_all
  unfold bSecondMoment bProjectedSecondMoment bPathPV bSurvival
  simp_rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
  by_cases hi : a ≤ i ∧ i < a + n <;> by_cases hj : a ≤ j ∧ j < a + n
  · simp only [hi, hj, and_self, if_true]
    apply Finset.sum_congr rfl; intro k _
    rw [← hE]; ring
  all_goals simp [hi, hj]


end ActuarialAnnuities

open ActuarialAnnuities

theorem solution (h a n g m : ℕ) (v w : ℝ) (b p : ℕ → ℝ) (hp : bTotal h p = 1) (hn : ∀ k, 0 ≤ p k) (hv : 0 < v) (hv1 : v ≤ 1) (hw : 0 < w) (hm : 0 < m) : (bExpectedPV h a n g 0 v b p = bSurvivalPV h a n g 0 v b p) ∧ (bExpectedPV h a n g 1 v b p = bSurvivalPV h a n g 1 v b p) ∧ (bSurvivalPV h a n g 0 v b p = bGuaranteedPV h a n g 0 v b p+bPostGuaranteePV h a n g 0 v b p) ∧ (bSecondMoment h a n g 0 v b p = bProjectedSecondMoment h a n g 0 v b p) ∧ (bAssurancePV h v p+(1-v)*bSurvivalPV h 0 h 0 0 v (bLevel 1) p = 1-v^h*p h) ∧ (bFractionalExpectedPV h a n g 0 m w b p = bFractionalSurvivalPV h a n g 0 m w b p) := by
  refine ⟨aH_ex _ _ _ _ _ _ _ _, aH_ex _ _ _ _ _ _ _ _, aH_gp _ _ _ _ _ _ _ _, aH_sm _ _ _ _ _ _ _ _, ?_, ?_⟩
  · rw [aH_lvl]; simp only [add_zero]
    have key : ∀ j ∈ Finset.range h, (1 - v) * (v^j * bSurvival h p j) =
        (v^j * bSurvival h p j - v^(j+1) * bSurvival h p (j+1)) - p j * v^(j+1) := by
      intro j hj
      rw [aH_S_succ h j p (by simp at hj; omega)]; ring
    rw [Finset.mul_sum, Finset.sum_congr rfl key, Finset.sum_sub_distrib,
      Finset.sum_range_sub' (fun j => v^j * bSurvival h p j) h]
    unfold bAssurancePV
    have hSh : bSurvival h p h = p h := by rw [aH_S_succ h h p le_rfl, aH_Sh, add_zero]
    rw [hSh, pow_zero, one_mul, aH_S0, hp]
    ring
  · unfold bFractionalExpectedPV bFractionalSurvivalPV; exact aH_ex _ _ _ _ _ _ _ _


