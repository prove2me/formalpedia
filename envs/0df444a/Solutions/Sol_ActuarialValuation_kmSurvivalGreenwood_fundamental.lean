-- Prove2me | solution 1 for ActuarialValuation.kmSurvivalGreenwood_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:03:56.278424+00:00
-- url     : https://prove2.me/submissions/6e49173e-b152-45c3-9c3e-311e91207cd3

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Definitions.Def_actuarial_kmSurvival
import Definitions.Def_actuarial_kmFailure
import Definitions.Def_actuarial_kmGreenwoodTerm
import Definitions.Def_actuarial_kmGreenwoodSum
import Definitions.Def_actuarial_kmGreenwoodVariance
import Definitions.Def_actuarial_kmRestrictedLife

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (risk deaths : ℕ → ℝ) (n : ℕ)
    (hr : ∀ t ∈ Finset.range (n+1), 0 < risk t)
    (hd : ∀ t ∈ Finset.range (n+1), 0 ≤ deaths t ∧ deaths t < risk t) :
    (0 ≤ kmSurvival risk deaths (n+1)) ∧
      (kmSurvival risk deaths (n+1) ≤ kmSurvival risk deaths n) ∧
      (kmSurvival risk deaths (n+1) + kmFailure risk deaths (n+1) = 1) ∧
      (0 ≤ kmGreenwoodVariance risk deaths (n+1)) ∧
      (0 ≤ kmRestrictedLife risk deaths (n+1)) := by
  have hfactor_nonneg (t : ℕ) (ht : t ∈ Finset.range (n+1)) :
      0 ≤ kmSurvivalFactor (deaths t) (risk t) := by
    have hrt := hr t ht
    have hdt := hd t ht
    unfold kmSurvivalFactor kmDeathHazard
    rw [sub_nonneg]
    exact (div_le_one₀ hrt).2 (le_of_lt hdt.2)
  have hfactor_le_one (t : ℕ) (ht : t ∈ Finset.range (n+1)) :
      kmSurvivalFactor (deaths t) (risk t) ≤ 1 := by
    have hrt := hr t ht
    have hdt := hd t ht
    unfold kmSurvivalFactor kmDeathHazard
    exact sub_le_self 1 (div_nonneg hdt.1 hrt.le)
  have hsurvival_nonneg (m : ℕ) (hm : m ≤ n+1) :
      0 ≤ kmSurvival risk deaths m := by
    unfold kmSurvival
    apply Finset.prod_nonneg
    intro t ht
    apply hfactor_nonneg
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp ht) hm)
  have hsurvival_succ : kmSurvival risk deaths (n+1) =
      kmSurvival risk deaths n * kmSurvivalFactor (deaths n) (risk n) := by
    simp [kmSurvival, Finset.prod_range_succ]
  have hn : n ∈ Finset.range (n+1) := Finset.mem_range.mpr (Nat.lt_succ_self n)
  have hgreenwood_term_nonneg (t : ℕ) (ht : t ∈ Finset.range (n+1)) :
      0 ≤ kmGreenwoodTerm (deaths t) (risk t) := by
    have hdt := hd t ht
    unfold kmGreenwoodTerm
    apply div_nonneg hdt.1
    exact mul_nonneg (le_trans hdt.1 (le_of_lt hdt.2)) (sub_nonneg.mpr (le_of_lt hdt.2))
  have hgreenwood_sum_nonneg : 0 ≤ kmGreenwoodSum risk deaths (n+1) :=
    by
      unfold kmGreenwoodSum
      exact Finset.sum_nonneg fun t ht => hgreenwood_term_nonneg t ht
  refine ⟨hsurvival_nonneg (n+1) le_rfl, ?_, ?_, ?_, ?_⟩
  · rw [hsurvival_succ]
    exact mul_le_of_le_one_right (hsurvival_nonneg n (Nat.le_succ n)) (hfactor_le_one n hn)
  · rw [kmFailure, add_comm]
    exact sub_add_cancel 1 (kmSurvival risk deaths (n+1))
  · unfold kmGreenwoodVariance
    exact mul_nonneg (sq_nonneg (kmSurvival risk deaths (n+1))) hgreenwood_sum_nonneg
  · unfold kmRestrictedLife
    apply Finset.sum_nonneg
    intro t ht
    exact hsurvival_nonneg t (le_of_lt (Finset.mem_range.mp ht))
