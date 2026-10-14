-- Prove2me | solution 1 for ActuarialValuation.tailTailRisk_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:45:47.753715+00:00
-- url     : https://prove2.me/submissions/9e9a0174-f08f-470e-98ac-e43ba4da14c6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Definitions.Def_actuarial_tailMass
import Definitions.Def_actuarial_tailLossMean
import Definitions.Def_actuarial_tailStopLoss
import Definitions.Def_actuarial_tailCVaRObjective
import Definitions.Def_actuarial_tailCDF
import Definitions.Def_actuarial_tailUpperMass
import Definitions.Def_actuarial_tailShiftObjective

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℝ) (n : ℕ) (a t s : ℝ) (ha : a < 1)
    (hp : ∀ k ∈ Finset.range (n+1), 0 ≤ p k) :
    (0 ≤ tailStopLoss p n t) ∧ (t ≤ tailCVaRObjective p n a t)
      ∧ (tailShiftObjective p n a t s = tailCVaRObjective p n a t + s)
      ∧ (tailCDF p n n + tailUpperMass p n n = tailMass p n)
      ∧ (tailStopLoss p n 0 = tailLossMean p n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold tailStopLoss
    apply Finset.sum_nonneg
    intro k hk
    refine mul_nonneg ?_ (hp k hk)
    first
    | (simp [tailExcess]; done)
    | (unfold tailExcess; positivity)
    | (simp only [tailExcess]; positivity)
    | (unfold tailExcess; simp; done)
  · unfold tailCVaRObjective
    have hSL : 0 ≤ tailStopLoss p n t := by
      unfold tailStopLoss
      apply Finset.sum_nonneg
      intro k hk
      refine mul_nonneg ?_ (hp k hk)
      first
      | (simp [tailExcess]; done)
      | (unfold tailExcess; positivity)
      | (simp only [tailExcess]; positivity)
      | (unfold tailExcess; simp; done)
    have h1a : (0 : ℝ) < 1 - a := by linarith
    have hdiv : (0 : ℝ) ≤ tailStopLoss p n t / (1 - a) := div_nonneg hSL h1a.le
    linarith
  · have hsum : (∑ k ∈ Finset.range (n+1), tailShiftExcess (k : ℝ) s t * p k)
        = ∑ k ∈ Finset.range (n+1), tailExcess (k : ℝ) t * p k := by
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      unfold tailShiftExcess tailExcess
      congr 1
      ring
    unfold tailShiftObjective tailCVaRObjective tailStopLoss
    rw [hsum]
    ring
  · unfold tailCDF tailUpperMass tailMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases h : k ≤ n
    · have hnt : ¬ n < k := not_lt.mpr h
      simp [h, hnt]
    · have ht : n < k := by omega
      simp [h, ht]
  · unfold tailStopLoss tailLossMean
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    unfold tailExcess
    rw [sub_zero]
    exact max_eq_left (Nat.cast_nonneg k)
