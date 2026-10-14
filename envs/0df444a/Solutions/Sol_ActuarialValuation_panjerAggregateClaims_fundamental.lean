-- Prove2me | solution 1 for ActuarialValuation.panjerAggregateClaims_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:23:34.795795+00:00
-- url     : https://prove2.me/submissions/0e8d69f1-5bfc-45d4-86cc-a1c4759ea427

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerSeverityMean
import Definitions.Def_actuarial_panjerRecurrenceLaw
import Definitions.Def_actuarial_panjerFrequencyPremium
import Definitions.Def_actuarial_panjerAggregateCDF
import Definitions.Def_actuarial_panjerUpperTail
import Definitions.Def_actuarial_panjerStopLoss

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lambda : ℝ) (f g h : ℕ → ℝ) (hl : 0 ≤ lambda) (hf : ∀ j, 0 ≤ f j) (hfzero : f 0 = 0) (hg : panjerRecurrenceLaw lambda f g) (hh : panjerRecurrenceLaw lambda f h) (n : ℕ) (d : ℝ) : (∀ k : ℕ, g k = h k) ∧ (∀ k : ℕ, 0 ≤ g k) ∧ (panjerAggregateCDF g n + panjerUpperTail g n = 1) ∧ (0 ≤ panjerStopLoss g n d) ∧ (0 ≤ panjerFrequencyPremium lambda (panjerSeverityMean f n)) := by
  have huniq : ∀ k : ℕ, g k = h k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      cases k with
      | zero =>
        exact hg.1.trans hh.1.symm
      | succ k =>
        calc
          g (k + 1) = panjerRecursionStep lambda f g k := hg.2 k
          _ = panjerRecursionStep lambda f h k := by
            unfold panjerRecursionStep
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            have hlt : k - j < k + 1 := Nat.lt_succ_of_le (Nat.sub_le k j)
            rw [ih (k - j) hlt]
          _ = h (k + 1) := (hh.2 k).symm
  have hnn : ∀ k : ℕ, 0 ≤ g k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      cases k with
      | zero =>
        rw [hg.1]
        exact le_of_lt (Real.exp_pos _)
      | succ k =>
        rw [hg.2 k]
        unfold panjerRecursionStep
        apply mul_nonneg
        · apply div_nonneg hl
          positivity
        · apply Finset.sum_nonneg
          intro j hj
          unfold panjerWeightedSeverity
          apply mul_nonneg
          · exact mul_nonneg (by positivity) (hf (j + 1))
          · exact ih (k - j) (Nat.lt_succ_of_le (Nat.sub_le k j))
  have htail : panjerAggregateCDF g n + panjerUpperTail g n = 1 := by
    unfold panjerUpperTail
    ring
  have hstop : 0 ≤ panjerStopLoss g n d := by
    unfold panjerStopLoss
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (le_max_right _ _) (hnn k)
  have hmean : 0 ≤ panjerSeverityMean f n := by
    unfold panjerSeverityMean
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (by positivity) (hf k)
  have hpremium : 0 ≤ panjerFrequencyPremium lambda (panjerSeverityMean f n) := by
    unfold panjerFrequencyPremium
    exact mul_nonneg hl hmean
  exact ⟨huniq, hnn, htail, hstop, hpremium⟩
