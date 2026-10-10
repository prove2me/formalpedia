-- Prove2me | solution 1 for ActuarialValuation.discreteStopLoss_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:31:18.592655+00:00
-- url     : https://prove2.me/submissions/2f2614a2-a210-45aa-930b-f3f9689cac29

import Mathlib
import Definitions.Def_actuarial_discreteStopLossLimitedMean
import Definitions.Def_actuarial_discreteStopLossPremium
import Definitions.Def_actuarial_discreteStopLossAggregateMean
import Definitions.Def_actuarial_discreteStopLossTail

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (bound deductible : ℕ)
  (hw : ∀ s, 0 ≤ w s) :
  (discreteStopLossLimitedMean w bound deductible +
    discreteStopLossPremium w bound deductible =
      discreteStopLossAggregateMean w bound) ∧
  (discreteStopLossPremium w bound deductible =
    ∑ j ∈ Finset.range (bound + 1),
      if deductible ≤ j then discreteStopLossTail w bound j else 0) ∧
  (discreteStopLossPremium w bound deductible +
    discreteStopLossPremium w bound (deductible + 2) ≥
      2 * discreteStopLossPremium w bound (deductible + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  ·
    unfold discreteStopLossLimitedMean discreteStopLossPremium
      discreteStopLossAggregateMean
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    have hp : min s deductible + discreteStopLossPayment s deductible = s := by
      simp only [discreteStopLossPayment]
      omega
    calc
      (min s deductible : ℝ) * w s +
          (discreteStopLossPayment s deductible : ℝ) * w s =
        ((min s deductible + discreteStopLossPayment s deductible : ℕ) : ℝ) * w s := by
          push_cast
          ring
      _ = (s : ℝ) * w s := by rw [hp]
  ·
    classical
    have hstep (j : ℕ) :
        discreteStopLossPremium w bound j =
          discreteStopLossPremium w bound (j + 1) +
            discreteStopLossTail w bound j := by
      unfold discreteStopLossPremium discreteStopLossTail
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hj : j < s
      · have hp : s - j = s - (j + 1) + 1 := by omega
        simp only [discreteStopLossPayment, if_pos hj]
        rw [hp]
        push_cast
        ring
      · have hle : s ≤ j := Nat.le_of_not_gt hj
        have hle1 : s ≤ j + 1 := by omega
        simp [discreteStopLossPayment, Nat.sub_eq_zero_of_le hle,
          Nat.sub_eq_zero_of_le hle1, hj]
    have hvanish (j : ℕ) (hj : bound ≤ j) :
        discreteStopLossPremium w bound j = 0 := by
      unfold discreteStopLossPremium
      apply Finset.sum_eq_zero
      intro s hs
      have hs : s ≤ bound := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
      simp [discreteStopLossPayment, Nat.sub_eq_zero_of_le (le_trans hs hj)]
    let f : ℕ → ℝ := fun j =>
      if deductible ≤ j then discreteStopLossPremium w bound j
      else discreteStopLossPremium w bound deductible
    have hf0 : f 0 = discreteStopLossPremium w bound deductible := by
      by_cases hd : deductible = 0
      · simp [f, hd]
      · have hnot : ¬ deductible ≤ 0 := by omega
        simp [f, hnot]
    have hfend : f (bound + 1) = 0 := by
      by_cases hd : deductible ≤ bound + 1
      · simp only [f, if_pos hd]
        exact hvanish (bound + 1) (by omega)
      · simp only [f, if_neg hd]
        exact hvanish deductible (by omega)
    have hdelta (j : ℕ) :
        (if deductible ≤ j then discreteStopLossTail w bound j else 0) =
          f j - f (j + 1) := by
      change (if deductible ≤ j then discreteStopLossTail w bound j else 0) =
        (if deductible ≤ j then discreteStopLossPremium w bound j
         else discreteStopLossPremium w bound deductible) -
        (if deductible ≤ j + 1 then discreteStopLossPremium w bound (j + 1)
         else discreteStopLossPremium w bound deductible)
      by_cases hj : deductible ≤ j
      · have hj1 : deductible ≤ j + 1 := by omega
        simp only [if_pos hj, if_pos hj1]
        have hs := hstep j
        linarith
      · by_cases hj1 : deductible ≤ j + 1
        · have heq : deductible = j + 1 := by omega
          simp only [if_neg hj, if_pos hj1]
          rw [heq]
          ring
        · simp only [if_neg hj, if_neg hj1]
          ring
    have htel (n : ℕ) :
        (∑ j ∈ Finset.range n, (f j - f (j + 1))) = f 0 - f n := by
      induction n with
      | zero => simp
      | succ k ih =>
          rw [Finset.sum_range_succ, ih]
          ring
    calc
      discreteStopLossPremium w bound deductible =
          f 0 - f (bound + 1) := by rw [hf0, hfend]; ring
      _ = ∑ j ∈ Finset.range (bound + 1), (f j - f (j + 1)) :=
        (htel (bound + 1)).symm
      _ = ∑ j ∈ Finset.range (bound + 1),
          if deductible ≤ j then discreteStopLossTail w bound j else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (hdelta j).symm
  ·
    unfold discreteStopLossPremium
    have hp :
        2 * (∑ s ∈ Finset.range (bound + 1),
          (discreteStopLossPayment s (deductible + 1) : ℝ) * w s) ≤
          ∑ s ∈ Finset.range (bound + 1),
            ((discreteStopLossPayment s deductible : ℝ) * w s +
            (discreteStopLossPayment s (deductible + 2) : ℝ) * w s) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro s hs
      have hnat :
          2 * (s - (deductible + 1)) ≤
            (s - deductible) + (s - (deductible + 2)) := by
        omega
      have hreal :
          (2 : ℝ) * (s - (deductible + 1) : ℕ) ≤
            (s - deductible : ℕ) + (s - (deductible + 2) : ℕ) := by
        exact_mod_cast hnat
      have hweighted := mul_le_mul_of_nonneg_right hreal (hw s)
      dsimp [discreteStopLossPayment]
      nlinarith
    rw [Finset.sum_add_distrib] at hp
    linarith
