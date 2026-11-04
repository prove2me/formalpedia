-- Prove2me | solution 1 for AIMInventory.UnknownRho.coupling
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T21:09:12.100785+00:00
-- url     : https://prove2.me/submissions/504c98d0-f91d-471d-aab9-b0d19f466c09

import Mathlib
import Definitions.Def_AIMInventory_UnknownRho_Model
open AIMInventory.UnknownRho

private lemma target_bounds (c : Parameters) (d : DemandPath) (n : ℕ) :
    0 ≤ (aimState c d n).1 ∧ (aimState c d n).1 ≤ c.barY := by
  cases n with
  | zero => exact ⟨c.initial_nonneg, c.initial_le⟩
  | succ n =>
    simp only [aimState]
    exact ⟨le_max_right _ _, max_le (min_le_right _ _) c.barY_pos.le⟩

private lemma step_nonneg (c : Parameters) (n : ℕ) : 0 ≤ stepSize c n := by
  unfold stepSize
  apply div_nonneg (mul_nonneg c.gamma_pos.le c.barY_pos.le)
  exact mul_nonneg ((le_max_left c.b c.h).trans' c.b_pos.le) (Real.sqrt_nonneg _)

private lemma target_drop (c : Parameters) (d : DemandPath) (n : ℕ) :
    (aimState c d n).1 - (aimState c d (n+1)).1 ≤ c.h * stepSize c (n+1) := by
  have hb := target_bounds c d n
  have hs := step_nonneg c (n+1)
  have hsl : observedSlope c (aimState c d n).1 (d n) ≤ c.h := by
    unfold observedSlope
    split_ifs <;> linarith [c.h_pos, c.b_pos]
  have hmul := mul_le_mul_of_nonneg_left hsl hs
  simp only [aimState]
  have hmin : (aimState c d n).1 - c.h * stepSize c (n+1) ≤
      min ((aimState c d n).1 - stepSize c (n+1) *
        observedSlope c (aimState c d n).1 (d n)) c.barY :=
    le_min (by nlinarith) (by nlinarith [c.h_pos])
  have := hmin.trans (le_max_left _ 0)
  linarith

theorem solution (c : Parameters) (d : DemandPath) (t : ℕ) (ht : 1 ≤ t) :
    aimLevel c d t - aimTarget c d t ≤ Z d (m c) t := by
  have hmain (n : ℕ) : (aimState c d n).2.1 - (aimState c d n).1 ≤ Z d (m c) (n+1) := by
    induction n with
    | zero => simp [aimState, Z]
    | succ n ih =>
      have hdrop := target_drop c d n
      have hb := (target_bounds c d (n+1)).1
      have heq : c.h * stepSize c (n+1) = m c / Real.sqrt ((n+1 : ℕ) : ℝ) := by
        unfold stepSize m
        ring
      rw [heq] at hdrop
      rw [Z, if_neg (by omega : n+1 ≠ 0), Nat.add_sub_cancel]
      simp only [aimState] at hb ⊢
      rw [sub_le_iff_le_add]
      apply max_le
      · have hz' : 0 ≤ max (Z d (m c) (n+1) + m c / Real.sqrt ((n+1 : ℕ) : ℝ) - (d n : ℝ)) 0 :=
          le_max_right _ _
        linarith
      · apply max_le
        · have hh := le_max_left (Z d (m c) (n+1) + m c / Real.sqrt ((n+1 : ℕ) : ℝ) - (d n : ℝ)) 0
          simp only [aimState] at hdrop
          linarith
        · have hh := le_max_right (Z d (m c) (n+1) + m c / Real.sqrt ((n+1 : ℕ) : ℝ) - (d n : ℝ)) 0
          linarith
  simpa [aimLevel, aimTarget, Nat.sub_add_cancel ht] using hmain (t-1)

#print axioms solution
