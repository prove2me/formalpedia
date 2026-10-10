-- Prove2me | solution 1 for ActuarialValuation.gamblerFiniteSuccessRuin_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:50:48.91025+00:00
-- url     : https://prove2.me/submissions/ccf06dae-9920-4bbc-b66b-f6be68408cc3

import Mathlib.Tactic
import Definitions.Def_actuarial_gamblerFiniteSuccess
import Definitions.Def_actuarial_gamblerFiniteRuin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (N n i : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hN : 0 < N) :
    gamblerFiniteSuccess N p n i + gamblerFiniteRuin N p n i ≤ 1 := by
  induction n generalizing i with
  | zero =>
      change (if i = 0 then (0 : ℝ) else if N ≤ i then 1 else 0) +
        (if i = 0 then (1 : ℝ) else 0) ≤ 1
      split_ifs <;> norm_num
  | succ n ih =>
      by_cases hz : i = 0
      · simp [gamblerFiniteSuccess, gamblerFiniteRuin, hz]
      by_cases ht : N ≤ i
      · simp [gamblerFiniteSuccess, gamblerFiniteRuin, hz, ht]
      have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1
      have hup := mul_le_mul_of_nonneg_left (ih (i + 1)) hp0
      have hdown := mul_le_mul_of_nonneg_left (ih (i - 1)) hq
      rw [gamblerFiniteSuccess, gamblerFiniteRuin]
      simp only [if_neg hz, if_neg ht]
      nlinarith [hup, hdown]
