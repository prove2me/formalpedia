-- Prove2me | solution 1 for ActuarialValuation.gamblerFiniteRuin_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:50:37.704512+00:00
-- url     : https://prove2.me/submissions/d405a3e8-3513-40aa-ba48-ed95b676eed6

import Mathlib.Tactic
import Definitions.Def_actuarial_gamblerFiniteRuin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (N n i : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ gamblerFiniteRuin N p n i := by
  induction n generalizing i with
  | zero =>
      change 0 ≤ (if i = 0 then (1 : ℝ) else 0)
      split_ifs <;> norm_num
  | succ n ih =>
      rw [gamblerFiniteRuin]
      split_ifs with hz ht
      · norm_num
      · norm_num
      · exact add_nonneg
          (mul_nonneg hp0 (ih (i + 1)))
          (mul_nonneg (sub_nonneg.mpr hp1) (ih (i - 1)))
