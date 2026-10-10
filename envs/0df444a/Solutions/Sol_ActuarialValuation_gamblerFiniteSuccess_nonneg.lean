-- Prove2me | solution 1 for ActuarialValuation.gamblerFiniteSuccess_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:50:34.71121+00:00
-- url     : https://prove2.me/submissions/f0b06b30-4739-4860-a0d2-f77d84e5b272

import Mathlib.Tactic
import Definitions.Def_actuarial_gamblerFiniteSuccess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (N n i : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ gamblerFiniteSuccess N p n i := by
  induction n generalizing i with
  | zero =>
      change 0 ≤ (if i = 0 then (0 : ℝ) else if N ≤ i then 1 else 0)
      split_ifs <;> norm_num
  | succ n ih =>
      rw [gamblerFiniteSuccess]
      split_ifs with hz ht
      · norm_num
      · norm_num
      · exact add_nonneg
          (mul_nonneg hp0 (ih (i + 1)))
          (mul_nonneg (sub_nonneg.mpr hp1) (ih (i - 1)))
