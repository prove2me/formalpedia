-- Prove2me | solution 1 for ActuarialValuation.gamblerFairSuccess_harmonic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:56:46.611386+00:00
-- url     : https://prove2.me/submissions/a8e202de-da1e-4bc0-941e-e29530f7b7db

import Mathlib.Tactic
import Definitions.Def_actuarial_gamblerFairSuccess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (N i : ℕ) (hlo : 0 < i) (hhi : i < N) :
  gamblerFairSuccess N i =
    ((1 / 2 : ℝ) * gamblerFairSuccess N (i + 1)) +
    ((1 / 2 : ℝ) * gamblerFairSuccess N (i - 1)) := by
  have hN : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_trans hlo hhi))
  have hle : 1 ≤ i := hlo
  have hs : i - 1 + 1 = i := Nat.sub_add_cancel hle
  have hc : (((i - 1 : ℕ) : ℝ) + 1) = (i : ℝ) := by
    have hh := congrArg (fun k : ℕ => (k : ℝ)) hs
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  have hminus : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by linarith [hc]
  unfold gamblerFairSuccess
  rw [hminus, Nat.cast_add, Nat.cast_one]
  field_simp [hN]
  ring


