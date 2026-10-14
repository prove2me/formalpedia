-- Prove2me | solution 1 for ActuarialValuation.bnPutCall_terminal_parity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:02:49.24591+00:00
-- url     : https://prove2.me/submissions/8cb0ccab-c2ed-46f2-a47b-c6070df168b5

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnCall
import Definitions.Def_actuarial_bnPut

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (s k : ℝ) : bnCall s k - bnPut s k = s-k := by
  unfold bnCall bnPut
  rcases le_total s k with hsk | hks
  · rw [max_eq_right (by linarith : s-k ≤ (0:ℝ))]
    rw [max_eq_left (by linarith : (0:ℝ) ≤ k-s)]
    ring
  · rw [max_eq_left (by linarith : (0:ℝ) ≤ s-k)]
    rw [max_eq_right (by linarith : k-s ≤ (0:ℝ))]
    ring
