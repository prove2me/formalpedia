-- Prove2me | solution 1 for ActuarialValuation.commDiscountedLives_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:10:47.030887+00:00
-- url     : https://prove2.me/submissions/ac42b403-9852-491e-a38b-1bd36d9d213f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (v : ℝ) (x : ℕ) (hl : 0 ≤ l x) (hv : 0 ≤ v) : 0 ≤ commDiscountedLives l v x := by
  unfold commDiscountedLives
  exact mul_nonneg (pow_nonneg hv _) hl
