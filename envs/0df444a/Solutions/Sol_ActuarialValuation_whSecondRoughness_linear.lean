-- Prove2me | solution 1 for ActuarialValuation.whSecondRoughness_linear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T06:55:38.127978+00:00
-- url     : https://prove2.me/submissions/592f543d-1cf8-44dd-9ab1-4a1a6304858e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whSecondRoughness
import Definitions.Def_actuarial_whLinearCurve
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b : ℝ) (n : ℕ) : whSecondRoughness (whLinearCurve a b) n = 0 := by
  unfold whSecondRoughness
  apply Finset.sum_eq_zero
  intro i hi
  have hz : whSecondDifference (whLinearCurve a b) i = 0 := by
    simp only [whSecondDifference, whFirstDifference, whLinearCurve,
      Nat.cast_add, Nat.cast_one]
    ring
  simp [hz]
