-- Prove2me | solution 1 for ActuarialValuation.whSecondRoughness_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T06:39:05.432188+00:00
-- url     : https://prove2.me/submissions/2fde0bc8-3bea-490f-a7f4-42a1bfb5e368

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whSecondDifference
import Definitions.Def_actuarial_whSecondRoughness

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (g : ℕ → ℝ) (n : ℕ) : whSecondRoughness g (n+1) = whSecondRoughness g n + (whSecondDifference g n)^2 := by
  simp [whSecondRoughness, Finset.sum_range_succ]
