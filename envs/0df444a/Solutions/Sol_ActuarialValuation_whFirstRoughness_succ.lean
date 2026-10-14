-- Prove2me | solution 1 for ActuarialValuation.whFirstRoughness_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T06:38:02.588623+00:00
-- url     : https://prove2.me/submissions/23520bf6-cf08-44a4-b566-6cc73c07885f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whFirstDifference
import Definitions.Def_actuarial_whFirstRoughness

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (g : ℕ → ℝ) (n : ℕ) : whFirstRoughness g (n+1) = whFirstRoughness g n + (whFirstDifference g n)^2 := by
  simp [whFirstRoughness, Finset.sum_range_succ]
