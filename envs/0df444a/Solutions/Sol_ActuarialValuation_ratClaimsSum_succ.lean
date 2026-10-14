-- Prove2me | solution 1 for ActuarialValuation.ratClaimsSum_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:08:25.996339+00:00
-- url     : https://prove2.me/submissions/87368d36-f06a-4ffa-b4d3-60a16a1b0b99

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratClaimsSum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (n : ℕ) : ratClaimsSum l (n+1) = ratClaimsSum l n + l n := by
  simp [ratClaimsSum, Finset.sum_range_succ]
