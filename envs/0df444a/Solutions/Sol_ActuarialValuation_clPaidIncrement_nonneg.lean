-- Prove2me | solution 1 for ActuarialValuation.clPaidIncrement_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:13:01.404996+00:00
-- url     : https://prove2.me/submissions/29949e16-aeb7-4b12-8d99-98f7a9e41325

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clPaidIncrement

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℕ → ℝ) (i j : ℕ) (h : p i j ≤ p i (j+1)) : 0 ≤ clPaidIncrement p i j := by
  change 0 ≤ p i (j + 1) - p i j
  exact sub_nonneg.mpr h
