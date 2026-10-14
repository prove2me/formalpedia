-- Prove2me | solution 1 for ActuarialValuation.clPriorUltimate_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:17:58.894544+00:00
-- url     : https://prove2.me/submissions/c53b2acd-506b-4c2f-875b-5288b6a9b705

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clPriorUltimate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p l : ℝ) (hp : 0 ≤ p) (hl : 0 ≤ l) : 0 ≤ clPriorUltimate p l := by
  change 0 ≤ p * l
  exact mul_nonneg hp hl
