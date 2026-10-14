-- Prove2me | solution 1 for ActuarialValuation.ruTwoScenarioRuin_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T16:19:29.437032+00:00
-- url     : https://prove2.me/submissions/2b594c7e-6ca4-4af2-9f06-7871e96cb3f6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruTwoScenarioRuin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (a b : Bool) :
    0 ≤ ruTwoScenarioRuin p q a b := by
  cases a <;> cases b <;>
    simp [ruTwoScenarioRuin, hp, hq, add_nonneg hp hq]
