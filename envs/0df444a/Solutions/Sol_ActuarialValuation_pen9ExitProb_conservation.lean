-- Prove2me | solution 1 for ActuarialValuation.pen9ExitProb_conservation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:04:21.968661+00:00
-- url     : https://prove2.me/submissions/2e24364c-ac74-4f36-bade-57a5dd5bd514

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9ExitMass
import Definitions.Def_actuarial_pen9ActiveProbability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (w d i r : ℝ) : pen9ActiveProbability w d i r + pen9ExitMass w d i r = 1 := by
  unfold pen9ActiveProbability
  ring
