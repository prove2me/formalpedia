-- Prove2me | solution 1 for ActuarialValuation.pfSurplus_assets
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:35:48.605917+00:00
-- url     : https://prove2.me/submissions/cc154ea1-0e2c-4a0f-add8-ec6e1bd98c5a

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfSurplus
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (assets liabilities extra : ℝ) : pfSurplus (assets+extra) liabilities=pfSurplus assets liabilities+extra := by
  unfold pfSurplus
  ring
