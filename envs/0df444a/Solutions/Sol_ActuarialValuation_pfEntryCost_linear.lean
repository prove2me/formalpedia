-- Prove2me | solution 1 for ActuarialValuation.pfEntryCost_linear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:57:51.891346+00:00
-- url     : https://prove2.me/submissions/47308284-ea01-43d6-b3e0-d24274e9556d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfEntryNormalCost
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (rate x y : ℝ) : pfEntryNormalCost rate (x+y)=pfEntryNormalCost rate x+pfEntryNormalCost rate y := by
  unfold pfEntryNormalCost
  ring
