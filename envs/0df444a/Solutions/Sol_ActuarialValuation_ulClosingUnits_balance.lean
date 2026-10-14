-- Prove2me | solution 1 for ActuarialValuation.ulClosingUnits_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:20:15.76874+00:00
-- url     : https://prove2.me/submissions/e6f6846a-c55a-459d-9337-26cdb31ea49a

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulClosingUnits

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (opening bought cancelled : ℝ) : ulClosingUnits opening bought cancelled+cancelled=opening+bought := by
  unfold ulClosingUnits
  ring
