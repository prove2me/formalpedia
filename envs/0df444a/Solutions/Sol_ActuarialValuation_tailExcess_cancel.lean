-- Prove2me | solution 1 for ActuarialValuation.tailExcess_cancel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:27:06.984409+00:00
-- url     : https://prove2.me/submissions/e295f724-22e1-4b71-b646-b46aaa0c62c5

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Definitions.Def_actuarial_tailExcess
import Definitions.Def_actuarial_tailShortfall

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x t : ℝ) :
    tailExcess x t - tailShortfall x t = x - t := by
  unfold tailExcess tailShortfall
  simp only [max_def]
  split_ifs <;> linarith
