-- Prove2me | solution 1 for ActuarialValuation.tailShiftExcess_same
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:38:23.391052+00:00
-- url     : https://prove2.me/submissions/82e2809a-3508-4c8f-af16-54e365acac5b

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Definitions.Def_actuarial_tailExcess
import Definitions.Def_actuarial_tailShiftExcess

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x t s : ℝ) :
    tailShiftExcess x s t = tailExcess x t := by
  unfold tailShiftExcess tailExcess
  congr 1
  ring
