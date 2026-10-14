-- Prove2me | solution 1 for ActuarialValuation.alterationReserveRelease_equals_deduction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:18:42.355983+00:00
-- url     : https://prove2.me/submissions/d7df8288-033b-4578-8c4a-983e2751d507

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationSurrenderValue
import Definitions.Def_actuarial_alterationReserveRelease

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (V c : ℝ) : alterationReserveRelease V (alterationSurrenderValue V c) = c := by
  unfold alterationReserveRelease alterationSurrenderValue
  ring
