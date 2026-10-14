-- Prove2me | solution 1 for ActuarialValuation.irDeflate_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:58:56.802985+00:00
-- url     : https://prove2.me/submissions/7beba656-35a5-4379-b19f-e862ea5a2499

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irDeflate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b base hist : ℝ) : irDeflate (a+b) base hist=irDeflate a base hist+irDeflate b base hist := by
  unfold irDeflate
  ring
