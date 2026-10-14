-- Prove2me | solution 1 for ActuarialValuation.irReinflate_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:59:14.767082+00:00
-- url     : https://prove2.me/submissions/c027f6bc-64b1-424e-938b-5db809413cba

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irReinflate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b future base : ℝ) : irReinflate (a+b) future base=irReinflate a future base+irReinflate b future base := by
  unfold irReinflate
  ring
