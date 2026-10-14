-- Prove2me | solution 1 for ActuarialValuation.pen9RequiredContribution_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:15:06.667962+00:00
-- url     : https://prove2.me/submissions/8d9ed958-cf6e-488e-a66e-0cf068e5e5c2

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9RequiredContribution

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (reserve exitPV pActive next : ℝ) : reserve+pen9RequiredContribution reserve exitPV pActive next = exitPV+pActive*next := by
  unfold pen9RequiredContribution
  ring
