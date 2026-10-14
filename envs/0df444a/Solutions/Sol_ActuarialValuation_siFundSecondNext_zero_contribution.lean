-- Prove2me | solution 1 for ActuarialValuation.siFundSecondNext_zero_contribution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:01:07.354991+00:00
-- url     : https://prove2.me/submissions/52ad5523-01c9-4d44-9bbe-8b1943684077

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siFundSecondNext

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (priorSecond priorMean secondGross : ℝ) : siFundSecondNext priorSecond priorMean 0 secondGross=priorSecond*secondGross := by
  unfold siFundSecondNext
  ring
