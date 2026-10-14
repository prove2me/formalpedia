-- Prove2me | solution 1 for ActuarialValuation.siFundMeanNext_zero_contribution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:00:10.08538+00:00
-- url     : https://prove2.me/submissions/75665769-911a-4bd7-b8c1-d7f8aca977b4

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siFundMeanNext

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (priorMean meanGross : ℝ) : siFundMeanNext priorMean 0 meanGross=priorMean*meanGross := by
  unfold siFundMeanNext
  ring
