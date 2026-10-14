-- Prove2me | solution 1 for ActuarialValuation.whRateResidual_reverse
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T06:26:14.909164+00:00
-- url     : https://prove2.me/submissions/05b7123d-bad1-41d5-b2b7-c37909baaaec

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whRateResidual
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (g q : ℝ) : whRateResidual g q = - whRateResidual q g := by
  simp only [whRateResidual]
  ring
