-- Prove2me | solution 1 for ActuarialValuation.pucAmortisationRate_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:57:27.517978+00:00
-- url     : https://prove2.me/submissions/fd687b47-b4d3-4d8b-8a5b-731386a1c1ac

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucAmortisationRate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u base rate : ℝ) (hb : base ≠ 0) (h : rate * base = u) : rate = pucAmortisationRate u base := by
  change rate = u / base
  apply (eq_div_iff hb).2
  exact h
