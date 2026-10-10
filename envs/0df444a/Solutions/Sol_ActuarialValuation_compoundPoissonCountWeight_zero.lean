-- Prove2me | solution 1 for ActuarialValuation.compoundPoissonCountWeight_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:09:03.941275+00:00
-- url     : https://prove2.me/submissions/79475d16-189e-4e71-9136-a2b0606a84cc

import Mathlib
import Definitions.Def_actuarial_compoundPoissonCountWeight

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (rate : ℝ) :
  compoundPoissonCountWeight rate 0 = Real.exp (-rate) := by
  simp [compoundPoissonCountWeight]
