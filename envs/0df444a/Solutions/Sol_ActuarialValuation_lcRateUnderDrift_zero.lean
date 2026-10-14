-- Prove2me | solution 1 for ActuarialValuation.lcRateUnderDrift_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:29:01.628407+00:00
-- url     : https://prove2.me/submissions/19ca5700-ca11-4223-8356-cd56c3ff9dc0

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcRate
import Definitions.Def_actuarial_lcDriftIndex
import Definitions.Def_actuarial_lcRateUnderDrift

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b initial drift : ℝ) :
    lcRateUnderDrift a b initial drift 0 = lcRate a b initial := by
  simp [lcRateUnderDrift, lcDriftIndex]
