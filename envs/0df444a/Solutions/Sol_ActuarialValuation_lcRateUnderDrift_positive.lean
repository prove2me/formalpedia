-- Prove2me | solution 1 for ActuarialValuation.lcRateUnderDrift_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:29:32.063983+00:00
-- url     : https://prove2.me/submissions/7806f37f-bf76-4966-a70c-c8ea79e01a2c

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcRate
import Definitions.Def_actuarial_lcRateUnderDrift

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b initial drift : ℝ) (n : ℕ) :
    0 < lcRateUnderDrift a b initial drift n := by
  unfold lcRateUnderDrift lcRate
  exact Real.exp_pos _
