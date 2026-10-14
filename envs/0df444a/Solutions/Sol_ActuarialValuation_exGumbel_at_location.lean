-- Prove2me | solution 1 for ActuarialValuation.exGumbel_at_location
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:45:40.599005+00:00
-- url     : https://prove2.me/submissions/826e4281-6bd3-4a47-9af6-29e25905c0b7

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exGumbelMaxCdf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (mu sigma : ℝ) (hs : sigma≠0) : exGumbelMaxCdf mu sigma mu=Real.exp (-1) := by
  unfold exGumbelMaxCdf
  have h0 : (-(mu - mu) / sigma) = 0 := by simp
  rw [h0, Real.exp_zero]
