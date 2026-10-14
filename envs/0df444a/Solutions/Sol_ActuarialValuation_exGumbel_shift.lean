-- Prove2me | solution 1 for ActuarialValuation.exGumbel_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:50:24.066083+00:00
-- url     : https://prove2.me/submissions/811ba5dd-ea23-4462-b84a-547013dcee5a

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exGumbelMaxCdf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (mu sigma x shift : ℝ) : exGumbelMaxCdf (mu+shift) sigma (x+shift)=exGumbelMaxCdf mu sigma x := by
  unfold exGumbelMaxCdf
  have h : (x + shift) - (mu + shift) = x - mu := by ring
  rw [h]
