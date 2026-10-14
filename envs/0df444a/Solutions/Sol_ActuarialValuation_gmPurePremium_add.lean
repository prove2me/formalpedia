-- Prove2me | solution 1 for ActuarialValuation.gmPurePremium_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:41:01.860932+00:00
-- url     : https://prove2.me/submissions/0d038534-cc02-47c7-b7e6-45ac79526d2c

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmPurePremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (frequency s1 s2 : ℝ) :
    gmPurePremium frequency (s1 + s2) =
      gmPurePremium frequency s1 + gmPurePremium frequency s2 := by
  simp only [gmPurePremium, mul_add]
