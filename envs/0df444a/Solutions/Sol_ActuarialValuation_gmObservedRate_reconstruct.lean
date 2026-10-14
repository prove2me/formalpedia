-- Prove2me | solution 1 for ActuarialValuation.gmObservedRate_reconstruct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:33:15.241481+00:00
-- url     : https://prove2.me/submissions/200c8a53-2a41-4776-8653-2f7bf8754fb8

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Definitions.Def_actuarial_gmObservedRate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (claims exposure : ℝ) (hE : exposure ≠ 0) :
    gmObservedRate claims exposure * exposure = claims := by
  unfold gmObservedRate
  field_simp
