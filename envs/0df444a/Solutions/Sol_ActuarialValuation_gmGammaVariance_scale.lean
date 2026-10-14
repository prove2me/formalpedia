-- Prove2me | solution 1 for ActuarialValuation.gmGammaVariance_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:37:58.220255+00:00
-- url     : https://prove2.me/submissions/699c9018-76ed-4cd1-9a98-6385698a56d4

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_gmGammaVariance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (mean shape factor : ℝ) :
    gmGammaVariance (factor * mean) shape =
      factor ^ 2 * gmGammaVariance mean shape := by
  unfold gmGammaVariance
  ring
