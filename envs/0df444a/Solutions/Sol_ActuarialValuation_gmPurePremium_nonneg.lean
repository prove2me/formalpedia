-- Prove2me | solution 1 for ActuarialValuation.gmPurePremium_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:42:33.532638+00:00
-- url     : https://prove2.me/submissions/053eb9e1-5f77-4108-982a-a43f80425941

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmPurePremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (frequency severity : ℝ) (hf : 0 ≤ frequency)
    (hs : 0 ≤ severity) : 0 ≤ gmPurePremium frequency severity := by
  unfold gmPurePremium
  exact mul_nonneg hf hs
