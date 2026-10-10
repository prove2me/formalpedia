-- Prove2me | solution 1 for ActuarialValuation.trancheSchemeAdjustedPV_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:04:47.519375+00:00
-- url     : https://prove2.me/submissions/6501e55c-2bc5-4a23-9ef4-f426da136997

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_trancheSchemeAdjustedPV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (P A D : ℕ → ℝ) :
  trancheSchemeAdjustedPV P A D 0 = 0 := by
  simp [trancheSchemeAdjustedPV]
