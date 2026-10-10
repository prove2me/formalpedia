-- Prove2me | solution 1 for ActuarialValuation.trancheSchemeComparatorPV_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:04:54.517067+00:00
-- url     : https://prove2.me/submissions/8e3b81df-2d89-4621-9423-0904cf043199

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_trancheSchemeComparatorPV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (P D : ℕ → ℝ) :
  trancheSchemeComparatorPV P D 0 = 0 := by
  simp [trancheSchemeComparatorPV]
