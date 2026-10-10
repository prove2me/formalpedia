-- Prove2me | solution 1 for ActuarialValuation.ruinNextSurplus_zero_claim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:40:59.745985+00:00
-- url     : https://prove2.me/submissions/171c04d8-ee3f-401e-94af-8684c6d66543

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinNextSurplus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u : ℤ) (c : ℕ) :
  ruinNextSurplus u c 0 = u + (c : ℤ) := by
  simp [ruinNextSurplus]
