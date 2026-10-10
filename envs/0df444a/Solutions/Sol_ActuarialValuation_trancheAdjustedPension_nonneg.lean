-- Prove2me | solution 1 for ActuarialValuation.trancheAdjustedPension_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:04:26.06822+00:00
-- url     : https://prove2.me/submissions/14d7c697-31fc-4d9e-b791-986ea56471fb

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_trancheAdjustedPension
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (P A D : ℕ → ℝ) (i : ℕ)
  (hP : 0 ≤ P i) (hA : 0 < A i) (hD : 0 ≤ D i) :
  0 ≤ trancheAdjustedPension P A D i := by
  unfold trancheAdjustedPension trancheIndividualFactor
  exact mul_nonneg hP (div_nonneg hD (le_of_lt hA))
