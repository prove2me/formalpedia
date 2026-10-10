-- Prove2me | solution 1 for ActuarialValuation.trancheIndividualFactor_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:04:02.885854+00:00
-- url     : https://prove2.me/submissions/74bd7471-1516-4db6-8eae-fa4a166bc9dd

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_trancheIndividualFactor
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (A D : ℕ → ℝ) (i : ℕ)
  (hA : 0 < A i) (hD : 0 ≤ D i) :
  0 ≤ trancheIndividualFactor A D i := by
  dsimp [trancheIndividualFactor]
  exact div_nonneg hD (le_of_lt hA)
