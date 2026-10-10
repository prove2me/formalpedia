-- Prove2me | solution 1 for ActuarialValuation.trancheAnnuityLedgerValue_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:03:48.960872+00:00
-- url     : https://prove2.me/submissions/2a4f80ed-85e2-4da5-a8db-2cd1f8260cb2

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_trancheAnnuityLedgerValue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (w : ℕ → ℕ → ℝ) (i : ℕ) :
  trancheAnnuityLedgerValue w i 0 = 0 := by
  simp [trancheAnnuityLedgerValue]
