-- Prove2me | solution 1 for ActuarialValuation.pvLoss_zero_premium
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:54:35.791871+00:00
-- url     : https://prove2.me/submissions/b7dd298c-56a1-4021-a61f-c830272d95a8

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvLoss

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (benefit annuity : Fin n → ℝ) (i : Fin n) : pvLoss benefit annuity 0 i = benefit i := by
  simp [pvLoss, pvPremium]
