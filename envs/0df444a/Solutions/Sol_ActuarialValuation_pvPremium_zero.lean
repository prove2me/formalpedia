-- Prove2me | solution 1 for ActuarialValuation.pvPremium_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:53:12.239702+00:00
-- url     : https://prove2.me/submissions/553ff015-5f82-4fd2-8769-b7110264a2c2

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (annuity : Fin n → ℝ) (i : Fin n) : pvPremium annuity 0 i = 0 := by
  simp [pvPremium]
