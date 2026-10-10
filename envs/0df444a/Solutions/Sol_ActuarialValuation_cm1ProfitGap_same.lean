-- Prove2me | solution 1 for ActuarialValuation.cm1ProfitGap_same
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:17:29.340889+00:00
-- url     : https://prove2.me/submissions/21c4881d-24b6-4c7e-8e2c-92432fdb3ca1

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ProfitGap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c : ℕ → ℝ) (n : ℕ) (i : ℝ) : cm1ProfitGap c c n i = 0 := by
  simp [cm1ProfitGap]
