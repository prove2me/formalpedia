-- Prove2me | solution 1 for ActuarialValuation.cm1ProfitGap_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:17:28.542982+00:00
-- url     : https://prove2.me/submissions/fff19429-b8a4-422a-98ac-a12bdacd291b

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1CashflowPV
import Definitions.Def_actuarial_cm1ProfitGap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a l : ℕ → ℝ) (i : ℝ) : cm1ProfitGap a l 0 i = 0 := by
  simp [cm1ProfitGap, cm1CashflowPV]
