-- Prove2me | solution 1 for ActuarialValuation.cm1MacaulayDuration_cancel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:15:52.739202+00:00
-- url     : https://prove2.me/submissions/631cae12-3817-43ae-afb7-0f8b046f071f

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1CashflowPV
import Definitions.Def_actuarial_cm1DurationNumerator
import Definitions.Def_actuarial_cm1MacaulayDuration
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c : ℕ → ℝ) (n : ℕ) (i : ℝ) (hV : cm1CashflowPV c n i ≠ 0) : cm1MacaulayDuration c n i * cm1CashflowPV c n i = cm1DurationNumerator c n i := by
  simp [cm1MacaulayDuration, hV]
