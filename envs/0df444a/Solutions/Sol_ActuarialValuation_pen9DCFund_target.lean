-- Prove2me | solution 1 for ActuarialValuation.pen9DCFund_target
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:14:14.351736+00:00
-- url     : https://prove2.me/submissions/bf8f81f4-0e9a-4351-9ab4-80095cc0066b

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_pen9AccumFactor
import Definitions.Def_actuarial_pen9DCFund
import Definitions.Def_actuarial_pen9ReversionaryAnnuity
import Definitions.Def_actuarial_pen9TargetCapital
import Definitions.Def_actuarial_pen9RequiredDCRate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (s : ℕ → ℝ) (j : ℝ) (n : ℕ) (retSalary ratio member spouse reversion : ℝ) (hF : pen9AccumFactor s j n ≠ 0) : pen9DCFund (pen9RequiredDCRate (pen9TargetCapital retSalary ratio (pen9ReversionaryAnnuity member spouse reversion)) (pen9AccumFactor s j n)) s j n = pen9TargetCapital retSalary ratio (pen9ReversionaryAnnuity member spouse reversion) := by
  unfold pen9DCFund pen9RequiredDCRate
  field_simp [hF] <;> ring
