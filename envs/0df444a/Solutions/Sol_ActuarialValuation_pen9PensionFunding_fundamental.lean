-- Prove2me | solution 1 for ActuarialValuation.pen9PensionFunding_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:12:57.246415+00:00
-- url     : https://prove2.me/submissions/9ec5a21c-b0f9-4951-a917-b50d27f4aafa

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9AccumFactor
import Definitions.Def_actuarial_pen9DCFund
import Definitions.Def_actuarial_pen9ReversionaryAnnuity
import Definitions.Def_actuarial_pen9TargetCapital
import Definitions.Def_actuarial_pen9RequiredDCRate
import Definitions.Def_actuarial_pen9PUC
import Definitions.Def_actuarial_pen9TUC
import Definitions.Def_actuarial_pen9PUCNormalCost
import Definitions.Def_actuarial_pen9RequiredContribution
import Definitions.Def_actuarial_pen9ExitPV
import Definitions.Def_actuarial_pen9ActiveProbability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (salary : ℕ → ℝ) (investment : ℝ) (years service : ℕ) (retSalary replacement member spouse reversion accrual currentSalary projectedSalary pensionFactor : ℝ) (reserve discount w d i r bw bd bi br nextReserve : ℝ) (hF : pen9AccumFactor salary investment years ≠ 0) : (pen9DCFund (pen9RequiredDCRate (pen9TargetCapital retSalary replacement (pen9ReversionaryAnnuity member spouse reversion)) (pen9AccumFactor salary investment years)) salary investment years = pen9TargetCapital retSalary replacement (pen9ReversionaryAnnuity member spouse reversion)) ∧ (pen9PUC accrual projectedSalary pensionFactor (service+1) = pen9PUC accrual projectedSalary pensionFactor service + pen9PUCNormalCost accrual projectedSalary pensionFactor) ∧ (pen9PUC accrual projectedSalary pensionFactor service - pen9TUC accrual currentSalary pensionFactor service = accrual*(service:ℝ)*(projectedSalary-currentSalary)*pensionFactor) ∧ (reserve + pen9RequiredContribution reserve (pen9ExitPV discount w d i r bw bd bi br) (discount*pen9ActiveProbability w d i r) nextReserve = pen9ExitPV discount w d i r bw bd bi br + (discount*pen9ActiveProbability w d i r)*nextReserve) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [pen9DCFund, pen9RequiredDCRate]
    field_simp [hF] <;> ring
  · dsimp only [pen9PUC, pen9PUCNormalCost]
    push_cast
    ring
  · dsimp only [pen9PUC, pen9TUC]
    ring
  · dsimp only [pen9RequiredContribution]
    ring
