-- Prove2me | Definitions.Def_actuarial_f_afSurvivorSection87WeeklyFloor
-- name    : actuarial_f_afSurvivorSection87WeeklyFloor
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T13:02:26.245417+00:00
-- url     : https://prove2.me/theorems/6b1c4695-917e-45f5-bc56-c5ac848ba049
-- title:
--   Conditional section 87 survivor weekly minimum
-- statement:
--   Conditional Pension Schemes Act 1993 section 87 calculation. Both historic exclusions, independently certified pre-1985 transfer-credit growth disregard, and the required post-cessation employment accrual eligibility are represented where relevant. This remains an open Lean statement and does not decide all statutory exceptions.
-- source:
--   Pension Schemes Act 1993 section 87(1)-(7), 88-92, https://www.legislation.gov.uk/ukpga/1993/48/section/87 (including section 87(4)(d) conditional later accrual, (5) pre-1985 transfer-credit GMP growth disregard, and (7)(a)-(b) historic exclusions). Certified dates, GMP growth exclusions and benefits are external inputs.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_afRelevantAggregateWeekly
import Definitions.Def_actuarial_f_afSurvivorSection87Eligible

namespace ActuarialUnderpinsF
noncomputable def afSurvivorSection87WeeklyFloor
    (cessation memberDeath gmpCommencement payment : ℕ)
    (leftBefore1985 contractedOutEndedBefore1985
       fullSurvivorEntitled completeSubstitute laterAccrualApplies : Bool)
    (survivorRelevantSum survivorGmpCurrent memberGmpAtCessation : ℝ)
    (appropriateAddition laterEarnings excludedTransferGrowth : ℝ) : ℝ := by
  classical
  exact if afSurvivorSection87Eligible cessation memberDeath
        gmpCommencement payment leftBefore1985 contractedOutEndedBefore1985 fullSurvivorEntitled
        completeSubstitute survivorRelevantSum survivorGmpCurrent
        memberGmpAtCessation excludedTransferGrowth then
     afRelevantAggregateWeekly survivorRelevantSum
       (survivorGmpCurrent - memberGmpAtCessation / 2 - excludedTransferGrowth)
       appropriateAddition (if laterAccrualApplies then laterEarnings else 0)
   else 0
end ActuarialUnderpinsF


