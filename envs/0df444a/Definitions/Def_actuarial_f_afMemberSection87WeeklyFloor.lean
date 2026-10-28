-- Prove2me | Definitions.Def_actuarial_f_afMemberSection87WeeklyFloor
-- name    : actuarial_f_afMemberSection87WeeklyFloor
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:51:17.058218+00:00
-- url     : https://prove2.me/theorems/48ddc407-9b51-4564-9991-23b3a560976f
-- title:
--   Conditional section 87 member weekly minimum
-- statement:
--   Conditional Pension Schemes Act 1993 section 87 calculation. Both historic exclusions, independently certified pre-1985 transfer-credit growth disregard, and the required post-cessation employment accrual eligibility are represented where relevant. This remains an open Lean statement and does not decide all statutory exceptions.
-- source:
--   Pension Schemes Act 1993 section 87(1)-(7), 88-92, https://www.legislation.gov.uk/ukpga/1993/48/section/87 (including section 87(4)(d) conditional later accrual, (5) pre-1985 transfer-credit GMP growth disregard, and (7)(a)-(b) historic exclusions). Certified dates, GMP growth exclusions and benefits are external inputs.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_afMemberGmpExcessSinceCessation
import Definitions.Def_actuarial_f_afRelevantAggregateWeekly
import Definitions.Def_actuarial_f_afMemberSection87Eligible

namespace ActuarialUnderpinsF
noncomputable def afMemberSection87WeeklyFloor
    (cessation gmpCommencement payment : ℕ)
    (leftBefore1985 contractedOutEndedBefore1985
       fullBenefitEntitled completeSubstitute laterAccrualApplies : Bool)
    (relevantSum currentGmp gmpAfterCessation : ℝ)
    (appropriateAddition laterEarnings excludedTransferGrowth : ℝ) : ℝ := by
  classical
  exact if afMemberSection87Eligible cessation gmpCommencement payment
       leftBefore1985 contractedOutEndedBefore1985
       fullBenefitEntitled completeSubstitute
       relevantSum currentGmp gmpAfterCessation excludedTransferGrowth then
      afRelevantAggregateWeekly relevantSum
        (afMemberGmpExcessSinceCessation currentGmp gmpAfterCessation
          - excludedTransferGrowth)
        appropriateAddition (if laterAccrualApplies then laterEarnings else 0)
    else 0
end ActuarialUnderpinsF


