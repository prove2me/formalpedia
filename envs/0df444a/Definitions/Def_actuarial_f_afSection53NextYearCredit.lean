-- Prove2me | Definitions.Def_actuarial_f_afSection53NextYearCredit
-- name    : actuarial_f_afSection53NextYearCredit
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T13:03:34.360176+00:00
-- url     : https://prove2.me/theorems/4206a482-c10b-4c15-a203-7362636a8e31
-- title:
--   Next-tax-year qualified increase credit
-- statement:
--   Conditional next-tax-year section 53 credit. Pension-credit-attributable pensions are excluded. All credit amounts and section 51/109 allocation eligibility require separate certification. The declared Lean statement is open.
-- source:
--   Pensions Act 1995 section 53(1)-(3A): https://www.legislation.gov.uk/ukpga/1995/26/section/53

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def afSection53NextYearCredit
    (voluntaryTaxYear obligationTaxYear : ℕ)
    (attributableToPensionCredit : Bool)
    (eligibleNonstatutoryExcess : ℝ) : ℝ :=
  if obligationTaxYear = voluntaryTaxYear + 1 ∧
     attributableToPensionCredit = false then
    max 0 eligibleNonstatutoryExcess else 0
end ActuarialUnderpinsF


