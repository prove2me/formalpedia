-- Prove2me | Definitions.Def_actuarial_f_afMemberGmpExcessSinceCessation
-- name    : actuarial_f_afMemberGmpExcessSinceCessation
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:50:50.003386+00:00
-- url     : https://prove2.me/theorems/a5d40e19-51ac-4e8f-b842-e7166de7937b
-- title:
--   GMP increase since cessation
-- statement:
--   Difference between the weekly GMP currently due and the weekly GMP at the statutory cessation baseline.
--
--   The formal Lean declaration explicitly identifies the pension/cessation inputs, units and cases.
-- source:
--   Original derived statutory UK DB benefit contracts based on Pension Schemes Act 1993 sections 87–92 (including statutory relevant sum, appropriate addition, later earnings addition and exclusions), https://www.legislation.gov.uk/ukpga/1993/48/part/IV/chapter/III; and Pensions Act 1995 section 53 (next-year above-statutory credit and full deemed increase), https://www.legislation.gov.uk/ukpga/1995/26/section/53. Historic cessation-date definitions and GMP age, s88 pension-at-cessation or short service benefits, s89 additional accrual and postponement enhancements, and the s90(3) assumed earnings/GMP inputs must be certified member-by-member. The ordinary member/survivor branches exclude complete substituted benefits requiring alternative s87(3)(a) treatment, and do not by themselves implement all of sections 87–92, section 91 special service rules or s92 commutation disregard. Monetary inputs are weekly unless explicitly converted, and section 53 credits are already certified amounts.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def afMemberGmpExcessSinceCessation
    (currentGmpAtPayment gmpAtCessation : ℝ) : ℝ :=
  currentGmpAtPayment - gmpAtCessation
end ActuarialUnderpinsF


