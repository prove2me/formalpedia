-- Prove2me | Definitions.Def_actuarial_f_afMemberRelevantSum
-- name    : actuarial_f_afMemberRelevantSum
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:50:23.395836+00:00
-- url     : https://prove2.me/theorems/b427b9bb-4018-4164-90e9-ef75d2bdb037
-- title:
--   Member relevant sum under section 88
-- statement:
--   Depending on whether normal pension age was reached, select the appropriate post-cessation pension rate or separately assessed preserved/short-service rate; both require certification under section 88.
--
--   The formal Lean declaration explicitly identifies the pension/cessation inputs, units and cases.
-- source:
--   Original derived statutory UK DB benefit contracts based on Pension Schemes Act 1993 sections 87–92 (including statutory relevant sum, appropriate addition, later earnings addition and exclusions), https://www.legislation.gov.uk/ukpga/1993/48/part/IV/chapter/III; and Pensions Act 1995 section 53 (next-year above-statutory credit and full deemed increase), https://www.legislation.gov.uk/ukpga/1995/26/section/53. Historic cessation-date definitions and GMP age, s88 pension-at-cessation or short service benefits, s89 additional accrual and postponement enhancements, and the s90(3) assumed earnings/GMP inputs must be certified member-by-member. The ordinary member/survivor branches exclude complete substituted benefits requiring alternative s87(3)(a) treatment, and do not by themselves implement all of sections 87–92, section 91 special service rules or s92 commutation disregard. Monetary inputs are weekly unless explicitly converted, and section 53 credits are already certified amounts.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def afMemberRelevantSum
    (atNormalPensionAge : Bool) (pensionAfterCessation : ℝ)
    (shortServiceOrPreservedBenefit : ℝ) : ℝ :=
  if atNormalPensionAge then pensionAfterCessation else
    shortServiceOrPreservedBenefit
end ActuarialUnderpinsF


