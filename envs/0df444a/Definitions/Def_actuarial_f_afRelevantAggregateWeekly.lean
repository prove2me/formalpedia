-- Prove2me | Definitions.Def_actuarial_f_afRelevantAggregateWeekly
-- name    : actuarial_f_afRelevantAggregateWeekly
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:50:57.378633+00:00
-- url     : https://prove2.me/theorems/cdec928f-c61f-4f1f-9073-a08e5ef06713
-- title:
--   Anti-franking protected relevant aggregate
-- statement:
--   Calculate weekly relevant sum plus the GMP increase since cessation, the appropriate addition and any later earnings addition under section 87(4).
--
--   The formal Lean declaration explicitly identifies the pension/cessation inputs, units and cases.
-- source:
--   Original derived statutory UK DB benefit contracts based on Pension Schemes Act 1993 sections 87–92 (including statutory relevant sum, appropriate addition, later earnings addition and exclusions), https://www.legislation.gov.uk/ukpga/1993/48/part/IV/chapter/III; and Pensions Act 1995 section 53 (next-year above-statutory credit and full deemed increase), https://www.legislation.gov.uk/ukpga/1995/26/section/53. Historic cessation-date definitions and GMP age, s88 pension-at-cessation or short service benefits, s89 additional accrual and postponement enhancements, and the s90(3) assumed earnings/GMP inputs must be certified member-by-member. The ordinary member/survivor branches exclude complete substituted benefits requiring alternative s87(3)(a) treatment, and do not by themselves implement all of sections 87–92, section 91 special service rules or s92 commutation disregard. Monetary inputs are weekly unless explicitly converted, and section 53 credits are already certified amounts.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def afRelevantAggregateWeekly
    (relevantSum gmpIncrease appropriateAddition laterEarnings : ℝ) : ℝ :=
  relevantSum + gmpIncrease + appropriateAddition + laterEarnings
end ActuarialUnderpinsF


