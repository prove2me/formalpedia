-- Prove2me | Definitions.Def_actuarial_f_afSurvivorSection87TopUp
-- name    : actuarial_f_afSurvivorSection87TopUp
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T13:03:02.945302+00:00
-- url     : https://prove2.me/theorems/586cf9f0-2ae8-4ec2-945f-abb01869e447
-- title:
--   Survivor section 87 payment protection
-- statement:
--   Add only the positive shortfall between contractual survivor instalment and the section 87 survivor floor, where a survivor payment is due.
--
--   The formal Lean declaration explicitly identifies the pension/cessation inputs, units and cases.
-- source:
--   Original derived statutory UK DB benefit contracts based on Pension Schemes Act 1993 sections 87–92 (including statutory relevant sum, appropriate addition, later earnings addition and exclusions), https://www.legislation.gov.uk/ukpga/1993/48/part/IV/chapter/III; and Pensions Act 1995 section 53 (next-year above-statutory credit and full deemed increase), https://www.legislation.gov.uk/ukpga/1995/26/section/53. Historic cessation-date definitions and GMP age, s88 pension-at-cessation or short service benefits, s89 additional accrual and postponement enhancements, and the s90(3) assumed earnings/GMP inputs must be certified member-by-member. The ordinary member/survivor branches exclude complete substituted benefits requiring alternative s87(3)(a) treatment, and do not by themselves implement all of sections 87–92, section 91 special service rules or s92 commutation disregard. Monetary inputs are weekly unless explicitly converted, and section 53 credits are already certified amounts.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseDue
import Definitions.Def_actuarial_f_afStatutoryWeeklyToMonthly

namespace ActuarialUnderpinsF
noncomputable def afSurvivorSection87TopUp
    (h i j t : ℕ) (contractMonthly weeklyFloor : ℝ) : ℝ :=
  max 0 (afStatutoryWeeklyToMonthly weeklyFloor - contractMonthly) *
    spouseDue h i j t
end ActuarialUnderpinsF


