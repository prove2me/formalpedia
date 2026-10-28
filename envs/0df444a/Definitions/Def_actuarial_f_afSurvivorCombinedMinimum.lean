-- Prove2me | Definitions.Def_actuarial_f_afSurvivorCombinedMinimum
-- name    : actuarial_f_afSurvivorCombinedMinimum
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T13:03:17.15781+00:00
-- url     : https://prove2.me/theorems/4d13e0f7-dc84-4520-8d01-09ccba0fcdf7
-- title:
--   Combined survivor GMP and anti-franking minimum
-- statement:
--   Protect the larger of independently certified survivor GMP and section 87(2) anti-franking minimum, in common monthly units.
--
--   The formal Lean declaration explicitly identifies the pension/cessation inputs, units and cases.
-- source:
--   Original derived statutory UK DB benefit contracts based on Pension Schemes Act 1993 sections 87–92 (including statutory relevant sum, appropriate addition, later earnings addition and exclusions), https://www.legislation.gov.uk/ukpga/1993/48/part/IV/chapter/III; and Pensions Act 1995 section 53 (next-year above-statutory credit and full deemed increase), https://www.legislation.gov.uk/ukpga/1995/26/section/53. Historic cessation-date definitions and GMP age, s88 pension-at-cessation or short service benefits, s89 additional accrual and postponement enhancements, and the s90(3) assumed earnings/GMP inputs must be certified member-by-member. The ordinary member/survivor branches exclude complete substituted benefits requiring alternative s87(3)(a) treatment, and do not by themselves implement all of sections 87–92, section 91 special service rules or s92 commutation disregard. Monetary inputs are weekly unless explicitly converted, and section 53 credits are already certified amounts.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_afStatutoryWeeklyToMonthly

namespace ActuarialUnderpinsF
noncomputable def afSurvivorCombinedMinimum
    (contractualGmpMinimum survivorAntiFrankingWeekly : ℝ) : ℝ :=
  max contractualGmpMinimum
    (afStatutoryWeeklyToMonthly survivorAntiFrankingWeekly)
end ActuarialUnderpinsF


