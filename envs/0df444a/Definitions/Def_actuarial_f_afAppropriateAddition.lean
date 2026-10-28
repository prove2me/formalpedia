-- Prove2me | Definitions.Def_actuarial_f_afAppropriateAddition
-- name    : actuarial_f_afAppropriateAddition
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:50:32.388109+00:00
-- url     : https://prove2.me/theorems/467485e6-3b08-4091-ad8b-ead1a70c6e97
-- title:
--   Appropriate addition under section 89
-- statement:
--   Combine certified post-cessation accrual and enhancement of the non-GMP pension for postponement. Scheme law determines both components.
--
--   The formal Lean declaration explicitly identifies the pension/cessation inputs, units and cases.
-- source:
--   Original derived statutory UK DB benefit contracts based on Pension Schemes Act 1993 sections 87–92 (including statutory relevant sum, appropriate addition, later earnings addition and exclusions), https://www.legislation.gov.uk/ukpga/1993/48/part/IV/chapter/III; and Pensions Act 1995 section 53 (next-year above-statutory credit and full deemed increase), https://www.legislation.gov.uk/ukpga/1995/26/section/53. Historic cessation-date definitions and GMP age, s88 pension-at-cessation or short service benefits, s89 additional accrual and postponement enhancements, and the s90(3) assumed earnings/GMP inputs must be certified member-by-member. The ordinary member/survivor branches exclude complete substituted benefits requiring alternative s87(3)(a) treatment, and do not by themselves implement all of sections 87–92, section 91 special service rules or s92 commutation disregard. Monetary inputs are weekly unless explicitly converted, and section 53 credits are already certified amounts.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def afAppropriateAddition
    (newAccrual lateUnguaranteedEnhancement : ℝ) : ℝ :=
  newAccrual + lateUnguaranteedEnhancement
end ActuarialUnderpinsF


