-- Prove2me | Definitions.Def_actuarial_f_gmpPre88StatutoryIncrease
-- name    : actuarial_f_gmpPre88StatutoryIncrease
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:42:16.901798+00:00
-- url     : https://prove2.me/theorems/2532c33f-c366-4937-be54-f57b02822c0e
-- title:
--   Pre-88 GMP has nil section 109 increase
-- statement:
--   Pre-1988 GMP has no statutory section 109 pension-in-payment increase, without prohibiting any scheme-rule discretionary increase.
--
--   The defining relation is:
--
--   $$
--   u^{\mathrm{pre88}}_y=0
--   $$
-- source:
--   Original explicitly specified UK pension scheme model. Pension Schemes Act 1993 s109: full annual post-1988 GMP statutory order with cap of 3%, effective 6 April after the GMP becomes payable, without first-period pro-rating; no corresponding statutory increase to pre-1988 GMP. https://www.legislation.gov.uk/ukpga/1993/48/section/109. HMRC GMP first-increase guidance: https://www.gov.uk/guidance/provide-a-pension-for-your-scheme-member. Section 110 sets GMP increase funding restrictions and Pensions Act 1995 s53 provides permitted reductions for other increases; not all are modelled. Anti-franking statutory sections 87-92 are NOT fully implemented: the protected-excess floor is an externally supplied illustrative minimum, not a legal certification. GMP payable date, scheme-specific pre-GPD revaluation, survivor eligibility/amounts and calendar-date inputs must be independently verified for each scheme.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def gmpPre88StatutoryIncrease
    (_payableFrom _date _year : ℕ) : ℝ :=
  0
end ActuarialUnderpinsF


