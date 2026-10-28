-- Prove2me | Definitions.Def_actuarial_f_gmpMemberMinimumAtPayment
-- name    : actuarial_f_gmpMemberMinimumAtPayment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:43:08.072955+00:00
-- url     : https://prove2.me/theorems/35dd2181-767f-4c32-9936-e5a0c398987a
-- title:
--   Post-88 GMP increases but pre-88 GMP does not
-- statement:
--   The member statutory GMP floor includes an unchanged pre-88 part and a fully 6-April-indexed post-88 part.
--
--   The defining relation is:
--
--   $$
--   G_t=G_{88-}+G_{88+}I_t
--   $$
-- source:
--   Original explicitly specified UK pension scheme model. Pension Schemes Act 1993 s109: full annual post-1988 GMP statutory order with cap of 3%, effective 6 April after the GMP becomes payable, without first-period pro-rating; no corresponding statutory increase to pre-1988 GMP. https://www.legislation.gov.uk/ukpga/1993/48/section/109. HMRC GMP first-increase guidance: https://www.gov.uk/guidance/provide-a-pension-for-your-scheme-member. Section 110 sets GMP increase funding restrictions and Pensions Act 1995 s53 provides permitted reductions for other increases; not all are modelled. Anti-franking statutory sections 87-92 are NOT fully implemented: the protected-excess floor is an externally supplied illustrative minimum, not a legal certification. GMP payable date, scheme-specific pre-GPD revaluation, survivor eligibility/amounts and calendar-date inputs must be independently verified for each scheme.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpPost88StatutoryGrowth

namespace ActuarialUnderpinsF
noncomputable def gmpMemberMinimumAtPayment
    (pre88AtPayable post88AtPayable : ℝ)
    (payableFrom date : ℕ) (orderRate : ℕ → ℝ) : ℝ :=
  pre88AtPayable +
    post88AtPayable * gmpPost88StatutoryGrowth
      payableFrom date orderRate
end ActuarialUnderpinsF


