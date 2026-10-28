-- Prove2me | Definitions.Def_actuarial_f_gmpStatutoryAprilEligible
-- name    : actuarial_f_gmpStatutoryAprilEligible
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:41:47.491191+00:00
-- url     : https://prove2.me/theorems/f395439f-69a0-4f34-8af7-f241bb4d4643
-- title:
--   6 April eligibility after GMP commencement
-- statement:
--   A statutory GMP increase event must be strictly later than GMP becoming payable, and no later than the payment date.
--
--   The defining relation is:
--
--   $$
--   GPD<D_y\le t
--   $$
-- source:
--   Original explicitly specified UK pension scheme model. Pension Schemes Act 1993 s109: full annual post-1988 GMP statutory order with cap of 3%, effective 6 April after the GMP becomes payable, without first-period pro-rating; no corresponding statutory increase to pre-1988 GMP. https://www.legislation.gov.uk/ukpga/1993/48/section/109. HMRC GMP first-increase guidance: https://www.gov.uk/guidance/provide-a-pension-for-your-scheme-member. Section 110 sets GMP increase funding restrictions and Pensions Act 1995 s53 provides permitted reductions for other increases; not all are modelled. Anti-franking statutory sections 87-92 are NOT fully implemented: the protected-excess floor is an externally supplied illustrative minimum, not a legal certification. GMP payable date, scheme-specific pre-GPD revaluation, survivor eligibility/amounts and calendar-date inputs must be independently verified for each scheme.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpSixApril

namespace ActuarialUnderpinsF
noncomputable def gmpStatutoryAprilEligible
    (payableFrom date : ℕ) (year : ℕ) : Prop :=
  payableFrom < gmpSixApril year ∧ gmpSixApril year ≤ date
end ActuarialUnderpinsF


