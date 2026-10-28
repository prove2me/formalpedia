-- Prove2me | Definitions.Def_actuarial_f_gmpPre88StatutoryGrowth
-- name    : actuarial_f_gmpPre88StatutoryGrowth
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:42:39.980122+00:00
-- url     : https://prove2.me/theorems/800cc7f4-422c-4bb0-ae38-65d0af453a52
-- title:
--   Pre-88 GMP statutory growth remains one
-- statement:
--   The separate pre-88 GMP component is unchanged by the section 109 statutory scheme increase rule.
--
--   The defining relation is:
--
--   $$
--   G_t^{\mathrm{pre88}}=1
--   $$
-- source:
--   Original explicitly specified UK pension scheme model. Pension Schemes Act 1993 s109: full annual post-1988 GMP statutory order with cap of 3%, effective 6 April after the GMP becomes payable, without first-period pro-rating; no corresponding statutory increase to pre-1988 GMP. https://www.legislation.gov.uk/ukpga/1993/48/section/109. HMRC GMP first-increase guidance: https://www.gov.uk/guidance/provide-a-pension-for-your-scheme-member. Section 110 sets GMP increase funding restrictions and Pensions Act 1995 s53 provides permitted reductions for other increases; not all are modelled. Anti-franking statutory sections 87-92 are NOT fully implemented: the protected-excess floor is an externally supplied illustrative minimum, not a legal certification. GMP payable date, scheme-specific pre-GPD revaluation, survivor eligibility/amounts and calendar-date inputs must be independently verified for each scheme.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def gmpPre88StatutoryGrowth
    (_payableFrom _date : ℕ) : ℝ :=
  1
end ActuarialUnderpinsF


