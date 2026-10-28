-- Prove2me | Definitions.Def_actuarial_f_gmpPost88StatutoryGrowth
-- name    : actuarial_f_gmpPost88StatutoryGrowth
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:42:33.126756+00:00
-- url     : https://prove2.me/theorems/153f1df6-0168-4e6e-94be-0c0f07321f4a
-- title:
--   Compound whole post-88 GMP April orders
-- statement:
--   Multiply the full section 109 orders for every 6 April after GMP commencement and no later than payment date.
--
--   The defining relation is:
--
--   $$
--   G_t^{\mathrm{post88}}=\prod_{D_y\le t}(1+u_{y,t})
--   $$
-- source:
--   Original explicitly specified UK pension scheme model. Pension Schemes Act 1993 s109: full annual post-1988 GMP statutory order with cap of 3%, effective 6 April after the GMP becomes payable, without first-period pro-rating; no corresponding statutory increase to pre-1988 GMP. https://www.legislation.gov.uk/ukpga/1993/48/section/109. HMRC GMP first-increase guidance: https://www.gov.uk/guidance/provide-a-pension-for-your-scheme-member. Section 110 sets GMP increase funding restrictions and Pensions Act 1995 s53 provides permitted reductions for other increases; not all are modelled. Anti-franking statutory sections 87-92 are NOT fully implemented: the protected-excess floor is an externally supplied illustrative minimum, not a legal certification. GMP payable date, scheme-specific pre-GPD revaluation, survivor eligibility/amounts and calendar-date inputs must be independently verified for each scheme.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpDateYear
import Definitions.Def_actuarial_f_gmpPost88AprilIncrease

namespace ActuarialUnderpinsF
noncomputable def gmpPost88StatutoryGrowth
    (payableFrom date : ℕ) (orderRate : ℕ → ℝ) : ℝ :=
  ∏ year ∈ Finset.range (gmpDateYear date + 1),
    (1 + gmpPost88AprilIncrease payableFrom date orderRate year)
end ActuarialUnderpinsF


