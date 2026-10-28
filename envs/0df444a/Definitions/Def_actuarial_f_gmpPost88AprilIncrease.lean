-- Prove2me | Definitions.Def_actuarial_f_gmpPost88AprilIncrease
-- name    : actuarial_f_gmpPost88AprilIncrease
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:42:10.272353+00:00
-- url     : https://prove2.me/theorems/754cf100-eded-4470-93cc-a23a90d06f65
-- title:
--   Post-88 GMP 6 April event rate
-- statement:
--   Apply the full ordered percentage at the first eligible 6 April and every subsequent eligible 6 April; no other calendar date triggers the event.
--
--   The defining relation is:
--
--   $$
--   u_{y,t}=\mathbf 1_{\{GPD<D_y\le t\}}q_y
--   $$
-- source:
--   Original explicitly specified UK pension scheme model. Pension Schemes Act 1993 s109: full annual post-1988 GMP statutory order with cap of 3%, effective 6 April after the GMP becomes payable, without first-period pro-rating; no corresponding statutory increase to pre-1988 GMP. https://www.legislation.gov.uk/ukpga/1993/48/section/109. HMRC GMP first-increase guidance: https://www.gov.uk/guidance/provide-a-pension-for-your-scheme-member. Section 110 sets GMP increase funding restrictions and Pensions Act 1995 s53 provides permitted reductions for other increases; not all are modelled. Anti-franking statutory sections 87-92 are NOT fully implemented: the protected-excess floor is an externally supplied illustrative minimum, not a legal certification. GMP payable date, scheme-specific pre-GPD revaluation, survivor eligibility/amounts and calendar-date inputs must be independently verified for each scheme.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpStatutoryAprilEligible
import Definitions.Def_actuarial_f_gmpStatutoryPost88OrderRate

namespace ActuarialUnderpinsF
noncomputable def gmpPost88AprilIncrease
    (payableFrom date : ℕ) (orderRate : ℕ → ℝ)
    (year : ℕ) : ℝ := by
  classical
  exact if gmpStatutoryAprilEligible payableFrom date year then
    gmpStatutoryPost88OrderRate orderRate year else 0
end ActuarialUnderpinsF


