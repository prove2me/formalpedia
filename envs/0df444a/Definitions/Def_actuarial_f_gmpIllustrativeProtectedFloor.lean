-- Prove2me | Definitions.Def_actuarial_f_gmpIllustrativeProtectedFloor
-- name    : actuarial_f_gmpIllustrativeProtectedFloor
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:43:17.700179+00:00
-- url     : https://prove2.me/theorems/fcf7caea-a2ab-44bd-940e-c60e1d12e192
-- title:
--   Protected-excess floor, not full anti-franking
-- statement:
--   Illustrative externally certified protected excess and GMP minimum must both be respected without reducing the total pension. This is NOT the complete statutory anti-franking test.
--
--   The defining relation is:
--
--   $$
--   P_{\min}=\max(P_{\mathrm{old}},G+E_{\mathrm{protected}})
--   $$
-- source:
--   Original explicitly specified UK pension scheme model. Pension Schemes Act 1993 s109: full annual post-1988 GMP statutory order with cap of 3%, effective 6 April after the GMP becomes payable, without first-period pro-rating; no corresponding statutory increase to pre-1988 GMP. https://www.legislation.gov.uk/ukpga/1993/48/section/109. HMRC GMP first-increase guidance: https://www.gov.uk/guidance/provide-a-pension-for-your-scheme-member. Section 110 sets GMP increase funding restrictions and Pensions Act 1995 s53 provides permitted reductions for other increases; not all are modelled. Anti-franking statutory sections 87-92 are NOT fully implemented: the protected-excess floor is an externally supplied illustrative minimum, not a legal certification. GMP payable date, scheme-specific pre-GPD revaluation, survivor eligibility/amounts and calendar-date inputs must be independently verified for each scheme.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def gmpIllustrativeProtectedFloor
    (gmpMinimum protectedExcess currentTotal : ℝ) : ℝ :=
  max currentTotal (gmpMinimum + protectedExcess)
end ActuarialUnderpinsF


