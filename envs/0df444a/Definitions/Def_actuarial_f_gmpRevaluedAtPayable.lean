-- Prove2me | Definitions.Def_actuarial_f_gmpRevaluedAtPayable
-- name    : actuarial_f_gmpRevaluedAtPayable
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:42:46.502762+00:00
-- url     : https://prove2.me/theorems/72f51d01-0c72-4194-9d9d-39c74bdec924
-- title:
--   Revaluation at GMP commencement distinct from increases
-- statement:
--   Multiply GMP at leaving by scheme-specific pre-GPD revaluation factors, distinct from increases after GPD.
--
--   The defining relation is:
--
--   $$
--   GPD_{\mathrm{base}}=G_{88-}R_-+G_{88+}R_+
--   $$
-- source:
--   Original explicitly specified UK pension scheme model. Pension Schemes Act 1993 s109: full annual post-1988 GMP statutory order with cap of 3%, effective 6 April after the GMP becomes payable, without first-period pro-rating; no corresponding statutory increase to pre-1988 GMP. https://www.legislation.gov.uk/ukpga/1993/48/section/109. HMRC GMP first-increase guidance: https://www.gov.uk/guidance/provide-a-pension-for-your-scheme-member. Section 110 sets GMP increase funding restrictions and Pensions Act 1995 s53 provides permitted reductions for other increases; not all are modelled. Anti-franking statutory sections 87-92 are NOT fully implemented: the protected-excess floor is an externally supplied illustrative minimum, not a legal certification. GMP payable date, scheme-specific pre-GPD revaluation, survivor eligibility/amounts and calendar-date inputs must be independently verified for each scheme.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def gmpRevaluedAtPayable
    (pre88Leaving post88Leaving pre88Factor post88Factor : ℝ) :
    ℝ :=
  pre88Leaving * pre88Factor + post88Leaving * post88Factor
end ActuarialUnderpinsF


