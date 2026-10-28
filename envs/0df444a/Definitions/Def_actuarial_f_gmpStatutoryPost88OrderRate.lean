-- Prove2me | Definitions.Def_actuarial_f_gmpStatutoryPost88OrderRate
-- name    : actuarial_f_gmpStatutoryPost88OrderRate
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:41:55.00102+00:00
-- url     : https://prove2.me/theorems/5e1ab40f-6219-4ea7-a092-33908f2c75a6
-- title:
--   Full post-88 GMP annual rate
-- statement:
--   Clamp the supplied statutory GMP Increase Order percentage at 0% and 3%; this is not a first-period pro-rata calculation.
--
--   The defining relation is:
--
--   $$
--   u_y=\min(0.03,\max(0,q_y))
--   $$
-- source:
--   Original explicitly specified UK pension scheme model. Pension Schemes Act 1993 s109: full annual post-1988 GMP statutory order with cap of 3%, effective 6 April after the GMP becomes payable, without first-period pro-rating; no corresponding statutory increase to pre-1988 GMP. https://www.legislation.gov.uk/ukpga/1993/48/section/109. HMRC GMP first-increase guidance: https://www.gov.uk/guidance/provide-a-pension-for-your-scheme-member. Section 110 sets GMP increase funding restrictions and Pensions Act 1995 s53 provides permitted reductions for other increases; not all are modelled. Anti-franking statutory sections 87-92 are NOT fully implemented: the protected-excess floor is an externally supplied illustrative minimum, not a legal certification. GMP payable date, scheme-specific pre-GPD revaluation, survivor eligibility/amounts and calendar-date inputs must be independently verified for each scheme.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_lpiRate

namespace ActuarialUnderpinsF
noncomputable def gmpStatutoryPost88OrderRate
    (orderRate : ℕ → ℝ) (year : ℕ) : ℝ :=
  lpiRate 0 (3 / 100) (orderRate year)
end ActuarialUnderpinsF


