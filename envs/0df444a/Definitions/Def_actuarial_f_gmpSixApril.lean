-- Prove2me | Definitions.Def_actuarial_f_gmpSixApril
-- name    : actuarial_f_gmpSixApril
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:41:30.618334+00:00
-- url     : https://prove2.me/theorems/59a3cd84-ace5-4826-926a-acca09cfd13d
-- title:
--   Six April event date
-- statement:
--   An actual 6 April event is encoded as a YYYYMMDD natural-number date.
--
--   The defining relation is:
--
--   $$
--   D_y=10000y+406
--   $$
-- source:
--   Original explicitly specified UK pension scheme model. Pension Schemes Act 1993 s109: full annual post-1988 GMP statutory order with cap of 3%, effective 6 April after the GMP becomes payable, without first-period pro-rating; no corresponding statutory increase to pre-1988 GMP. https://www.legislation.gov.uk/ukpga/1993/48/section/109. HMRC GMP first-increase guidance: https://www.gov.uk/guidance/provide-a-pension-for-your-scheme-member. Section 110 sets GMP increase funding restrictions and Pensions Act 1995 s53 provides permitted reductions for other increases; not all are modelled. Anti-franking statutory sections 87-92 are NOT fully implemented: the protected-excess floor is an externally supplied illustrative minimum, not a legal certification. GMP payable date, scheme-specific pre-GPD revaluation, survivor eligibility/amounts and calendar-date inputs must be independently verified for each scheme.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def gmpSixApril (year : ℕ) : ℕ :=
  year * 10000 + 406
end ActuarialUnderpinsF


