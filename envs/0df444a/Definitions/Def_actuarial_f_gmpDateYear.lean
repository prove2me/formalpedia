-- Prove2me | Definitions.Def_actuarial_f_gmpDateYear
-- name    : actuarial_f_gmpDateYear
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:41:37.135124+00:00
-- url     : https://prove2.me/theorems/3ab99bb1-340e-48d9-b5e9-ec909bdcbec0
-- title:
--   Extract year of dated GMP event
-- statement:
--   Recover the year from a YYYYMMDD integer; input date validity is external.
--
--   The defining relation is:
--
--   $$
--   y=\lfloor D/10000\rfloor
--   $$
-- source:
--   Original explicitly specified UK pension scheme model. Pension Schemes Act 1993 s109: full annual post-1988 GMP statutory order with cap of 3%, effective 6 April after the GMP becomes payable, without first-period pro-rating; no corresponding statutory increase to pre-1988 GMP. https://www.legislation.gov.uk/ukpga/1993/48/section/109. HMRC GMP first-increase guidance: https://www.gov.uk/guidance/provide-a-pension-for-your-scheme-member. Section 110 sets GMP increase funding restrictions and Pensions Act 1995 s53 provides permitted reductions for other increases; not all are modelled. Anti-franking statutory sections 87-92 are NOT fully implemented: the protected-excess floor is an externally supplied illustrative minimum, not a legal certification. GMP payable date, scheme-specific pre-GPD revaluation, survivor eligibility/amounts and calendar-date inputs must be independently verified for each scheme.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def gmpDateYear (date : ℕ) : ℕ :=
  date / 10000
end ActuarialUnderpinsF


