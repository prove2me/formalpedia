-- Prove2me | Definitions.Def_actuarial_f_gmpMemberProtectedTopUp
-- name    : actuarial_f_gmpMemberProtectedTopUp
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:43:44.208046+00:00
-- url     : https://prove2.me/theorems/c5fe0b88-ed5c-4a3d-aa6d-6a4cae226043
-- title:
--   GMP member top-up only from commencement
-- statement:
--   Where GPD has passed and a member instalment is due, add only the shortfall below the supplied protected floor rather than adding GMP twice.
--
--   The defining relation is:
--
--   $$
--   T_t=\max(0,P_{\min}-P_t)
--   $$
-- source:
--   Original explicitly specified UK pension scheme model. Pension Schemes Act 1993 s109: full annual post-1988 GMP statutory order with cap of 3%, effective 6 April after the GMP becomes payable, without first-period pro-rating; no corresponding statutory increase to pre-1988 GMP. https://www.legislation.gov.uk/ukpga/1993/48/section/109. HMRC GMP first-increase guidance: https://www.gov.uk/guidance/provide-a-pension-for-your-scheme-member. Section 110 sets GMP increase funding restrictions and Pensions Act 1995 s53 provides permitted reductions for other increases; not all are modelled. Anti-franking statutory sections 87-92 are NOT fully implemented: the protected-excess floor is an externally supplied illustrative minimum, not a legal certification. GMP payable date, scheme-specific pre-GPD revaluation, survivor eligibility/amounts and calendar-date inputs must be independently verified for each scheme.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_memberDue
import Definitions.Def_actuarial_f_fixedChoicePayment
import Definitions.Def_actuarial_f_gmpMemberMinimumAtPayment
import Definitions.Def_actuarial_f_gmpIllustrativeProtectedFloor

namespace ActuarialUnderpinsF
noncomputable def gmpMemberProtectedTopUp
    (r z i t payableFrom : ℕ) (dateOf : ℕ → ℕ)
    (pre88 post88 protectedExcess : ℕ → ℝ)
    (orderRate : ℕ → ℝ) (a b c ga gb gc : ℕ → ℝ) : ℝ :=
  if payableFrom ≤ dateOf t then
    let current := fixedChoicePayment a b ga gb z t + c z * gc t
    let gmpMinimum :=
      gmpMemberMinimumAtPayment (pre88 z) (post88 z)
        payableFrom (dateOf t) orderRate
    (gmpIllustrativeProtectedFloor gmpMinimum
      (protectedExcess z) current - current) * memberDue r i t
  else 0
end ActuarialUnderpinsF


