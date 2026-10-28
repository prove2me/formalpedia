-- Prove2me | Definitions.Def_actuarial_f_gmpSurvivorMinimumAtPayment
-- name    : actuarial_f_gmpSurvivorMinimumAtPayment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:44:02.022156+00:00
-- url     : https://prove2.me/theorems/372e3fd2-11ee-4209-bfb5-e534f1467f33
-- title:
--   Qualifying survivor statutory GMP minimum
-- statement:
--   Use separately certified survivor eligibility and pre/post-88 GMP bases, with the post-88 element independently indexed after survivor commencement.
--
--   The defining relation is:
--
--   $$
--   G^S_t=\mathbf1_Q(G^S_{88-}+G^S_{88+}I^S_t)
--   $$
-- source:
--   Original explicitly specified UK pension scheme model. Pension Schemes Act 1993 s109: full annual post-1988 GMP statutory order with cap of 3%, effective 6 April after the GMP becomes payable, without first-period pro-rating; no corresponding statutory increase to pre-1988 GMP. https://www.legislation.gov.uk/ukpga/1993/48/section/109. HMRC GMP first-increase guidance: https://www.gov.uk/guidance/provide-a-pension-for-your-scheme-member. Section 110 sets GMP increase funding restrictions and Pensions Act 1995 s53 provides permitted reductions for other increases; not all are modelled. Anti-franking statutory sections 87-92 are NOT fully implemented: the protected-excess floor is an externally supplied illustrative minimum, not a legal certification. GMP payable date, scheme-specific pre-GPD revaluation, survivor eligibility/amounts and calendar-date inputs must be independently verified for each scheme.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpPost88StatutoryGrowth

namespace ActuarialUnderpinsF
noncomputable def gmpSurvivorMinimumAtPayment
    (z i t : ℕ) (dateOf : ℕ → ℕ)
    (qualifies : ℕ → ℕ → Bool)
    (survivorPre88 survivorPost88 : ℕ → ℕ → ℝ)
    (orderRate : ℕ → ℝ) : ℝ :=
  if qualifies z i then
    survivorPre88 z i +
      survivorPost88 z i *
        gmpPost88StatutoryGrowth (dateOf (i + 1))
          (dateOf t) orderRate
  else 0
end ActuarialUnderpinsF


