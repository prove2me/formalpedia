-- Prove2me | Definitions.Def_actuarial_f_gmpSurvivorProtectedTopUp
-- name    : actuarial_f_gmpSurvivorProtectedTopUp
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:44:23.657604+00:00
-- url     : https://prove2.me/theorems/3341683b-f84a-4dc5-af4e-c3bb9a8cb127
-- title:
--   Survivor statutory guarantee overlays option-linked benefit
-- statement:
--   Apply a top-up above the elected option's survivor pension only if the statutory survivor minimum is higher and a survivor instalment is due.
--
--   The defining relation is:
--
--   $$
--   T^S_t=\max(0,G^S_t-P^S_t)
--   $$
-- source:
--   Original explicitly specified UK pension scheme model. Pension Schemes Act 1993 s109: full annual post-1988 GMP statutory order with cap of 3%, effective 6 April after the GMP becomes payable, without first-period pro-rating; no corresponding statutory increase to pre-1988 GMP. https://www.legislation.gov.uk/ukpga/1993/48/section/109. HMRC GMP first-increase guidance: https://www.gov.uk/guidance/provide-a-pension-for-your-scheme-member. Section 110 sets GMP increase funding restrictions and Pensions Act 1995 s53 provides permitted reductions for other increases; not all are modelled. Anti-franking statutory sections 87-92 are NOT fully implemented: the protected-excess floor is an externally supplied illustrative minimum, not a legal certification. GMP payable date, scheme-specific pre-GPD revaluation, survivor eligibility/amounts and calendar-date inputs must be independently verified for each scheme.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseDue
import Definitions.Def_actuarial_f_linkedSpouseBasis
import Definitions.Def_actuarial_f_gmpSurvivorMinimumAtPayment

namespace ActuarialUnderpinsF
noncomputable def gmpSurvivorProtectedTopUp
    (h z i j t : ℕ) (dateOf : ℕ → ℕ)
    (qualifies : ℕ → ℕ → Bool)
    (survivorPre88 survivorPost88 sa sb : ℕ → ℕ → ℝ)
    (a b orderRate : ℕ → ℝ) (gs : ℕ → ℕ → ℝ) : ℝ :=
  let minimum :=
    gmpSurvivorMinimumAtPayment z i t dateOf qualifies
      survivorPre88 survivorPost88 orderRate
  let alreadyPromised := linkedSpouseBasis a b sa sb z i * gs i t
  (max minimum alreadyPromised - alreadyPromised) * spouseDue h i j t
end ActuarialUnderpinsF


