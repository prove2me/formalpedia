-- Prove2me | Definitions.Def_actuarial_f_gmpBoundedMemberProtectedTopUp
-- name    : actuarial_f_gmpBoundedMemberProtectedTopUp
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:50:04.30002+00:00
-- url     : https://prove2.me/theorems/a315934d-4feb-488a-a8bc-f3768727d9ff
-- title:
--   GPD-gated protected member pension top-up
-- statement:
--   Apply a GMP-plus-externally-certified-excess floor at or after the payable date, using bounded statutory GMP growth and only the positive shortfall.
--
--   The defining expression is:
--
--   $$
--   T_t=\mathbf1_{\mathrm{due,GPD}}\max(0,G_t+E_t-C_t)
--   $$
-- source:
--   Original derived UK DB pension valuation. Statutory context: PSA 1993 sections 17, 87–92 and 109, https://www.legislation.gov.uk/ukpga/1993/48/section/109; Pensions Act 1995 section 53, https://www.legislation.gov.uk/ukpga/1995/26/section/53; HMRC Pensions Tax Manual PTM071500, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm071500. Full statutory anti-franking, allowable offset credits, GMP revaluation modes and exact survivor eligibility remain externally certified inputs. The estate guarantee replacement is a conditional illustrative contract, not a legal assertion.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_memberDue
import Definitions.Def_actuarial_f_fixedChoicePayment
import Definitions.Def_actuarial_f_gmpBoundedMemberMinimum

namespace ActuarialUnderpinsF
noncomputable def gmpBoundedMemberProtectedTopUp
    (r z i t payableFrom : ℕ) (dateOf : ℕ → ℕ)
    (pre88 post88 protectedExcess : ℕ → ℝ)
    (orderRate a b c ga gb gc : ℕ → ℝ) : ℝ :=
  if payableFrom ≤ dateOf t then
    let current := fixedChoicePayment a b ga gb z t + c z * gc t
    let minimum := gmpBoundedMemberMinimum
      (pre88 z) (post88 z) payableFrom (dateOf t) orderRate
    (max current (minimum + protectedExcess z) - current) *
      memberDue r i t
  else 0
end ActuarialUnderpinsF


