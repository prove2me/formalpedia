-- Prove2me | Definitions.Def_actuarial_f_gmpBoundedMemberMinimum
-- name    : actuarial_f_gmpBoundedMemberMinimum
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:46:47.562764+00:00
-- url     : https://prove2.me/theorems/a46b6797-210b-476a-9924-620e74bbd11e
-- title:
--   Statutory member GMP with bounded increase product
-- statement:
--   Add constant statutory pre-88 component to fully 6-April-increased post-88 component.
--
--   The defining expression is:
--
--   $$
--   G_t=G_-+G_+I_t
--   $$
-- source:
--   Original derived UK DB pension valuation. Statutory context: PSA 1993 sections 17, 87–92 and 109, https://www.legislation.gov.uk/ukpga/1993/48/section/109; Pensions Act 1995 section 53, https://www.legislation.gov.uk/ukpga/1995/26/section/53; HMRC Pensions Tax Manual PTM071500, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm071500. Full statutory anti-franking, allowable offset credits, GMP revaluation modes and exact survivor eligibility remain externally certified inputs. The estate guarantee replacement is a conditional illustrative contract, not a legal assertion.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpBoundedPost88Growth

namespace ActuarialUnderpinsF
noncomputable def gmpBoundedMemberMinimum
    (pre88AtPayable post88AtPayable : ℝ)
    (payableFrom date : ℕ) (orderRate : ℕ → ℝ) : ℝ :=
  pre88AtPayable +
    post88AtPayable * gmpBoundedPost88Growth payableFrom date orderRate
end ActuarialUnderpinsF


