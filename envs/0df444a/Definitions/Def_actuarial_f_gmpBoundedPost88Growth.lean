-- Prove2me | Definitions.Def_actuarial_f_gmpBoundedPost88Growth
-- name    : actuarial_f_gmpBoundedPost88Growth
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:46:23.875721+00:00
-- url     : https://prove2.me/theorems/c046936e-36bb-4e12-ae94-90b002871e5c
-- title:
--   Bounded post-88 statutory 6 April accumulation
-- statement:
--   Compound whole post-88 GMP order rates over years from GPD rather than evaluating years from zero.
--
--   The defining expression is:
--
--   $$
--   I_t=\prod_{k=0}^{Y(t)-Y(GPD)}(1+u_{Y(GPD)+k,t})
--   $$
-- source:
--   Original derived UK DB pension valuation. Statutory context: PSA 1993 sections 17, 87–92 and 109, https://www.legislation.gov.uk/ukpga/1993/48/section/109; Pensions Act 1995 section 53, https://www.legislation.gov.uk/ukpga/1995/26/section/53; HMRC Pensions Tax Manual PTM071500, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm071500. Full statutory anti-franking, allowable offset credits, GMP revaluation modes and exact survivor eligibility remain externally certified inputs. The estate guarantee replacement is a conditional illustrative contract, not a legal assertion.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpDateYear
import Definitions.Def_actuarial_f_gmpPost88AprilIncrease

namespace ActuarialUnderpinsF
noncomputable def gmpBoundedPost88Growth
    (payableFrom date : ℕ) (orderRate : ℕ → ℝ) : ℝ :=
  ∏ k ∈ Finset.range (gmpDateYear date + 1 - gmpDateYear payableFrom),
    (1 + gmpPost88AprilIncrease payableFrom date orderRate
      (gmpDateYear payableFrom + k))
end ActuarialUnderpinsF


