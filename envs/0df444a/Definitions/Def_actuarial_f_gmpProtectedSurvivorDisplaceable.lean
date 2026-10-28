-- Prove2me | Definitions.Def_actuarial_f_gmpProtectedSurvivorDisplaceable
-- name    : actuarial_f_gmpProtectedSurvivorDisplaceable
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:47:35.097819+00:00
-- url     : https://prove2.me/theorems/f48fd14e-abfc-4997-b56b-dda70f1fc1a9
-- title:
--   Only non-statutory survivor surplus can be displaced
-- statement:
--   Calculate any replaceable amount as the positive surplus of the contractual spouse instalment over its statutory minimum.
--
--   The defining expression is:
--
--   $$
--   O^S_t=\mathbf1_{\mathrm{replace}}\max(0,C^S_t-M^S_t)
--   $$
-- source:
--   Original derived UK DB pension valuation. Statutory context: PSA 1993 sections 17, 87–92 and 109, https://www.legislation.gov.uk/ukpga/1993/48/section/109; Pensions Act 1995 section 53, https://www.legislation.gov.uk/ukpga/1995/26/section/53; HMRC Pensions Tax Manual PTM071500, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm071500. Full statutory anti-franking, allowable offset credits, GMP revaluation modes and exact survivor eligibility remain externally certified inputs. The estate guarantee replacement is a conditional illustrative contract, not a legal assertion.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def gmpProtectedSurvivorDisplaceable
    (replace : Prop) (contractual statutoryMinimum : ℝ) : ℝ := by
  classical
  exact if replace then max 0 (contractual - statutoryMinimum) else 0
end ActuarialUnderpinsF


