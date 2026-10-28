-- Prove2me | Definitions.Def_actuarial_f_gmpProtectedSurvivorParallel
-- name    : actuarial_f_gmpProtectedSurvivorParallel
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:47:17.847771+00:00
-- url     : https://prove2.me/theorems/7f410982-bc03-4274-b111-490451d5c864
-- title:
--   Full contractual and statutory survivor floor
-- statement:
--   Pay the greater of the contractual survivor instalment and statutory protected minimum.
--
--   The defining expression is:
--
--   $$
--   P^S_t=\max(C^S_t,M^S_t)
--   $$
-- source:
--   Original derived UK DB pension valuation. Statutory context: PSA 1993 sections 17, 87–92 and 109, https://www.legislation.gov.uk/ukpga/1993/48/section/109; Pensions Act 1995 section 53, https://www.legislation.gov.uk/ukpga/1995/26/section/53; HMRC Pensions Tax Manual PTM071500, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm071500. Full statutory anti-franking, allowable offset credits, GMP revaluation modes and exact survivor eligibility remain externally certified inputs. The estate guarantee replacement is a conditional illustrative contract, not a legal assertion.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def gmpProtectedSurvivorParallel
    (contractual statutoryMinimum : ℝ) : ℝ :=
  max contractual statutoryMinimum
end ActuarialUnderpinsF


