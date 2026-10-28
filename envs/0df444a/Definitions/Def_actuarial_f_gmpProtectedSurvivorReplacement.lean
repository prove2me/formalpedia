-- Prove2me | Definitions.Def_actuarial_f_gmpProtectedSurvivorReplacement
-- name    : actuarial_f_gmpProtectedSurvivorReplacement
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:47:28.146422+00:00
-- url     : https://prove2.me/theorems/925827d1-fe8e-4ec0-81cb-5477cf6ae829
-- title:
--   Preserved survivor GMP during optional guarantee replacement
-- statement:
--   When the contract permits estate-guarantee replacement, retain the statutory survivor floor rather than extinguishing it.
--
--   The defining expression is:
--
--   $$
--   R^S_t=\begin{cases}M^S_t&\mathrm{replace}\\\max(C^S_t,M^S_t)&\mathrm{otherwise}\end{cases}
--   $$
-- source:
--   Original derived UK DB pension valuation. Statutory context: PSA 1993 sections 17, 87–92 and 109, https://www.legislation.gov.uk/ukpga/1993/48/section/109; Pensions Act 1995 section 53, https://www.legislation.gov.uk/ukpga/1995/26/section/53; HMRC Pensions Tax Manual PTM071500, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm071500. Full statutory anti-franking, allowable offset credits, GMP revaluation modes and exact survivor eligibility remain externally certified inputs. The estate guarantee replacement is a conditional illustrative contract, not a legal assertion.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpProtectedSurvivorParallel

namespace ActuarialUnderpinsF
noncomputable def gmpProtectedSurvivorReplacement
    (replace : Prop) (contractual statutoryMinimum : ℝ) : ℝ := by
  classical
  exact if replace then statutoryMinimum else
    gmpProtectedSurvivorParallel contractual statutoryMinimum
end ActuarialUnderpinsF


