-- Prove2me | Definitions.Def_actuarial_f_gmpProtectedDisplaceableInstalment
-- name    : actuarial_f_gmpProtectedDisplaceableInstalment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:48:20.856994+00:00
-- url     : https://prove2.me/theorems/93d580d4-32d6-49bc-9097-0f016c96436e
-- title:
--   Permissible contractual survivor overlap only
-- statement:
--   Return only the non-statutory survivor surplus when a scheme-permitted estate replacement overlaps it.
--
--   The defining expression is:
--
--   $$
--   O_t=\mathbf1_{\mathrm{replace}}\max(0,C^S_t-M^S_t)
--   $$
-- source:
--   Original derived UK DB pension valuation. Statutory context: PSA 1993 sections 17, 87–92 and 109, https://www.legislation.gov.uk/ukpga/1993/48/section/109; Pensions Act 1995 section 53, https://www.legislation.gov.uk/ukpga/1995/26/section/53; HMRC Pensions Tax Manual PTM071500, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm071500. Full statutory anti-franking, allowable offset credits, GMP revaluation modes and exact survivor eligibility remain externally certified inputs. The estate guarantee replacement is a conditional illustrative contract, not a legal assertion.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_estateDue
import Definitions.Def_actuarial_f_gmpProtectedContractualSurvivor
import Definitions.Def_actuarial_f_gmpProtectedSurvivorDisplaceable

namespace ActuarialUnderpinsF
noncomputable def gmpProtectedDisplaceableInstalment
    (h r g z i j t : ℕ) (a b : ℕ → ℝ)
    (sa sb : ℕ → ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (statutorySurvivor : ℕ → ℕ → ℕ → ℕ → ℝ) : ℝ :=
  gmpProtectedSurvivorDisplaceable (estateDue h r g i t = 1)
    (gmpProtectedContractualSurvivor h z i j t a b sa sb gs)
    (statutorySurvivor z i j t)
end ActuarialUnderpinsF


