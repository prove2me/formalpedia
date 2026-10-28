-- Prove2me | Definitions.Def_actuarial_f_gmpProtectedDisplaceableEPV
-- name    : actuarial_f_gmpProtectedDisplaceableEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:49:23.048005+00:00
-- url     : https://prove2.me/theorems/afc9f8e1-dd6c-4098-9d10-85b3f13de96a
-- title:
--   GMP-safe overlap expected value
-- statement:
--   Value only the survivor amount actually displaced and never the statutory GMP minimum.
--
--   The defining expression is:
--
--   $$
--   O=\mathbb E[\sum_t v_tO_t]
--   $$
-- source:
--   Original derived UK DB pension valuation. Statutory context: PSA 1993 sections 17, 87–92 and 109, https://www.legislation.gov.uk/ukpga/1993/48/section/109; Pensions Act 1995 section 53, https://www.legislation.gov.uk/ukpga/1995/26/section/53; HMRC Pensions Tax Manual PTM071500, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm071500. Full statutory anti-franking, allowable offset credits, GMP revaluation modes and exact survivor eligibility remain externally certified inputs. The estate guarantee replacement is a conditional illustrative contract, not a legal assertion.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_expect
import Definitions.Def_actuarial_f_gmpProtectedDisplaceableInstalment

namespace ActuarialUnderpinsF
noncomputable def gmpProtectedDisplaceableEPV
    (n h r g : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (disc a b : ℕ → ℝ) (sa sb : ℕ → ℕ → ℝ)
    (gs : ℕ → ℕ → ℝ)
    (statutorySurvivor : ℕ → ℕ → ℕ → ℕ → ℝ) : ℝ :=
  expect n h p (fun z i j =>
    ∑ t ∈ Finset.range (h+1), disc t *
      gmpProtectedDisplaceableInstalment h r g z i j t
        a b sa sb gs statutorySurvivor)
end ActuarialUnderpinsF


