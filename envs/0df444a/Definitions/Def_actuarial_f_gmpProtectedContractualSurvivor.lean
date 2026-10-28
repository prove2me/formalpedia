-- Prove2me | Definitions.Def_actuarial_f_gmpProtectedContractualSurvivor
-- name    : actuarial_f_gmpProtectedContractualSurvivor
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:47:11.129987+00:00
-- url     : https://prove2.me/theorems/13770343-67ce-4743-9b48-6b44d8b28666
-- title:
--   Elected option contractual survivor instalment
-- statement:
--   The survivor's contractual basis follows the option elected at award and remains contingent on survival.
--
--   The defining expression is:
--
--   $$
--   C^S_t=S^{\mathrm{elected}}_{zi}G^S_{i,t}\mathbf1_{\mathrm{due}}
--   $$
-- source:
--   Original derived UK DB pension valuation. Statutory context: PSA 1993 sections 17, 87–92 and 109, https://www.legislation.gov.uk/ukpga/1993/48/section/109; Pensions Act 1995 section 53, https://www.legislation.gov.uk/ukpga/1995/26/section/53; HMRC Pensions Tax Manual PTM071500, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm071500. Full statutory anti-franking, allowable offset credits, GMP revaluation modes and exact survivor eligibility remain externally certified inputs. The estate guarantee replacement is a conditional illustrative contract, not a legal assertion.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseInstalment
import Definitions.Def_actuarial_f_linkedSpouseBasis

namespace ActuarialUnderpinsF
noncomputable def gmpProtectedContractualSurvivor
    (h z i j t : ℕ)
    (a b : ℕ → ℝ) (sa sb : ℕ → ℕ → ℝ)
    (gs : ℕ → ℕ → ℝ) : ℝ :=
  spouseInstalment h z i j t (linkedSpouseBasis a b sa sb) gs
end ActuarialUnderpinsF


