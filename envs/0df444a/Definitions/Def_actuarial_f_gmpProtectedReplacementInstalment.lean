-- Prove2me | Definitions.Def_actuarial_f_gmpProtectedReplacementInstalment
-- name    : actuarial_f_gmpProtectedReplacementInstalment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:48:03.928384+00:00
-- url     : https://prove2.me/theorems/84934410-b030-4576-99dd-3b943fe44407
-- title:
--   GMP-safe survivor and estate guarantee replacement
-- statement:
--   Retain the statutory survivor floor in a replacement design alongside the selected member benefit and estate stream.
--
--   The defining expression is:
--
--   $$
--   R_t=P^M_t+P^E_t+R^S_t
--   $$
-- source:
--   Original derived UK DB pension valuation. Statutory context: PSA 1993 sections 17, 87–92 and 109, https://www.legislation.gov.uk/ukpga/1993/48/section/109; Pensions Act 1995 section 53, https://www.legislation.gov.uk/ukpga/1995/26/section/53; HMRC Pensions Tax Manual PTM071500, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm071500. Full statutory anti-franking, allowable offset credits, GMP revaluation modes and exact survivor eligibility remain externally certified inputs. The estate guarantee replacement is a conditional illustrative contract, not a legal assertion.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_memberDue
import Definitions.Def_actuarial_f_estateDue
import Definitions.Def_actuarial_f_estateInstalment
import Definitions.Def_actuarial_f_linkedFirstTranche
import Definitions.Def_actuarial_f_gmpProtectedContractualSurvivor
import Definitions.Def_actuarial_f_gmpProtectedSurvivorReplacement

namespace ActuarialUnderpinsF
noncomputable def gmpProtectedReplacementInstalment
    (h r g z i j t : ℕ) (a b c : ℕ → ℝ)
    (sa sb : ℕ → ℕ → ℝ) (estate ga gb gc : ℕ → ℝ)
    (gs : ℕ → ℕ → ℝ) (ge : ℕ → ℝ)
    (memberSupplement : ℕ → ℕ → ℕ → ℝ)
    (statutorySurvivor : ℕ → ℕ → ℕ → ℕ → ℝ) : ℝ :=
  linkedFirstTranche r z i t a b ga gb +
  c z * gc t * memberDue r i t +
  memberSupplement z i t +
  estateInstalment h r g z i t estate ge +
  gmpProtectedSurvivorReplacement (estateDue h r g i t = 1)
    (gmpProtectedContractualSurvivor h z i j t a b sa sb gs)
    (statutorySurvivor z i j t)
end ActuarialUnderpinsF


