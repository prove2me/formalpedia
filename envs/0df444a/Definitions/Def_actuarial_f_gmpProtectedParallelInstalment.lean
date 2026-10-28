-- Prove2me | Definitions.Def_actuarial_f_gmpProtectedParallelInstalment
-- name    : actuarial_f_gmpProtectedParallelInstalment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:47:47.102601+00:00
-- url     : https://prove2.me/theorems/e3c23c8a-d95d-4f06-a8d9-b22fd0ba2c15
-- title:
--   GMP-protected parallel payment
-- statement:
--   Add member, estate and protected survivor payments without counting any GMP component twice.
--
--   The defining expression is:
--
--   $$
--   P_t=P^M_t+P^E_t+\max(C^S_t,M^S_t)
--   $$
-- source:
--   Original derived UK DB pension valuation. Statutory context: PSA 1993 sections 17, 87–92 and 109, https://www.legislation.gov.uk/ukpga/1993/48/section/109; Pensions Act 1995 section 53, https://www.legislation.gov.uk/ukpga/1995/26/section/53; HMRC Pensions Tax Manual PTM071500, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm071500. Full statutory anti-franking, allowable offset credits, GMP revaluation modes and exact survivor eligibility remain externally certified inputs. The estate guarantee replacement is a conditional illustrative contract, not a legal assertion.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_memberDue
import Definitions.Def_actuarial_f_estateInstalment
import Definitions.Def_actuarial_f_linkedFirstTranche
import Definitions.Def_actuarial_f_gmpProtectedContractualSurvivor
import Definitions.Def_actuarial_f_gmpProtectedSurvivorParallel

namespace ActuarialUnderpinsF
noncomputable def gmpProtectedParallelInstalment
    (h r g z i j t : ℕ) (a b c : ℕ → ℝ)
    (sa sb : ℕ → ℕ → ℝ) (estate ga gb gc : ℕ → ℝ)
    (gs : ℕ → ℕ → ℝ) (ge : ℕ → ℝ)
    (memberSupplement : ℕ → ℕ → ℕ → ℝ)
    (statutorySurvivor : ℕ → ℕ → ℕ → ℕ → ℝ) : ℝ :=
  linkedFirstTranche r z i t a b ga gb +
  c z * gc t * memberDue r i t +
  memberSupplement z i t +
  estateInstalment h r g z i t estate ge +
  gmpProtectedSurvivorParallel
    (gmpProtectedContractualSurvivor h z i j t a b sa sb gs)
    (statutorySurvivor z i j t)
end ActuarialUnderpinsF


