-- Prove2me | Definitions.Def_actuarial_f_gmpProtectedStateEPV
-- name    : actuarial_f_gmpProtectedStateEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:48:52.551246+00:00
-- url     : https://prove2.me/theorems/ef5c88d5-7b34-4c78-bd30-1a341d8521f1
-- title:
--   GMP-safe state-summed expected value
-- statement:
--   Sum the same protected cashflows by date and state, retaining all state dependence.
--
--   The defining expression is:
--
--   $$
--   V_S=\sum_t v_t\mathbb E[P_t]
--   $$
-- source:
--   Original derived UK DB pension valuation. Statutory context: PSA 1993 sections 17, 87–92 and 109, https://www.legislation.gov.uk/ukpga/1993/48/section/109; Pensions Act 1995 section 53, https://www.legislation.gov.uk/ukpga/1995/26/section/53; HMRC Pensions Tax Manual PTM071500, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm071500. Full statutory anti-franking, allowable offset credits, GMP revaluation modes and exact survivor eligibility remain externally certified inputs. The estate guarantee replacement is a conditional illustrative contract, not a legal assertion.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_expect
import Definitions.Def_actuarial_f_gmpProtectedParallelInstalment

namespace ActuarialUnderpinsF
noncomputable def gmpProtectedStateEPV
    (n h r g : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (disc a b c : ℕ → ℝ) (sa sb : ℕ → ℕ → ℝ)
    (estate ga gb gc : ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (ge : ℕ → ℝ)
    (memberSupplement : ℕ → ℕ → ℕ → ℝ)
    (statutorySurvivor : ℕ → ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ t ∈ Finset.range (h+1), disc t *
    expect n h p (fun z i j =>
      gmpProtectedParallelInstalment h r g z i j t a b c sa sb
        estate ga gb gc gs ge memberSupplement statutorySurvivor)
end ActuarialUnderpinsF


