-- Prove2me | Definitions.Def_actuarial_e_guaranteeEPV
-- name    : actuarial_e_guaranteeEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:33:57.244068+00:00
-- url     : https://prove2.me/theorems/8f30371f-a4a0-4d94-9bc1-77e4f99052e0
-- title:
--   Guaranteed-instalment EPV
-- statement:
--   Guaranteed-instalment EPV. All estate-guarantee instalments after member death are priced independently of the spouse's survival.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_G=\sum_t v_t\sum_{i,j}p_{ij}G_t(i)
--   $$
--
--   The object is defined at its stated payment dates. Amounts are per instalment or in pounds as appropriate; probabilities are dimensionless and discounts are to valuation.
-- source:
--   Originally derived finite-grid pension contract statement, based on the actuarial context in Chapter 11, p. 423, of Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, 3rd ed, Chapters 8–11. https://doi.org/10.1017/9781108784184 Specific benefit switches and endpoint rules are explicit new scheme assumptions, not verbatim textbook results.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_expect
import Definitions.Def_actuarial_e_guaranteePayment

namespace ActuarialDeathE
noncomputable def guaranteeEPV (h n r g : ℕ) (p : ℕ → ℕ → ℝ) (disc base : ℕ → ℝ) : ℝ := ∑ t ∈ Finset.range n, disc t * expect h p (fun i j => guaranteePayment h r g i t base)
end ActuarialDeathE


