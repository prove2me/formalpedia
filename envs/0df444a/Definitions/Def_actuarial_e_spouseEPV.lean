-- Prove2me | Definitions.Def_actuarial_e_spouseEPV
-- name    : actuarial_e_spouseEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:33:45.251677+00:00
-- url     : https://prove2.me/theorems/46c2e627-c709-45ca-9fcb-d5e62281c838
-- title:
--   Survivor-pension instalment EPV
-- statement:
--   Survivor-pension instalment EPV. Period-first value with qualifying-dependent entitlement determined by death and survivor occupancy at payment.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_R(\eta)=\sum_t v_t\sum_{i,j}p_{ij}R_t(i,j;\eta)
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
import Definitions.Def_actuarial_e_spousePayment

namespace ActuarialDeathE
noncomputable def spouseEPV (h n e r g : ℕ) (p : ℕ → ℕ → ℝ) (disc a b c increase : ℕ → ℝ) (replace : Bool) : ℝ := ∑ t ∈ Finset.range n, disc t * expect h p (fun i j => spousePayment h e r g i j t a b c increase replace)
end ActuarialDeathE


