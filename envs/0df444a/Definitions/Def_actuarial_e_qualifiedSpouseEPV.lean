-- Prove2me | Definitions.Def_actuarial_e_qualifiedSpouseEPV
-- name    : actuarial_e_qualifiedSpouseEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:59:07.521133+00:00
-- url     : https://prove2.me/theorems/b27cea80-efed-42b7-958f-20e364c4c3db
-- title:
--   Survivor pension with eligibility probability fixed at death
-- statement:
--   Survivor pension with eligibility probability fixed at death. Conditional probability of a qualifying spouse is q i, fixed by member death year i and independent of later rechecking.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_R(q,\eta)=\sum_t v_t\sum_{i,j}p_{ij}q_iR_t(i,j;\eta)
--   $$
--
--   The object is defined at its stated payment dates. Amounts are per instalment or in pounds as appropriate; probabilities are dimensionless and discounts are to valuation.
-- source:
--   Originally derived finite-grid pension contract statement, based on the actuarial context in Chapter 10, p. 388, of Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, 3rd ed, Chapters 8–11. https://doi.org/10.1017/9781108784184 Specific benefit switches and endpoint rules are explicit new scheme assumptions, not verbatim textbook results.

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
noncomputable def qualifiedSpouseEPV (h n e r g : ℕ) (p : ℕ → ℕ → ℝ) (q disc a b c increase : ℕ → ℝ) (replace : Bool) : ℝ := ∑ t ∈ Finset.range n, disc t * expect h p (fun i j => q i * spousePayment h e r g i j t a b c increase replace)
end ActuarialDeathE


