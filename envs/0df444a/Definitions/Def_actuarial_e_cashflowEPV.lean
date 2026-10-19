-- Prove2me | Definitions.Def_actuarial_e_cashflowEPV
-- name    : actuarial_e_cashflowEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:34:35.234593+00:00
-- url     : https://prove2.me/theorems/5160e807-d6af-4306-a0b1-6c04997c4dd1
-- title:
--   Payment-date construction of the contract EPV
-- statement:
--   Payment-date construction of the contract EPV. Four economically different cashflow families are each valued on their due dates.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_{\text{dated}}(\eta)=V_L+V_M+V_R(\eta)+V_G
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
import Definitions.Def_actuarial_e_deathEPV
import Definitions.Def_actuarial_e_memberEPV
import Definitions.Def_actuarial_e_spouseEPV
import Definitions.Def_actuarial_e_guaranteeEPV

namespace ActuarialDeathE
noncomputable def cashflowEPV (h n e r g : ℕ) (p : ℕ → ℕ → ℝ) (disc service defer retire base a b c increase : ℕ → ℝ) (replace : Bool) : ℝ := deathEPV h e r p disc service defer retire + memberEPV h n r p disc base + spouseEPV h n e r g p disc a b c increase replace + guaranteeEPV h n r g p disc base
end ActuarialDeathE


