-- Prove2me | Definitions.Def_actuarial_e_qualifiedCashflowEPV
-- name    : actuarial_e_qualifiedCashflowEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T14:51:06.61274+00:00
-- url     : https://prove2.me/theorems/6819d14f-8172-4ac2-9e04-b956a132dd04
-- title:
--   Payment-date contract with spouse-at-death probability
-- statement:
--   Payment-date contract with spouse-at-death probability. Four disjoint-beneficiary cashflow families use q i only on survivor instalments.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_{\text{dated}}(q,\eta)=V_L+V_M+V_R(q,\eta)+V_G
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
import Definitions.Def_actuarial_e_guaranteeEPV
import Definitions.Def_actuarial_e_qualifiedSpouseEPV

namespace ActuarialDeathE
noncomputable def qualifiedCashflowEPV (h n e r g : ℕ) (p : ℕ → ℕ → ℝ) (q disc service defer retire base a b c increase : ℕ → ℝ) (replace : Bool) : ℝ := deathEPV h e r p disc service defer retire + memberEPV h n r p disc base + qualifiedSpouseEPV h n e r g p q disc a b c increase replace + guaranteeEPV h n r g p disc base
end ActuarialDeathE


