-- Prove2me | Definitions.Def_actuarial_e_qualifiedCommutableContractEPV
-- name    : actuarial_e_qualifiedCommutableContractEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T17:43:40.153472+00:00
-- url     : https://prove2.me/theorems/f99f6863-61c5-4471-9331-b4a1c5667c57
-- title:
--   Complete qualified pension contract with mutually exclusive estate guarantee alternative
-- statement:
--   Complete qualified pension contract with mutually exclusive estate guarantee alternative. The same death-status benefit model offers one selected estate payment mechanism while member and qualifying spouse cashflows retain their original due dates.
--
--   The contractual and mortality relation is:
--
--   $$
--   V^{\kappa}_{\text{total}}=\mathbb{E}[V_{\text{death}}+V_{\text{member}}+V_{\text{spouse}}+G_{\text{option}}(\kappa)]
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
import Definitions.Def_actuarial_e_deathPV
import Definitions.Def_actuarial_e_memberPayment
import Definitions.Def_actuarial_e_spousePayment
import Definitions.Def_actuarial_e_guaranteeOptionPV

namespace ActuarialDeathE
noncomputable def qualifiedCommutableContractEPV (h n e r g : ℕ) (p : ℕ → ℕ → ℝ) (q disc service defer retire base a b c increase : ℕ → ℝ) (forward : ℕ → ℕ → ℝ) (commute replace : Bool) : ℝ := expect h p (fun i j => deathPV h e r i disc service defer retire + guaranteeOptionPV n h r g i disc forward base commute + ∑ t ∈ Finset.range n, disc t * (memberPayment r i t base + q i * spousePayment h e r g i j t a b c increase replace))
end ActuarialDeathE


