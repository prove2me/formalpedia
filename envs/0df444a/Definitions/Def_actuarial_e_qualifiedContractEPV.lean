-- Prove2me | Definitions.Def_actuarial_e_qualifiedContractEPV
-- name    : actuarial_e_qualifiedContractEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:59:59.435699+00:00
-- url     : https://prove2.me/theorems/d7350011-cd04-4fc5-a104-3cc4804e5df3
-- title:
--   Event-conditioned contract with spouse-at-death probability
-- statement:
--   Event-conditioned contract with spouse-at-death probability. The joint mortality outcome is valued before the payment-date interchange, with q i applied exactly once.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_{\text{event}}(q,\eta)=\sum_{i,j}p_{ij}\left[v_{i+1}L(i)+\sum_t v_t(M_t+q_iR_t(\eta)+G_t)\right]
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
import Definitions.Def_actuarial_e_guaranteePayment
import Definitions.Def_actuarial_e_spousePayment

namespace ActuarialDeathE
noncomputable def qualifiedContractEPV (h n e r g : ℕ) (p : ℕ → ℕ → ℝ) (q disc service defer retire base a b c increase : ℕ → ℝ) (replace : Bool) : ℝ := expect h p (fun i j => deathPV h e r i disc service defer retire + ∑ t ∈ Finset.range n, disc t * (memberPayment r i t base + q i * spousePayment h e r g i j t a b c increase replace + guaranteePayment h r g i t base))
end ActuarialDeathE


