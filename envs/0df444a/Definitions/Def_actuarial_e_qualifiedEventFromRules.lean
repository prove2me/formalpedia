-- Prove2me | Definitions.Def_actuarial_e_qualifiedEventFromRules
-- name    : actuarial_e_qualifiedEventFromRules
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T14:51:25.167506+00:00
-- url     : https://prove2.me/theorems/87ef53a4-c889-442c-bf68-84149a10820e
-- title:
--   Complete contract from salary and preserved-rights death rules
-- statement:
--   Complete contract from salary and preserved-rights death rules. The active death benefit derives from the explicit salary or contribution rule, with deferred rights independently revalued.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_{\text{event}}^{\text{rules}}(q,\eta)=V_{\text{event}}\bigl(q,\eta;L_A=L_{\text{salary/service/refund}},L_D=P_{\text{exit}}G\mathcal{A}+\text{refund}\bigr)
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
import Definitions.Def_actuarial_e_serviceBundle
import Definitions.Def_actuarial_e_deferredBundle
import Definitions.Def_actuarial_e_qualifiedContractEPV

namespace ActuarialDeathE
noncomputable def qualifiedEventFromRules (h n e r g : ℕ) (p : ℕ → ℕ → ℝ) (q : ℕ → ℝ) (k atExit : ℝ) (salary accrued contributions growth capitalFactor refunds retire base a b c increase disc : ℕ → ℝ) (paySalary payAccrued serviceRefund deferRefund replace : Bool) : ℝ := qualifiedContractEPV h n e r g p q disc (fun t => serviceBundle k salary accrued contributions paySalary payAccrued serviceRefund t) (fun t => deferredBundle atExit growth capitalFactor refunds deferRefund t) retire base a b c increase replace
end ActuarialDeathE


