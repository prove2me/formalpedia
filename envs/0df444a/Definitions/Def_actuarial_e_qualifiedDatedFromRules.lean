-- Prove2me | Definitions.Def_actuarial_e_qualifiedDatedFromRules
-- name    : actuarial_e_qualifiedDatedFromRules
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T17:29:20.197389+00:00
-- url     : https://prove2.me/theorems/9aac4aa5-3055-4b04-b86f-193ee0870032
-- title:
--   Payment-date valuation of the salary and preserved-rights contract
-- statement:
--   Payment-date valuation of the salary and preserved-rights contract. The alternative construction uses the identical scheme-specific benefit basis and frozen dependent qualification.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_{\text{dated}}^{\text{rules}}(q,\eta)=V_{\text{dated}}\bigl(q,\eta;L_A=L_{\text{salary/service/refund}},L_D=P_{\text{exit}}G\mathcal{A}+\text{refund}\bigr)
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
import Definitions.Def_actuarial_e_qualifiedCashflowEPV

namespace ActuarialDeathE
noncomputable def qualifiedDatedFromRules (h n e r g : ℕ) (p : ℕ → ℕ → ℝ) (q : ℕ → ℝ) (k atExit : ℝ) (salary accrued contributions growth capitalFactor refunds retire base a b c increase disc : ℕ → ℝ) (paySalary payAccrued serviceRefund deferRefund replace : Bool) : ℝ := qualifiedCashflowEPV h n e r g p q disc (fun t => serviceBundle k salary accrued contributions paySalary payAccrued serviceRefund t) (fun t => deferredBundle atExit growth capitalFactor refunds deferRefund t) retire base a b c increase replace
end ActuarialDeathE


