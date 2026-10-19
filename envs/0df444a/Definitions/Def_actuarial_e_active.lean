-- Prove2me | Definitions.Def_actuarial_e_active
-- name    : actuarial_e_active
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:06:00.130034+00:00
-- url     : https://prove2.me/theorems/ceedbf5c-dd24-4dad-90fe-528b17f428b6
-- title:
--   Death in active employment
-- statement:
--   Death in active employment. Death takes place in (i,i+1] strictly before the employment exit anniversary e.
--
--   The contractual and mortality relation is:
--
--   $$
--   I_A(i)=\mathbf{1}_{\{i<h,\ i<e\}}
--   $$
--
--   The object is defined at its stated payment dates. Amounts are per instalment or in pounds as appropriate; probabilities are dimensionless and discounts are to valuation.
-- source:
--   Originally derived finite-grid pension contract statement, based on the actuarial context in Chapter 9, p. 359, of Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, 3rd ed, Chapters 8–11. https://doi.org/10.1017/9781108784184 Specific benefit switches and endpoint rules are explicit new scheme assumptions, not verbatim textbook results.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive

namespace ActuarialDeathE
noncomputable def active (h e i : ℕ) : ℝ := if i < h ∧ i < e then (1 : ℝ) else 0
end ActuarialDeathE


