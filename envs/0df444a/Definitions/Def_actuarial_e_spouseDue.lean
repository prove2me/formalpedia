-- Prove2me | Definitions.Def_actuarial_e_spouseDue
-- name    : actuarial_e_spouseDue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:08:51.50383+00:00
-- url     : https://prove2.me/theorems/c03d30c3-b4d3-4e1b-bd40-697853329651
-- title:
--   Spouse instalment crystallised at death
-- statement:
--   Spouse instalment crystallised at death. Survivor payments begin strictly after the settlement anniversary and require survival on their own due dates.
--
--   The contractual and mortality relation is:
--
--   $$
--   S(i,j,t)=\mathbf{1}_{\{i<j,\ i+1<t\leq j\}}
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
noncomputable def spouseDue (i j t : ℕ) : ℝ := if i < j ∧ i + 1 < t ∧ t ≤ j then (1 : ℝ) else 0
end ActuarialDeathE


