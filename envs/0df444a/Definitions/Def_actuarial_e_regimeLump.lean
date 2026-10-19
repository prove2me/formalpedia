-- Prove2me | Definitions.Def_actuarial_e_regimeLump
-- name    : actuarial_e_regimeLump
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:29:35.970682+00:00
-- url     : https://prove2.me/theorems/cff8240b-d8b5-4bee-95d4-497a26f451f3
-- title:
--   Disjoint death-event lump sum
-- statement:
--   Disjoint death-event lump sum. Exactly one of the three benefit bases is selected for each eligible member death.
--
--   The contractual and mortality relation is:
--
--   $$
--   L(i)=I_A(i)L_A(i+1)+I_D(i)L_D(i+1)+I_R(i)L_R(i+1)
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
import Definitions.Def_actuarial_e_active
import Definitions.Def_actuarial_e_deferred
import Definitions.Def_actuarial_e_retired

namespace ActuarialDeathE
noncomputable def regimeLump (h e r i : ℕ) (service defer retire : ℕ → ℝ) : ℝ := active h e i * service (i + 1) + deferred h e r i * defer (i + 1) + retired h r i * retire (i + 1)
end ActuarialDeathE


