-- Prove2me | Definitions.Def_actuarial_e_guaranteeCapitalPV
-- name    : actuarial_e_guaranteeCapitalPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T17:43:01.324009+00:00
-- url     : https://prove2.me/theorems/3d54942d-d389-4d08-8fd2-0d24327caba8
-- title:
--   Present value of the commuted estate guarantee
-- statement:
--   Present value of the commuted estate guarantee. The commuted capital is paid once at member-death settlement and discounted back to valuation time.
--
--   The contractual and mortality relation is:
--
--   $$
--   G_{\text{capital}}=v_{i+1}K_{i+1}
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
import Definitions.Def_actuarial_e_guaranteeCapitalAtDeath

namespace ActuarialDeathE
noncomputable def guaranteeCapitalPV (n h r g i : ℕ) (disc : ℕ → ℝ) (forward : ℕ → ℕ → ℝ) (base : ℕ → ℝ) : ℝ := disc (i + 1) * guaranteeCapitalAtDeath n h r g i forward base
end ActuarialDeathE


