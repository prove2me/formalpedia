-- Prove2me | Definitions.Def_actuarial_e_activeDeathMass
-- name    : actuarial_e_activeDeathMass
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:37:40.411521+00:00
-- url     : https://prove2.me/theorems/5c8b3bfe-322b-4468-b145-df93b0f6b56b
-- title:
--   Probability of death while actively employed
-- statement:
--   Probability of death while actively employed. The death-in-service probability is summed from member-death cells of a single joint law.
--
--   The contractual and mortality relation is:
--
--   $$
--   \Pr(\text{active death})=\mathbb{E}_p[I_A(i)]
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
import Definitions.Def_actuarial_e_expect
import Definitions.Def_actuarial_e_active

namespace ActuarialDeathE
noncomputable def activeDeathMass (h e : ℕ) (p : ℕ → ℕ → ℝ) : ℝ := expect h p (fun i j => active h e i)
end ActuarialDeathE


