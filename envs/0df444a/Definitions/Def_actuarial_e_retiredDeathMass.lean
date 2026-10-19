-- Prove2me | Definitions.Def_actuarial_e_retiredDeathMass
-- name    : actuarial_e_retiredDeathMass
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:56:30.569833+00:00
-- url     : https://prove2.me/theorems/33939154-2e64-4aac-bf31-978cf2b68705
-- title:
--   Probability of death after retirement
-- statement:
--   Probability of death after retirement. The retired-death mass excludes all deaths before the commencement anniversary.
--
--   The contractual and mortality relation is:
--
--   $$
--   \Pr(\text{retired death})=\mathbb{E}_p[I_R(i)]
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
import Definitions.Def_actuarial_e_retired

namespace ActuarialDeathE
noncomputable def retiredDeathMass (h r : ℕ) (p : ℕ → ℕ → ℝ) : ℝ := expect h p (fun i j => retired h r i)
end ActuarialDeathE


