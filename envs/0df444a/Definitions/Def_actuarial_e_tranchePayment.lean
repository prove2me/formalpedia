-- Prove2me | Definitions.Def_actuarial_e_tranchePayment
-- name    : actuarial_e_tranchePayment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:37:29.147375+00:00
-- url     : https://prove2.me/theorems/141db71a-91c3-4805-8734-a5f68b0f3740
-- title:
--   Distinctly indexed two-tranche instalment
-- statement:
--   Distinctly indexed two-tranche instalment. Each tranche retains its own member and survivor increase basis before cashflows are added.
--
--   The contractual and mortality relation is:
--
--   $$
--   C^{(1,2)}_t=C^{(1)}_t+C^{(2)}_t
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
import Definitions.Def_actuarial_e_instalment

namespace ActuarialDeathE
noncomputable def tranchePayment (h e r g i j t : ℕ) (base1 base2 a1 a2 b1 b2 c1 c2 inc1 inc2 : ℕ → ℝ) (replace : Bool) : ℝ := instalment h e r g i j t base1 a1 b1 c1 inc1 replace + instalment h e r g i j t base2 a2 b2 c2 inc2 replace
end ActuarialDeathE


