-- Prove2me | Definitions.Def_actuarial_e_revaluedDeferred
-- name    : actuarial_e_revaluedDeferred
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:28:03.62273+00:00
-- url     : https://prove2.me/theorems/8ee9b968-8ee6-4e66-ba5f-62884265fc8b
-- title:
--   Revalued preserved rights
-- statement:
--   Revalued preserved rights. The preservation amount is fixed at exit; the valuation-date revaluation factor is supplied separately.
--
--   The contractual and mortality relation is:
--
--   $$
--   P_D(t)=P_{\text{exit}}G_t
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

namespace ActuarialDeathE
noncomputable def revaluedDeferred (atExit : ℝ) (growth : ℕ → ℝ) (t : ℕ) : ℝ := atExit * growth t
end ActuarialDeathE


