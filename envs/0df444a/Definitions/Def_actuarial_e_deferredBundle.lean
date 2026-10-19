-- Prove2me | Definitions.Def_actuarial_e_deferredBundle
-- name    : actuarial_e_deferredBundle
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:28:27.095524+00:00
-- url     : https://prove2.me/theorems/0643e63d-40b8-455a-b762-48db2ecd9055
-- title:
--   Death-in-deferment capitalised pension or refund
-- statement:
--   Death-in-deferment capitalised pension or refund. A revalued preserved annual pension multiplied by an explicitly supplied pension-to-capital factor in years, plus any separately permitted refund.
--
--   The contractual and mortality relation is:
--
--   $$
--   L_D(t)=P_{\text{exit}}G_t\mathcal{A}_t+f_c C_t
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
import Definitions.Def_actuarial_e_revaluedDeferred

namespace ActuarialDeathE
noncomputable def deferredBundle (atExit : ℝ) (growth capitalFactor refunds : ℕ → ℝ) (payRefund : Bool) (t : ℕ) : ℝ := revaluedDeferred atExit growth t * capitalFactor t + (if payRefund then refunds t else 0)
end ActuarialDeathE


