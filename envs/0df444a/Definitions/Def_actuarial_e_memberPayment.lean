-- Prove2me | Definitions.Def_actuarial_e_memberPayment
-- name    : actuarial_e_memberPayment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:30:06.707646+00:00
-- url     : https://prove2.me/theorems/338a8570-d73b-4a61-926c-87b6c058cfe5
-- title:
--   In-payment member pension
-- statement:
--   In-payment member pension. The pension starts on anniversary r, with payment on tick t only while the member survives that date.
--
--   The contractual and mortality relation is:
--
--   $$
--   M_t(i)=b_t\mathbf{1}_{\{r\leq t\leq i\}}
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
import Definitions.Def_actuarial_e_alive

namespace ActuarialDeathE
noncomputable def memberPayment (r i t : ℕ) (base : ℕ → ℝ) : ℝ := if r ≤ t then base t * alive i t else 0
end ActuarialDeathE


