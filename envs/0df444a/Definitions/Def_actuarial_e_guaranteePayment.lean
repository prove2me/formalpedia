-- Prove2me | Definitions.Def_actuarial_e_guaranteePayment
-- name    : actuarial_e_guaranteePayment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:31:24.079644+00:00
-- url     : https://prove2.me/theorems/099f4fc6-eff6-4b55-be0a-a51f016d96d9
-- title:
--   Remaining guaranteed instalment
-- statement:
--   Remaining guaranteed instalment. After a pensioner's death, unpaid guaranteed instalments continue until, but excluding, tick r+g.
--
--   The contractual and mortality relation is:
--
--   $$
--   G_t(i)=b_t\mathbf{1}_{\{r\leq i<h,\ i<t<r+g\}}
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

namespace ActuarialDeathE
noncomputable def guaranteePayment (h r g i t : ℕ) (base : ℕ → ℝ) : ℝ := if r ≤ i ∧ i < h ∧ i < t ∧ r ≤ t ∧ t < r + g then base t else 0
end ActuarialDeathE


