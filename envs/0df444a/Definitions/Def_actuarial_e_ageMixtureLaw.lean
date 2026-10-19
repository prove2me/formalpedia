-- Prove2me | Definitions.Def_actuarial_e_ageMixtureLaw
-- name    : actuarial_e_ageMixtureLaw
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T17:32:12.269776+00:00
-- url     : https://prove2.me/theorems/25530358-2833-4909-ac80-7b1488116815
-- title:
--   Age-difference mixture of joint member and dependent mortality
-- statement:
--   Age-difference mixture of joint member and dependent mortality. Each scenario contributes its own member/dependent death-year law and is weighted once by its age-difference probability.
--
--   The contractual and mortality relation is:
--
--   $$
--   p_{ij}^{\text{mix}}=\sum_{k=0}^{a-1}w_kp^{(k)}_{ij}
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
noncomputable def ageMixtureLaw (h a : ℕ) (w : ℕ → ℝ) (laws : ℕ → ℕ → ℕ → ℝ) (i j : ℕ) : ℝ := ∑ k ∈ Finset.range a, w k * laws k i j
end ActuarialDeathE


