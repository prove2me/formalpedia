-- Prove2me | Definitions.Def_actuarial_e_overlapEPV
-- name    : actuarial_e_overlapEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:34:14.95898+00:00
-- url     : https://prove2.me/theorems/8bf0b569-4f7e-4908-ba4c-448a28b6212e
-- title:
--   Suppressed survivor-guarantee overlap EPV
-- statement:
--   Suppressed survivor-guarantee overlap EPV. Quantifies the payment reduction caused solely by replacing, rather than adding, the spouse pension inside a guarantee.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_O=\sum_t v_t\sum_{i,j}p_{ij}O_t(i,j)
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
import Definitions.Def_actuarial_e_expect
import Definitions.Def_actuarial_e_overlapPayment

namespace ActuarialDeathE
noncomputable def overlapEPV (h n r g : ℕ) (p : ℕ → ℕ → ℝ) (disc retiredBasis increase : ℕ → ℝ) : ℝ := ∑ t ∈ Finset.range n, disc t * expect h p (fun i j => overlapPayment h r g i j t retiredBasis increase)
end ActuarialDeathE


