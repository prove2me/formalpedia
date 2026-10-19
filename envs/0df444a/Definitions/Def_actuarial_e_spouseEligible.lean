-- Prove2me | Definitions.Def_actuarial_e_spouseEligible
-- name    : actuarial_e_spouseEligible
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:06:37.353113+00:00
-- url     : https://prove2.me/theorems/71471f18-a48b-4a63-af16-530759dc4cf7
-- title:
--   Qualifying dependent alive at death
-- statement:
--   Qualifying dependent alive at death. The entitlement indicator is fixed at the member's death; a same-tick death is ineligible.
--
--   The contractual and mortality relation is:
--
--   $$
--   Q(i,j)=\mathbf{1}_{\{i<j\}}
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
noncomputable def spouseEligible (i j : ℕ) : ℝ := if i < j then (1 : ℝ) else 0
end ActuarialDeathE


