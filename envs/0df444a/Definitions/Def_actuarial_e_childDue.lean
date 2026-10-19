-- Prove2me | Definitions.Def_actuarial_e_childDue
-- name    : actuarial_e_childDue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T17:41:51.18538+00:00
-- url     : https://prove2.me/theorems/33ee50ff-af88-4f07-b624-2d27d83bb41f
-- title:
--   Age-limited dependent child instalment indicator
-- statement:
--   Age-limited dependent child instalment indicator. A child must qualify alive at the member's death, survive the due tick and remain younger than the contractual cessation age.
--
--   The contractual and mortality relation is:
--
--   $$
--   C_{\text{child}}(i,j,t)=S(i,j,t)\mathbf{1}_{\{a_0+t<a_{\max}\}}
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
import Definitions.Def_actuarial_e_spouseDue

namespace ActuarialDeathE
noncomputable def childDue (i j t childAge maximumAge : ℕ) : ℝ := if childAge + t < maximumAge then spouseDue i j t else 0
end ActuarialDeathE


