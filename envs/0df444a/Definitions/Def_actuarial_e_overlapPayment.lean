-- Prove2me | Definitions.Def_actuarial_e_overlapPayment
-- name    : actuarial_e_overlapPayment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:32:08.099605+00:00
-- url     : https://prove2.me/theorems/eecba984-c1ce-463c-9775-2d931663e86e
-- title:
--   Spouse instalment suppressed by replacement
-- statement:
--   Spouse instalment suppressed by replacement. This is the surviving spouse instalment removed while a retiree's guarantee continues.
--
--   The contractual and mortality relation is:
--
--   $$
--   O_t(i,j)=I_R(i)S(i,j,t)u_tc_{i+1}\mathbf{1}_{\{t<r+g\}}
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
import Definitions.Def_actuarial_e_retired
import Definitions.Def_actuarial_e_spouseDue

namespace ActuarialDeathE
noncomputable def overlapPayment (h r g i j t : ℕ) (retiredBasis increase : ℕ → ℝ) : ℝ := retired h r i * spouseDue i j t * retiredBasis (i + 1) * increase t * (if t < r + g then (1 : ℝ) else 0)
end ActuarialDeathE


