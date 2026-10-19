-- Prove2me | Definitions.Def_actuarial_e_retired
-- name    : actuarial_e_retired
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:06:20.59217+00:00
-- url     : https://prove2.me/theorems/79a97631-6998-4a80-a109-b3394e8d374b
-- title:
--   Death after pension commencement
-- statement:
--   Death after pension commencement. The member is already retired when death occurs in year (i,i+1].
--
--   The contractual and mortality relation is:
--
--   $$
--   I_R(i)=\mathbf{1}_{\{i<h,\ r\leq i\}}
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
noncomputable def retired (h r i : ℕ) : ℝ := if i < h ∧ r ≤ i then (1 : ℝ) else 0
end ActuarialDeathE


