-- Prove2me | Definitions.Def_actuarial_e_deferred
-- name    : actuarial_e_deferred
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:06:10.866163+00:00
-- url     : https://prove2.me/theorems/1e975a67-a5cb-4207-b21b-f716c5143f9a
-- title:
--   Death while holding deferred rights
-- statement:
--   Death while holding deferred rights. Exit has occurred but pension commencement anniversary r has not.
--
--   The contractual and mortality relation is:
--
--   $$
--   I_D(i)=\mathbf{1}_{\{i<h,\ e\leq i<r\}}
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
noncomputable def deferred (h e r i : ℕ) : ℝ := if i < h ∧ e ≤ i ∧ i < r then (1 : ℝ) else 0
end ActuarialDeathE


