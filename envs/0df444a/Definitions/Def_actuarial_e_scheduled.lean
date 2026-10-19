-- Prove2me | Definitions.Def_actuarial_e_scheduled
-- name    : actuarial_e_scheduled
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:35:58.025985+00:00
-- url     : https://prove2.me/theorems/11bae430-8466-48b6-8356-0eb617e82a4c
-- title:
--   Payment-frequency selector
-- statement:
--   Payment-frequency selector. For a positive tick spacing m, payments are due at its multiples; use a monthly unit of time for monthly contracts.
--
--   The contractual and mortality relation is:
--
--   $$
--   H_m(t)=\mathbf{1}_{\{0<m,\ t\bmod m=0\}}
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

namespace ActuarialDeathE
noncomputable def scheduled (m t : ℕ) : ℝ := if 0 < m ∧ t % m = 0 then (1 : ℝ) else 0
end ActuarialDeathE


