-- Prove2me | Definitions.Def_actuarial_e_guaranteeStreamPV
-- name    : actuarial_e_guaranteeStreamPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T17:42:34.330785+00:00
-- url     : https://prove2.me/theorems/f825e200-e19d-406d-b2d0-8cf47f362711
-- title:
--   Present value of remaining estate-guaranteed instalments
-- statement:
--   Present value of remaining estate-guaranteed instalments. Each unpaid guaranteed instalment is discounted at its own actual due anniversary.
--
--   The contractual and mortality relation is:
--
--   $$
--   G_{\text{stream}}=\sum_t v_tG_t
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
import Definitions.Def_actuarial_e_guaranteePayment

namespace ActuarialDeathE
noncomputable def guaranteeStreamPV (n h r g i : ℕ) (disc base : ℕ → ℝ) : ℝ := ∑ t ∈ Finset.range n, disc t * guaranteePayment h r g i t base
end ActuarialDeathE


