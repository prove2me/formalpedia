-- Prove2me | Definitions.Def_actuarial_e_deathPV
-- name    : actuarial_e_deathPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:29:51.437609+00:00
-- url     : https://prove2.me/theorems/365b86a0-8b2a-48af-b3b7-5f68840d0949
-- title:
--   Discounted death-settlement value
-- statement:
--   Discounted death-settlement value. All death lumps here are paid at the end-of-death-year anniversary i+1.
--
--   The contractual and mortality relation is:
--
--   $$
--   Z_L(i)=v_{i+1}L(i)
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
import Definitions.Def_actuarial_e_regimeLump

namespace ActuarialDeathE
noncomputable def deathPV (h e r i : ℕ) (disc service defer retire : ℕ → ℝ) : ℝ := disc (i + 1) * regimeLump h e r i service defer retire
end ActuarialDeathE


