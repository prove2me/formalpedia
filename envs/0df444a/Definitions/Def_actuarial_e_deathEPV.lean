-- Prove2me | Definitions.Def_actuarial_e_deathEPV
-- name    : actuarial_e_deathEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:33:17.936975+00:00
-- url     : https://prove2.me/theorems/91bd58c5-01d7-47ce-9eb2-a9d1fd7f0759
-- title:
--   Disjoint death-event lump-sum EPV
-- statement:
--   Disjoint death-event lump-sum EPV. Death lumps are averaged on their genuine active, deferred and retired death events.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_L=\sum_{i,j}p_{ij}v_{i+1}L(i)
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
import Definitions.Def_actuarial_e_deathPV

namespace ActuarialDeathE
noncomputable def deathEPV (h e r : ℕ) (p : ℕ → ℕ → ℝ) (disc service defer retire : ℕ → ℝ) : ℝ := expect h p (fun i j => deathPV h e r i disc service defer retire)
end ActuarialDeathE


