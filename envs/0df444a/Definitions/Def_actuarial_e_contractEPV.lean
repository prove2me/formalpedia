-- Prove2me | Definitions.Def_actuarial_e_contractEPV
-- name    : actuarial_e_contractEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:33:01.90464+00:00
-- url     : https://prove2.me/theorems/9d5556f3-3b65-460a-8dd3-936ac89d578b
-- title:
--   Event-conditioned pension contract EPV
-- statement:
--   Event-conditioned pension contract EPV. Joint member and spouse mortality are integrated after the realised pension contract is priced.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_{\text{event}}(\eta)=\sum_{i,j}p_{ij}Z(i,j;\eta)
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
import Definitions.Def_actuarial_e_realisedPV

namespace ActuarialDeathE
noncomputable def contractEPV (h n e r g : ℕ) (p : ℕ → ℕ → ℝ) (disc service defer retire base a b c increase : ℕ → ℝ) (replace : Bool) : ℝ := expect h p (fun i j => realisedPV h n e r g i j disc service defer retire base a b c increase replace)
end ActuarialDeathE


