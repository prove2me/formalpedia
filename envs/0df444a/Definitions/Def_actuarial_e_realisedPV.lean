-- Prove2me | Definitions.Def_actuarial_e_realisedPV
-- name    : actuarial_e_realisedPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:32:42.539774+00:00
-- url     : https://prove2.me/theorems/ce9227e2-d0eb-4cd3-9f54-892724ba13ad
-- title:
--   Realised contract present value
-- statement:
--   Realised contract present value. All lump sums and annual instalments are valued from their actual conditional death states.
--
--   The contractual and mortality relation is:
--
--   $$
--   Z(i,j;\eta)=v_{i+1}L(i)+\sum_{t=0}^{n-1}v_tC_t(i,j;\eta)
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
import Definitions.Def_actuarial_e_deathPV
import Definitions.Def_actuarial_e_instalment

namespace ActuarialDeathE
noncomputable def realisedPV (h n e r g i j : ℕ) (disc service defer retire base a b c increase : ℕ → ℝ) (replace : Bool) : ℝ := deathPV h e r i disc service defer retire + ∑ t ∈ Finset.range n, disc t * instalment h e r g i j t base a b c increase replace
end ActuarialDeathE


