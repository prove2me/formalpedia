-- Prove2me | Definitions.Def_actuarial_e_ageMixtureOverlapEPV
-- name    : actuarial_e_ageMixtureOverlapEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T17:41:39.475627+00:00
-- url     : https://prove2.me/theorems/8233b407-d58b-4316-ab87-2317ec40558c
-- title:
--   Guarantee-overlap EPV mixed over dependent-age scenarios
-- statement:
--   Guarantee-overlap EPV mixed over dependent-age scenarios. The estate guarantee is valued separately from the death-fixed qualifying spouse pension in each age-difference scenario.
--
--   The contractual and mortality relation is:
--
--   $$
--   O^{\text{mix}}=\sum_kw_kO^{(k)}
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
import Definitions.Def_actuarial_e_qualifiedOverlapEPV

namespace ActuarialDeathE
noncomputable def ageMixtureOverlapEPV (h a n r g : ℕ) (w : ℕ → ℝ) (laws : ℕ → ℕ → ℕ → ℝ) (qualify : ℕ → ℕ → ℝ) (disc retiredBasis increase : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range a, w k * qualifiedOverlapEPV h n r g (laws k) (qualify k) disc retiredBasis increase
end ActuarialDeathE


