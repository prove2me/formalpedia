-- Prove2me | Definitions.Def_actuarial_e_ageMixtureDatedEPV
-- name    : actuarial_e_ageMixtureDatedEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T17:36:33.347973+00:00
-- url     : https://prove2.me/theorems/6c104f96-0329-4b18-9955-e56657560743
-- title:
--   Payment-first pension EPV over age-difference scenarios
-- statement:
--   Payment-first pension EPV over age-difference scenarios. Each scenario is first decomposed into death, member, dependent and guarantee streams, then mixed by the original age-difference law.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_{\text{dated}}^{\text{mix}}=\sum_kw_kV_{\text{dated}}^{(k)}
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
import Definitions.Def_actuarial_e_qualifiedCashflowEPV

namespace ActuarialDeathE
noncomputable def ageMixtureDatedEPV (h a n e r g : ℕ) (w : ℕ → ℝ) (laws : ℕ → ℕ → ℕ → ℝ) (qualify : ℕ → ℕ → ℝ) (disc service defer retire base activeBasis deferredBasis retiredBasis increase : ℕ → ℝ) (replace : Bool) : ℝ := ∑ k ∈ Finset.range a, w k * qualifiedCashflowEPV h n e r g (laws k) (qualify k) disc service defer retire base activeBasis deferredBasis retiredBasis increase replace
end ActuarialDeathE


