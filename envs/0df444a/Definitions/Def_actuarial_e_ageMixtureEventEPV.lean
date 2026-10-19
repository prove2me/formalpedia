-- Prove2me | Definitions.Def_actuarial_e_ageMixtureEventEPV
-- name    : actuarial_e_ageMixtureEventEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T17:33:35.315984+00:00
-- url     : https://prove2.me/theorems/ac3303e2-7262-4444-91c4-ac8f870f8bee
-- title:
--   Event-first pension EPV over spouse age-difference scenarios
-- statement:
--   Event-first pension EPV over spouse age-difference scenarios. The marriage-at-death probability and conditional joint law are scenario-specific; the time-of-payment survival test is not repeated.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_{\text{event}}^{\text{mix}}=\sum_kw_kV_{\text{event}}^{(k)}
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
import Definitions.Def_actuarial_e_qualifiedContractEPV

namespace ActuarialDeathE
noncomputable def ageMixtureEventEPV (h a n e r g : ℕ) (w : ℕ → ℝ) (laws : ℕ → ℕ → ℕ → ℝ) (qualify : ℕ → ℕ → ℝ) (disc service defer retire base activeBasis deferredBasis retiredBasis increase : ℕ → ℝ) (replace : Bool) : ℝ := ∑ k ∈ Finset.range a, w k * qualifiedContractEPV h n e r g (laws k) (qualify k) disc service defer retire base activeBasis deferredBasis retiredBasis increase replace
end ActuarialDeathE


