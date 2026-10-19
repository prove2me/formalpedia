-- Prove2me | Definitions.Def_actuarial_e_qualifiedOverlapEPV
-- name    : actuarial_e_qualifiedOverlapEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:59:33.976727+00:00
-- url     : https://prove2.me/theorems/ee013d22-2577-4a57-9adc-85770ec4806d
-- title:
--   Marriage-weighted guarantee-suppression EPV
-- statement:
--   Marriage-weighted guarantee-suppression EPV. The suppressed spouse instalments carry the same death-crystallised qualification probability as the contract.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_O(q)=\sum_t v_t\sum_{i,j}p_{ij}q_iO_t(i,j)
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
import Definitions.Def_actuarial_e_expect
import Definitions.Def_actuarial_e_overlapPayment

namespace ActuarialDeathE
noncomputable def qualifiedOverlapEPV (h n r g : ℕ) (p : ℕ → ℕ → ℝ) (q disc c increase : ℕ → ℝ) : ℝ := ∑ t ∈ Finset.range n, disc t * expect h p (fun i j => q i * overlapPayment h r g i j t c increase)
end ActuarialDeathE


