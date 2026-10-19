-- Prove2me | Definitions.Def_actuarial_e_guaranteeCapitalAtDeath
-- name    : actuarial_e_guaranteeCapitalAtDeath
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T17:42:44.692031+00:00
-- url     : https://prove2.me/theorems/cd69c595-e4e3-4feb-98c4-af37b87a7070
-- title:
--   Cash equivalent of remaining guaranteed instalments on settlement
-- statement:
--   Cash equivalent of remaining guaranteed instalments on settlement. An explicitly supplied forward discount factor converts dated estate payments to a GBP capital amount at the member's death-settlement anniversary.
--
--   The contractual and mortality relation is:
--
--   $$
--   K_{i+1}=\sum_t f_{i+1,t}G_t
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
noncomputable def guaranteeCapitalAtDeath (n h r g i : ℕ) (forward : ℕ → ℕ → ℝ) (base : ℕ → ℝ) : ℝ := ∑ t ∈ Finset.range n, forward (i + 1) t * guaranteePayment h r g i t base
end ActuarialDeathE


