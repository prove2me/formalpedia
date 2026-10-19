-- Prove2me | Definitions.Def_actuarial_e_memberEPV
-- name    : actuarial_e_memberEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:33:32.025641+00:00
-- url     : https://prove2.me/theorems/6473e36e-48a6-42a5-8497-2f5cf896ad64
-- title:
--   Member pension occupation EPV
-- statement:
--   Member pension occupation EPV. Period-first construction of the original retirement pension, retaining survival at each actual tick.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_M=\sum_t v_t\sum_{i,j}p_{ij}M_t(i)
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
import Definitions.Def_actuarial_e_memberPayment

namespace ActuarialDeathE
noncomputable def memberEPV (h n r : ℕ) (p : ℕ → ℕ → ℝ) (disc base : ℕ → ℝ) : ℝ := ∑ t ∈ Finset.range n, disc t * expect h p (fun i j => memberPayment r i t base)
end ActuarialDeathE


