-- Prove2me | Definitions.Def_actuarial_e_childDatedEPV
-- name    : actuarial_e_childDatedEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T17:42:20.230151+00:00
-- url     : https://prove2.me/theorems/c2dc9589-4b75-4568-a553-f40214986036
-- title:
--   Age-limited child income valued by instalment date
-- statement:
--   Age-limited child income valued by instalment date. The member-death and child-survival conditions are each tested at their respective contractual events.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_{\text{child,date}}=\sum_tv_t\mathbb{E}_p[C_{\text{child}}(i,j,t)b_{i+1}u_t]
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
import Definitions.Def_actuarial_e_childDue

namespace ActuarialDeathE
noncomputable def childDatedEPV (h n childAge maximumAge : ℕ) (p : ℕ → ℕ → ℝ) (disc basis increase : ℕ → ℝ) : ℝ := ∑ t ∈ Finset.range n, disc t * expect h p (fun i j => childDue i j t childAge maximumAge * basis (i + 1) * increase t)
end ActuarialDeathE


