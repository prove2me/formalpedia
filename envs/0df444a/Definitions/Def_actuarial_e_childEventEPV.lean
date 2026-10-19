-- Prove2me | Definitions.Def_actuarial_e_childEventEPV
-- name    : actuarial_e_childEventEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T17:42:06.078839+00:00
-- url     : https://prove2.me/theorems/d70b386c-e358-4332-9573-761c0d79c50c
-- title:
--   Age-limited child income valued first by death outcome
-- statement:
--   Age-limited child income valued first by death outcome. Child pensions are contingent on the child's age and survival at each due tick, with the member-death benefit basis fixed once.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_{\text{child,event}}=\mathbb{E}_p\left[\sum_tv_tC_{\text{child}}(i,j,t)b_{i+1}u_t\right]
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
noncomputable def childEventEPV (h n childAge maximumAge : ℕ) (p : ℕ → ℕ → ℝ) (disc basis increase : ℕ → ℝ) : ℝ := expect h p (fun i j => ∑ t ∈ Finset.range n, disc t * childDue i j t childAge maximumAge * basis (i + 1) * increase t)
end ActuarialDeathE


