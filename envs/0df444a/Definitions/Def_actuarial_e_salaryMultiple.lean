-- Prove2me | Definitions.Def_actuarial_e_salaryMultiple
-- name    : actuarial_e_salaryMultiple
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:09:02.433168+00:00
-- url     : https://prove2.me/theorems/50de93c1-6527-4a60-bd23-29fadafbe127
-- title:
--   Salary-multiple death lump sum
-- statement:
--   Salary-multiple death lump sum. Salary is measured at the explicitly specified death settlement anniversary; the multiplier is a scheme input.
--
--   The contractual and mortality relation is:
--
--   $$
--   L_{\text{salary}}(t)=k\,y_t
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

namespace ActuarialDeathE
noncomputable def salaryMultiple (k : ℝ) (salary : ℕ → ℝ) (t : ℕ) : ℝ := k * salary t
end ActuarialDeathE


