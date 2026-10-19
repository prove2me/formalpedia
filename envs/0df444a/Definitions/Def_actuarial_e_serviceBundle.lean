-- Prove2me | Definitions.Def_actuarial_e_serviceBundle
-- name    : actuarial_e_serviceBundle
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:09:15.115124+00:00
-- url     : https://prove2.me/theorems/d7528642-1ba4-4736-8357-b9826185a919
-- title:
--   Scheme-switched death-in-service benefits
-- statement:
--   Scheme-switched death-in-service benefits. A salary multiple, accrued-service benefit and contribution refund are individually optional, potentially exclusive under scheme rules.
--
--   The contractual and mortality relation is:
--
--   $$
--   L_A(t)=f_s k y_t+f_a A_t+f_c C_t,\quad f_s,f_a,f_c\in\{0,1\}
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
import Definitions.Def_actuarial_e_salaryMultiple

namespace ActuarialDeathE
noncomputable def serviceBundle (k : ℝ) (salary accrued contributions : ℕ → ℝ) (paySalary payAccrued payRefund : Bool) (t : ℕ) : ℝ := (if paySalary then salaryMultiple k salary t else 0) + (if payAccrued then accrued t else 0) + (if payRefund then contributions t else 0)
end ActuarialDeathE


