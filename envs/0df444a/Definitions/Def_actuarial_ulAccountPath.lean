-- Prove2me | Definitions.Def_actuarial_ulAccountPath
-- name    : actuarial_ulAccountPath
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:31:43.628209+00:00
-- url     : https://prove2.me/theorems/b969ead6-83f5-4957-98c0-79cd34de8cc3
-- title:
--   Path-dependent account evolution and stochastic guarantee pricing: ulAccountPath
-- statement:
--   Recursive finite-period Type B account path through successive premium, expense, credited-interest and insurance-charge dates.
--
--   Mathematical relation:
--
--   $$
--   Nat.rec initial (fun k value => ulTypeBNext value (prem k) (expenseRate k) (fixedExpense k) (interest k) (mortality k) (face k)) n
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulTypeBNext

namespace ActuarialValuation

noncomputable def ulAccountPath (initial : ℝ) (prem expenseRate fixedExpense interest mortality face : ℕ → ℝ) (n : ℕ) : ℝ := Nat.rec initial (fun k value => ulTypeBNext value (prem k) (expenseRate k) (fixedExpense k) (interest k) (mortality k) (face k)) n

end ActuarialValuation


