-- Prove2me | Definitions.Def_actuarial_ulEarned
-- name    : actuarial_ulEarned
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:29:06.17046+00:00
-- url     : https://prove2.me/theorems/140668ee-b110-4c44-bbab-99ea2e47d01a
-- title:
--   Monthly account premium expenses and insurance charges: ulEarned
-- statement:
--   Period-end account earnings before insurance deduction, with credited interest applied to the post-premium and post-expense account.
--
--   Mathematical relation:
--
--   $$
--   ulAfterPremium account prem expenseRate fixedExpense * (1+interest)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulAfterPremium

namespace ActuarialValuation

noncomputable def ulEarned (account prem expenseRate fixedExpense interest : ℝ) : ℝ := ulAfterPremium account prem expenseRate fixedExpense * (1+interest)

end ActuarialValuation


