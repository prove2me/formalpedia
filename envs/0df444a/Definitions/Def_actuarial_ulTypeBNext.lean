-- Prove2me | Definitions.Def_actuarial_ulTypeBNext
-- name    : actuarial_ulTypeBNext
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:29:19.332734+00:00
-- url     : https://prove2.me/theorems/2a9cce9c-39fa-460e-b4d8-0960337c3516
-- title:
--   Type A and B mortality strain and explicit guarantee: ulTypeBNext
-- statement:
--   Period-end Type B additive face death benefit policy account with cost of insurance mortality times full face amount deducted at period end.
--
--   Mathematical relation:
--
--   $$
--   ulEarned account prem expenseRate fixedExpense interest - mortality*face
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulEarned

namespace ActuarialValuation

noncomputable def ulTypeBNext (account prem expenseRate fixedExpense interest mortality face : ℝ) : ℝ := ulEarned account prem expenseRate fixedExpense interest - mortality*face

end ActuarialValuation


