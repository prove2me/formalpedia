-- Prove2me | Definitions.Def_actuarial_ulAfterPremium
-- name    : actuarial_ulAfterPremium
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:28:52.341037+00:00
-- url     : https://prove2.me/theorems/3fe832ba-da0d-4dde-a55a-93b93a493e0b
-- title:
--   Monthly account premium expenses and insurance charges: ulAfterPremium
-- statement:
--   Beginning-of-period account after net premium and fixed expense charge, before any credited interest or mortality cost.
--
--   Mathematical relation:
--
--   $$
--   account + ulAllocatedPremium prem expenseRate - fixedExpense
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulAllocatedPremium

namespace ActuarialValuation

noncomputable def ulAfterPremium (account prem expenseRate fixedExpense : ℝ) : ℝ := account + ulAllocatedPremium prem expenseRate - fixedExpense

end ActuarialValuation


