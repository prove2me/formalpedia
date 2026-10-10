-- Prove2me | Definitions.Def_actuarial_ulAllocatedPremium
-- name    : actuarial_ulAllocatedPremium
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:28:36.390596+00:00
-- url     : https://prove2.me/theorems/2b14451c-1a3b-4c2e-b3f5-9df81b69ef2c
-- title:
--   Monthly account premium expenses and insurance charges: ulAllocatedPremium
-- statement:
--   Premium allocation after proportional expenses at the beginning of each policy period.
--
--   Mathematical relation:
--
--   $$
--   prem*(1-expenseRate)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def ulAllocatedPremium (prem expenseRate : ℝ) : ℝ := prem*(1-expenseRate)

end ActuarialValuation


