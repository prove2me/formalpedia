-- Prove2me | Definitions.Def_actuarial_ulTypeANext
-- name    : actuarial_ulTypeANext
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:29:34.985977+00:00
-- url     : https://prove2.me/theorems/83ed0e48-5e85-4e22-a302-bbaa898d09e2
-- title:
--   Type A and B mortality strain and explicit guarantee: ulTypeANext
-- statement:
--   Type A fixed-total-death-benefit end-period account solved from net amount at risk face less survivor account, requiring mortality below unity and positive strain region.
--
--   Mathematical relation:
--
--   $$
--   (ulEarned account prem expenseRate fixedExpense interest - mortality*face)/(1-mortality)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulEarned

namespace ActuarialValuation

noncomputable def ulTypeANext (account prem expenseRate fixedExpense interest mortality face : ℝ) : ℝ := (ulEarned account prem expenseRate fixedExpense interest - mortality*face)/(1-mortality)

end ActuarialValuation


