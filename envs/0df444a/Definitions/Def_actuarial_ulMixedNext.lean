-- Prove2me | Definitions.Def_actuarial_ulMixedNext
-- name    : actuarial_ulMixedNext
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:30:26.777694+00:00
-- url     : https://prove2.me/theorems/9dcb09d8-df79-4255-b8d4-972300d27973
-- title:
--   Monthly account premium expenses and insurance charges: ulMixedNext
-- statement:
--   Period-end reserve with insurance charge valued on its own discount basis and deducted before account credited interest.
--
--   Mathematical relation:
--
--   $$
--   (earned/(1+interest) - mortality*risk/(1+insuranceDiscount))*(1+interest)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def ulMixedNext (earned interest insuranceDiscount mortality risk : ℝ) : ℝ := (earned/(1+interest) - mortality*risk/(1+insuranceDiscount))*(1+interest)

end ActuarialValuation


