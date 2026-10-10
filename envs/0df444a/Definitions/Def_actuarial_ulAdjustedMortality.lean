-- Prove2me | Definitions.Def_actuarial_ulAdjustedMortality
-- name    : actuarial_ulAdjustedMortality
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:30:18.063961+00:00
-- url     : https://prove2.me/theorems/a1c03c2c-36e7-41eb-8d00-48aed034569e
-- title:
--   Monthly account premium expenses and insurance charges: ulAdjustedMortality
-- statement:
--   Mortality charge rate adjusted for different insurance and account interest bases, assuming positive gross discount factors.
--
--   Mathematical relation:
--
--   $$
--   mortality*(1+interest)/(1+insuranceDiscount)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def ulAdjustedMortality (interest insuranceDiscount mortality : ℝ) : ℝ := mortality*(1+interest)/(1+insuranceDiscount)

end ActuarialValuation


