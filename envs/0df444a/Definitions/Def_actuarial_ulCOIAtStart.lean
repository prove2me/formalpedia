-- Prove2me | Definitions.Def_actuarial_ulCOIAtStart
-- name    : actuarial_ulCOIAtStart
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:30:08.933155+00:00
-- url     : https://prove2.me/theorems/870cb73a-db2f-4e85-92e7-6628bf1bfdf9
-- title:
--   Monthly account premium expenses and insurance charges: ulCOIAtStart
-- statement:
--   Beginning-period monetary cost of insurance when claims and account strain are paid at the end of the period; nonzero gross credited interest required.
--
--   Mathematical relation:
--
--   $$
--   mortality*risk/(1+interest)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def ulCOIAtStart (interest mortality risk : ℝ) : ℝ := mortality*risk/(1+interest)

end ActuarialValuation


