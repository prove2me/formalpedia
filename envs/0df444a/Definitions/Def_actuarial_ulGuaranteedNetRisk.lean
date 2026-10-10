-- Prove2me | Definitions.Def_actuarial_ulGuaranteedNetRisk
-- name    : actuarial_ulGuaranteedNetRisk
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:29:53.164987+00:00
-- url     : https://prove2.me/theorems/362f451d-2ca7-4bfa-8239-c8e35e4acd14
-- title:
--   Type A and B mortality strain and explicit guarantee: ulGuaranteedNetRisk
-- statement:
--   Mortality or option guarantee's positive shortfall below a guaranteed death amount.
--
--   Mathematical relation:
--
--   $$
--   max (floor-account) 0
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def ulGuaranteedNetRisk (account floor : ℝ) : ℝ := max (floor-account) 0

end ActuarialValuation


