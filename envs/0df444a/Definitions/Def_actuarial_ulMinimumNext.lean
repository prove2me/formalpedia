-- Prove2me | Definitions.Def_actuarial_ulMinimumNext
-- name    : actuarial_ulMinimumNext
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:30:01.542015+00:00
-- url     : https://prove2.me/theorems/7be2f45b-136f-40b2-b1bd-05e25bfe57fa
-- title:
--   Type A and B mortality strain and explicit guarantee: ulMinimumNext
-- statement:
--   Piecewise survivor account after an end-period maximum-of-account-and-guaranteed-floor death benefit, under mortality less than one and correct coverage region.
--
--   Mathematical relation:
--
--   $$
--   if earned ≤ floor then (earned-mortality*floor)/(1-mortality) else earned
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def ulMinimumNext (earned mortality floor : ℝ) : ℝ := if earned ≤ floor then (earned-mortality*floor)/(1-mortality) else earned

end ActuarialValuation


