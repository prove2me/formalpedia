-- Prove2me | Definitions.Def_actuarial_bdMacaulayDuration
-- name    : actuarial_bdMacaulayDuration
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:30:36.603989+00:00
-- url     : https://prove2.me/theorems/af32d76a-9570-48f6-8e56-7f91a6f3842a
-- title:
--   Coupon-bond cashflows duration and flat yield: bdMacaulayDuration
-- statement:
--   Cashflow-weighted Macaulay duration in years, meaningful for positive total bond price.
--
--   Mathematical relation:
--
--   $$
--   bdDurationNumerator D c n / bdCouponPV D c n
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdDurationNumerator
import Definitions.Def_actuarial_bdCouponPV

namespace ActuarialValuation

noncomputable def bdMacaulayDuration (D c : ℕ → ℝ) (n : ℕ) : ℝ := bdDurationNumerator D c n / bdCouponPV D c n

end ActuarialValuation


