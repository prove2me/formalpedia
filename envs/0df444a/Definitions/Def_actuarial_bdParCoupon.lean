-- Prove2me | Definitions.Def_actuarial_bdParCoupon
-- name    : actuarial_bdParCoupon
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:30:54.802919+00:00
-- url     : https://prove2.me/theorems/2ce9c8d8-10f3-4177-94ef-6e2315aed8a8
-- title:
--   Coupon-bond cashflows duration and flat yield: bdParCoupon
-- statement:
--   Annual-in-arrears coupon per unit nominal of a par bond with maturity n, using zero-coupon price D(n) and positive coupon-annuity denominator.
--
--   Mathematical relation:
--
--   $$
--   (1-D n)/(∑ k ∈ Finset.range n, D (k+1))
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ActuarialValuation

noncomputable def bdParCoupon (D : ℕ → ℝ) (n : ℕ) : ℝ := (1-D n)/(∑ k ∈ Finset.range n, D (k+1))

end ActuarialValuation


