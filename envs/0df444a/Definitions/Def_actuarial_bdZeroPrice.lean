-- Prove2me | Definitions.Def_actuarial_bdZeroPrice
-- name    : actuarial_bdZeroPrice
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:28:35.508179+00:00
-- url     : https://prove2.me/theorems/5c58a1cb-3750-4a63-8743-1cbe2372fc4e
-- title:
--   Deterministic zero-coupon bonds and forward discounts: bdZeroPrice
-- statement:
--   Value at time zero of a zero-coupon bond paying face currency units at maturity T, where D(T)>0 is the term discount.
--
--   Mathematical relation:
--
--   $$
--   face*D T
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ActuarialValuation

noncomputable def bdZeroPrice (D : ℕ → ℝ) (face : ℝ) (T : ℕ) : ℝ := face*D T

end ActuarialValuation


