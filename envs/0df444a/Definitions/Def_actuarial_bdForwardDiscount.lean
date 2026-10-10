-- Prove2me | Definitions.Def_actuarial_bdForwardDiscount
-- name    : actuarial_bdForwardDiscount
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:28:43.308985+00:00
-- url     : https://prove2.me/theorems/f3632c4c-d7d7-4b31-8719-220c6c7eb17e
-- title:
--   Deterministic zero-coupon bonds and forward discounts: bdForwardDiscount
-- statement:
--   Deterministic discount factor from forward settlement s to maturity t derived from time-zero zero-coupon prices, with nonzero D(s).
--
--   Mathematical relation:
--
--   $$
--   D t / D s
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ActuarialValuation

noncomputable def bdForwardDiscount (D : ℕ → ℝ) (s t : ℕ) : ℝ := D t / D s

end ActuarialValuation


