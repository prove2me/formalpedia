-- Prove2me | Definitions.Def_actuarial_bdFlatDiscount
-- name    : actuarial_bdFlatDiscount
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:29:59.150049+00:00
-- url     : https://prove2.me/theorems/4727d56a-09d2-4c1e-9525-ca7ab717e550
-- title:
--   Deterministic zero-coupon bonds and forward discounts: bdFlatDiscount
-- statement:
--   Flat yield curve discount at integer maturity t under positive gross annual return R.
--
--   Mathematical relation:
--
--   $$
--   1/(R^t)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ActuarialValuation

noncomputable def bdFlatDiscount (R : ℝ) (t : ℕ) : ℝ := 1/(R^t)

end ActuarialValuation


