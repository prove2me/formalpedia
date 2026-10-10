-- Prove2me | Definitions.Def_actuarial_bdForwardBond
-- name    : actuarial_bdForwardBond
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:29:15.710988+00:00
-- url     : https://prove2.me/theorems/e31a4735-b28b-4b72-8ff0-663ec4034df9
-- title:
--   Deterministic zero-coupon bonds and forward discounts: bdForwardBond
-- statement:
--   Contractual forward price at time s for the certain maturity-t zero-coupon redemption amount face, for a deterministic discount basis.
--
--   Mathematical relation:
--
--   $$
--   face * bdForwardDiscount D s t
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdForwardDiscount

namespace ActuarialValuation

noncomputable def bdForwardBond (D : ℕ → ℝ) (face : ℝ) (s t : ℕ) : ℝ := face * bdForwardDiscount D s t

end ActuarialValuation


