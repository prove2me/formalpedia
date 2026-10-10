-- Prove2me | Definitions.Def_actuarial_bdAnnualForward
-- name    : actuarial_bdAnnualForward
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:29:50.375212+00:00
-- url     : https://prove2.me/theorems/44c8e5f6-9b87-43df-9c44-5ff1d83a9746
-- title:
--   Deterministic zero-coupon bonds and forward discounts: bdAnnualForward
-- statement:
--   Effective forward interest rate for the single-year interval from anniversary t to t+1.
--
--   Mathematical relation:
--
--   $$
--   bdSimpleForward D t (t+1)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdSimpleForward

namespace ActuarialValuation

noncomputable def bdAnnualForward (D : ℕ → ℝ) (t : ℕ) : ℝ := bdSimpleForward D t (t+1)

end ActuarialValuation


