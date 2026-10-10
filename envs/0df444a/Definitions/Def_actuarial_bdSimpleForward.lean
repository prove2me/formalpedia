-- Prove2me | Definitions.Def_actuarial_bdSimpleForward
-- name    : actuarial_bdSimpleForward
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:29:32.869664+00:00
-- url     : https://prove2.me/theorems/16506388-c4a4-4a63-851e-48edd17f17fc
-- title:
--   Deterministic zero-coupon bonds and forward discounts: bdSimpleForward
-- statement:
--   Effective gross-to-net simple forward rate over the full time interval from s to t; no annualisation for intervals longer than one year.
--
--   Mathematical relation:
--
--   $$
--   bdForwardGross D s t - 1
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdForwardGross

namespace ActuarialValuation

noncomputable def bdSimpleForward (D : ℕ → ℝ) (s t : ℕ) : ℝ := bdForwardGross D s t - 1

end ActuarialValuation


