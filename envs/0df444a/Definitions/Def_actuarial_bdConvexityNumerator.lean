-- Prove2me | Definitions.Def_actuarial_bdConvexityNumerator
-- name    : actuarial_bdConvexityNumerator
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:30:47.582591+00:00
-- url     : https://prove2.me/theorems/cff4c913-a21e-4fd3-be64-f8dae1eefece
-- title:
--   Coupon-bond cashflows duration and flat yield: bdConvexityNumerator
-- statement:
--   Second time moment numerator, a basic building block for convexity and second-order interest-rate sensitivity.
--
--   Mathematical relation:
--
--   $$
--   ∑ k ∈ Finset.range n, (((k:ℝ)+1)^2) * c k * D (k+1)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ActuarialValuation

noncomputable def bdConvexityNumerator (D c : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, (((k:ℝ)+1)^2) * c k * D (k+1)

end ActuarialValuation


