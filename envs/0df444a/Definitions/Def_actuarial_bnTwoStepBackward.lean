-- Prove2me | Definitions.Def_actuarial_bnTwoStepBackward
-- name    : actuarial_bnTwoStepBackward
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:30:36.935392+00:00
-- url     : https://prove2.me/theorems/037629b3-69af-400a-81f1-e95568cb0c63
-- title:
--   Two-period binomial recursion and American option exercise: bnTwoStepBackward
-- statement:
--   Backward induction across a recombining or path-dependent two-period binomial tree.
--
--   Mathematical relation:
--
--   $$
--   bnOnePeriodPrice R q (bnOnePeriodPrice R q uu ud) (bnOnePeriodPrice R q du dd)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnOnePeriodPrice

namespace ActuarialValuation

noncomputable def bnTwoStepBackward (R q uu ud du dd : ℝ) : ℝ := bnOnePeriodPrice R q (bnOnePeriodPrice R q uu ud) (bnOnePeriodPrice R q du dd)

end ActuarialValuation


