-- Prove2me | Definitions.Def_actuarial_bnAmericanNode
-- name    : actuarial_bnAmericanNode
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:30:46.009264+00:00
-- url     : https://prove2.me/theorems/264c24f7-d73c-41fc-9e05-385f67f48f1b
-- title:
--   Two-period binomial recursion and American option exercise: bnAmericanNode
-- statement:
--   American-option node value is the larger of immediate exercise and risk-neutral continuation.
--
--   Mathematical relation:
--
--   $$
--   max exercise continuation
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def bnAmericanNode (exercise continuation : ℝ) : ℝ := max exercise continuation

end ActuarialValuation


