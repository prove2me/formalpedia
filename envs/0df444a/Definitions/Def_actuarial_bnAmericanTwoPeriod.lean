-- Prove2me | Definitions.Def_actuarial_bnAmericanTwoPeriod
-- name    : actuarial_bnAmericanTwoPeriod
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:31:01.622953+00:00
-- url     : https://prove2.me/theorems/b23d0b7c-4b07-40df-a7e9-3fc1b9a793d4
-- title:
--   Two-period binomial recursion and American option exercise: bnAmericanTwoPeriod
-- statement:
--   Two-period American-value recursion with explicit immediate exercise at each node and an eligible terminal payoff schedule.
--
--   Mathematical relation:
--
--   $$
--   bnAmericanNode exercise (bnOnePeriodPrice R q (bnAmericanNode upExercise (bnOnePeriodPrice R q uu ud)) (bnAmericanNode downExercise (bnOnePeriodPrice R q du dd)))
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnAmericanNode
import Definitions.Def_actuarial_bnOnePeriodPrice

namespace ActuarialValuation

noncomputable def bnAmericanTwoPeriod (R q exercise upExercise downExercise uu ud du dd : ℝ) : ℝ := bnAmericanNode exercise (bnOnePeriodPrice R q (bnAmericanNode upExercise (bnOnePeriodPrice R q uu ud)) (bnAmericanNode downExercise (bnOnePeriodPrice R q du dd)))

end ActuarialValuation


