-- Prove2me | Definitions.Def_actuarial_ruFiniteRuinBound
-- name    : actuarial_ruFiniteRuinBound
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:31:11.638546+00:00
-- url     : https://prove2.me/theorems/b0c6438c-707a-4c9a-9e8d-5038abcc0661
-- title:
--   Ruin events and finite-horizon Lundberg bound: ruFiniteRuinBound
-- statement:
--   Exponential upper bound on ruin probability under a positive adjustment coefficient and appropriate exponential-supermartingale conditions.
--
--   Mathematical relation:
--
--   $$
--   Real.exp (-R*initial)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 18 and 23, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://ocw.mit.edu/courses/18-440-probability-and-random-variables-spring-2014/resources/mit18_440s14_lecture35/. The proposed model is rooted in Promislow chapter 18 and 23. The target Lean identity is an original derivation, not a verbatim published result. Published source page 426 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ActuarialValuation

noncomputable def ruFiniteRuinBound (R initial : ℝ) : ℝ := Real.exp (-R*initial)

end ActuarialValuation


