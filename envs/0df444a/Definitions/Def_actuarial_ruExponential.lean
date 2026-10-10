-- Prove2me | Definitions.Def_actuarial_ruExponential
-- name    : actuarial_ruExponential
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:29:33.656114+00:00
-- url     : https://prove2.me/theorems/b4cabb0a-1308-4cde-a89a-21c86aa3c623
-- title:
--   Actuarial surplus and exponential supermartingale: ruExponential
-- statement:
--   Positive exponential adjustment-coefficient transform of realised capital; rate R has reciprocal monetary units.
--
--   Mathematical relation:
--
--   $$
--   Real.exp (-R*capital)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 18 and 23, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://ocw.mit.edu/courses/18-440-probability-and-random-variables-spring-2014/resources/mit18_440s14_lecture35/. The proposed model is rooted in Promislow chapter 18 and 23. The target Lean identity is an original derivation, not a verbatim published result. Published source page 426 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ActuarialValuation

noncomputable def ruExponential (R capital : ℝ) : ℝ := Real.exp (-R*capital)

end ActuarialValuation


