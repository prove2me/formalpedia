-- Prove2me | Definitions.Def_actuarial_csMarginalOneExp
-- name    : actuarial_csMarginalOneExp
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:29:48.796175+00:00
-- url     : https://prove2.me/theorems/f792daa4-839d-46fb-9827-7dedaa6e227c
-- title:
--   Independent-shock Marshall–Olkin survivor law: csMarginalOneExp
-- statement:
--   First observed life exponential survival with total first-life intensity a+c.
--
--   Mathematical relation:
--
--   $$
--   Real.exp (-(a+c)*t)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 11, 17 and 19, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1080/01621459.1967.10482885. The proposed model is rooted in Promislow chapter 11, 17 and 19. The target Lean identity is an original derivation, not a verbatim published result. Published source page 271 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace ActuarialValuation

noncomputable def csMarginalOneExp (a c t : ℝ) : ℝ := Real.exp (-(a+c)*t)

end ActuarialValuation


