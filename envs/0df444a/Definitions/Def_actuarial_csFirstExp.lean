-- Prove2me | Definitions.Def_actuarial_csFirstExp
-- name    : actuarial_csFirstExp
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:30:14.045302+00:00
-- url     : https://prove2.me/theorems/3161524f-4642-4df7-9d49-8442651c893c
-- title:
--   Independent-shock Marshall–Olkin survivor law: csFirstExp
-- statement:
--   First of either life or the common shock has exponential survivor factor with total primitive rate a+b+c.
--
--   Mathematical relation:
--
--   $$
--   Real.exp (-(a+b+c)*t)
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

noncomputable def csFirstExp (a b c t : ℝ) : ℝ := Real.exp (-(a+b+c)*t)

end ActuarialValuation


