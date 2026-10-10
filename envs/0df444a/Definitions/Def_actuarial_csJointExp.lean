-- Prove2me | Definitions.Def_actuarial_csJointExp
-- name    : actuarial_csJointExp
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:29:40.568264+00:00
-- url     : https://prove2.me/theorems/f31c2ff6-bcbb-4006-8873-461996e92a57
-- title:
--   Independent-shock Marshall–Olkin survivor law: csJointExp
-- statement:
--   Marshall–Olkin joint survivor law with primitive exponential rates a, b, c and common-shock threshold max(s,t).
--
--   Mathematical relation:
--
--   $$
--   Real.exp (-(a*s+b*t+c*max s t))
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

noncomputable def csJointExp (a b c s t : ℝ) : ℝ := Real.exp (-(a*s+b*t+c*max s t))

end ActuarialValuation


