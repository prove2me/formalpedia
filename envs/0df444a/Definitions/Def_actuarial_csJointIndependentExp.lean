-- Prove2me | Definitions.Def_actuarial_csJointIndependentExp
-- name    : actuarial_csJointIndependentExp
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:30:31.098855+00:00
-- url     : https://prove2.me/theorems/0aea3633-68dd-4202-8ab2-21cdbad46e5e
-- title:
--   Independent-shock Marshall–Olkin survivor law: csJointIndependentExp
-- statement:
--   Product of the two observed marginal survivor factors; an independence benchmark which is generally false when c is positive.
--
--   Mathematical relation:
--
--   $$
--   csMarginalOneExp a c t * csMarginalTwoExp b c t
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 11, 17 and 19, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1080/01621459.1967.10482885. The proposed model is rooted in Promislow chapter 11, 17 and 19. The target Lean identity is an original derivation, not a verbatim published result. Published source page 271 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_csMarginalOneExp
import Definitions.Def_actuarial_csMarginalTwoExp

namespace ActuarialValuation

noncomputable def csJointIndependentExp (a b c t : ℝ) : ℝ := csMarginalOneExp a c t * csMarginalTwoExp b c t

end ActuarialValuation


