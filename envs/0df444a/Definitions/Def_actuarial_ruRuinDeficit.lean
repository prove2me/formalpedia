-- Prove2me | Definitions.Def_actuarial_ruRuinDeficit
-- name    : actuarial_ruRuinDeficit
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:30:48.154605+00:00
-- url     : https://prove2.me/theorems/d8b7f171-e888-4440-9048-a5f0a75e4b64
-- title:
--   Ruin events and finite-horizon Lundberg bound: ruRuinDeficit
-- statement:
--   Nonnegative deficit of capital when the insured surplus has fallen below zero, with deficit zero for nonruin.
--
--   Mathematical relation:
--
--   $$
--   max (-surplus) 0
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 18 and 23, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://ocw.mit.edu/courses/18-440-probability-and-random-variables-spring-2014/resources/mit18_440s14_lecture35/. The proposed model is rooted in Promislow chapter 18 and 23. The target Lean identity is an original derivation, not a verbatim published result. Published source page 426 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ActuarialValuation

noncomputable def ruRuinDeficit (surplus : ℝ) : ℝ := max (-surplus) 0

end ActuarialValuation


