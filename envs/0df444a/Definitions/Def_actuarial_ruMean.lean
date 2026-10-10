-- Prove2me | Definitions.Def_actuarial_ruMean
-- name    : actuarial_ruMean
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:28:29.535848+00:00
-- url     : https://prove2.me/theorems/bd00ceee-fda6-4195-9030-b8a964e1d11b
-- title:
--   Finite probability martingales and bounded stopping: ruMean
-- statement:
--   Finite expectation of a real random variable X under scenario masses p; a genuine probability interpretation requires nonnegative weights summing to one.
--
--   Mathematical relation:
--
--   $$
--   ∑ ω : Fin m, p ω * X ω
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 18 and 23, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://ocw.mit.edu/courses/18-440-probability-and-random-variables-spring-2014/resources/mit18_440s14_lecture35/. The proposed model is rooted in Promislow chapter 18 and 23. The target Lean identity is an original derivation, not a verbatim published result. Published source page 426 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ActuarialValuation

noncomputable def ruMean {m : ℕ} (p X : Fin m → ℝ) : ℝ := ∑ ω : Fin m, p ω * X ω

end ActuarialValuation


