-- Prove2me | Definitions.Def_actuarial_ruExponentialSurplus
-- name    : actuarial_ruExponentialSurplus
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:29:51.335968+00:00
-- url     : https://prove2.me/theorems/d1181f14-64f9-42a2-8ac3-6c652c80196d
-- title:
--   Actuarial surplus and exponential supermartingale: ruExponentialSurplus
-- statement:
--   Exponential surplus process used as candidate positive supermartingale for ruin bounds.
--
--   Mathematical relation:
--
--   $$
--   ruExponential R (ruSurplus u G k ω)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 18 and 23, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://ocw.mit.edu/courses/18-440-probability-and-random-variables-spring-2014/resources/mit18_440s14_lecture35/. The proposed model is rooted in Promislow chapter 18 and 23. The target Lean identity is an original derivation, not a verbatim published result. Published source page 426 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruExponential
import Definitions.Def_actuarial_ruSurplus

namespace ActuarialValuation

noncomputable def ruExponentialSurplus {m : ℕ} (u R : ℝ) (G : ℕ → Fin m → ℝ) (k : ℕ) (ω : Fin m) : ℝ := ruExponential R (ruSurplus u G k ω)

end ActuarialValuation


