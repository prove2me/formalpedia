-- Prove2me | Definitions.Def_actuarial_ruRuinProbability
-- name    : actuarial_ruRuinProbability
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:30:24.591618+00:00
-- url     : https://prove2.me/theorems/c3b190b5-a161-4cf2-89a9-b60afd5cb0d3
-- title:
--   Ruin events and finite-horizon Lundberg bound: ruRuinProbability
-- statement:
--   Actual probability of a scenario-defined ruin event when p is a normalised probability mass function.
--
--   Mathematical relation:
--
--   $$
--   ∑ ω : Fin m, if ruin ω then p ω else 0
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 18 and 23, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://ocw.mit.edu/courses/18-440-probability-and-random-variables-spring-2014/resources/mit18_440s14_lecture35/. The proposed model is rooted in Promislow chapter 18 and 23. The target Lean identity is an original derivation, not a verbatim published result. Published source page 426 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ActuarialValuation

noncomputable def ruRuinProbability {m : ℕ} (p : Fin m → ℝ) (ruin : Fin m → Prop) [DecidablePred ruin] : ℝ := ∑ ω : Fin m, if ruin ω then p ω else 0

end ActuarialValuation


