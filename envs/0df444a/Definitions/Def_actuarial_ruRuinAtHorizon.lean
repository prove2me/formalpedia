-- Prove2me | Definitions.Def_actuarial_ruRuinAtHorizon
-- name    : actuarial_ruRuinAtHorizon
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:30:12.312006+00:00
-- url     : https://prove2.me/theorems/04652304-0627-4082-bdd6-23cce8fd800e
-- title:
--   Ruin events and finite-horizon Lundberg bound: ruRuinAtHorizon
-- statement:
--   Finite-horizon ruin event occurs when realised insurer surplus is strictly negative at any policy anniversary through N.
--
--   Mathematical relation:
--
--   $$
--   ∃ k ∈ Finset.range (N+1), ruSurplus u G k ω < 0
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 18 and 23, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://ocw.mit.edu/courses/18-440-probability-and-random-variables-spring-2014/resources/mit18_440s14_lecture35/. The proposed model is rooted in Promislow chapter 18 and 23. The target Lean identity is an original derivation, not a verbatim published result. Published source page 426 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruSurplus

namespace ActuarialValuation

noncomputable def ruRuinAtHorizon {m : ℕ} (u : ℝ) (G : ℕ → Fin m → ℝ) (N : ℕ) (ω : Fin m) : Prop := ∃ k ∈ Finset.range (N+1), ruSurplus u G k ω < 0

end ActuarialValuation


