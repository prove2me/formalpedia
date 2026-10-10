-- Prove2me | Definitions.Def_actuarial_ruStopped
-- name    : actuarial_ruStopped
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:28:38.946042+00:00
-- url     : https://prove2.me/theorems/b5ed4096-ba88-409f-8809-876b69453a46
-- title:
--   Finite probability martingales and bounded stopping: ruStopped
-- statement:
--   Stopped stochastic process at time k, frozen once bounded scenario-dependent stopping time τ is reached.
--
--   Mathematical relation:
--
--   $$
--   X (min k (τ ω)) ω
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 18 and 23, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://ocw.mit.edu/courses/18-440-probability-and-random-variables-spring-2014/resources/mit18_440s14_lecture35/. The proposed model is rooted in Promislow chapter 18 and 23. The target Lean identity is an original derivation, not a verbatim published result. Published source page 426 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ActuarialValuation

noncomputable def ruStopped {m : ℕ} (X : ℕ → Fin m → ℝ) (τ : Fin m → ℕ) (k : ℕ) (ω : Fin m) : ℝ := X (min k (τ ω)) ω

end ActuarialValuation


