-- Prove2me | Definitions.Def_actuarial_ruExpectedStopped
-- name    : actuarial_ruExpectedStopped
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:28:56.042549+00:00
-- url     : https://prove2.me/theorems/b33a3b81-3f35-400d-a8b1-7cd9b3f0759c
-- title:
--   Finite probability martingales and bounded stopping: ruExpectedStopped
-- statement:
--   Actual finite-scenario expectation of the stopped process, with horizon k.
--
--   Mathematical relation:
--
--   $$
--   ruMean p (ruStopped X τ k)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 18 and 23, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://ocw.mit.edu/courses/18-440-probability-and-random-variables-spring-2014/resources/mit18_440s14_lecture35/. The proposed model is rooted in Promislow chapter 18 and 23. The target Lean identity is an original derivation, not a verbatim published result. Published source page 426 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruMean
import Definitions.Def_actuarial_ruStopped

namespace ActuarialValuation

noncomputable def ruExpectedStopped {m : ℕ} (p : Fin m → ℝ) (X : ℕ → Fin m → ℝ) (τ : Fin m → ℕ) (k : ℕ) : ℝ := ruMean p (ruStopped X τ k)

end ActuarialValuation


