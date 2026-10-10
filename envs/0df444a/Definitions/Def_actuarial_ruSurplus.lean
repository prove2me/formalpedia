-- Prove2me | Definitions.Def_actuarial_ruSurplus
-- name    : actuarial_ruSurplus
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:29:24.048007+00:00
-- url     : https://prove2.me/theorems/071ad3bf-daba-461a-bbd7-ef4afc619d55
-- title:
--   Actuarial surplus and exponential supermartingale: ruSurplus
-- statement:
--   Actuarial surplus capital with deterministic initial capital u and realised net premium-minus-claim increments G(j,ω).
--
--   Mathematical relation:
--
--   $$
--   u + ∑ j ∈ Finset.range k, G j ω
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 18 and 23, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://ocw.mit.edu/courses/18-440-probability-and-random-variables-spring-2014/resources/mit18_440s14_lecture35/. The proposed model is rooted in Promislow chapter 18 and 23. The target Lean identity is an original derivation, not a verbatim published result. Published source page 426 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ActuarialValuation

noncomputable def ruSurplus {m : ℕ} (u : ℝ) (G : ℕ → Fin m → ℝ) (k : ℕ) (ω : Fin m) : ℝ := u + ∑ j ∈ Finset.range k, G j ω

end ActuarialValuation


