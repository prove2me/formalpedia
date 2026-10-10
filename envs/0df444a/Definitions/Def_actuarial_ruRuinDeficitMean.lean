-- Prove2me | Definitions.Def_actuarial_ruRuinDeficitMean
-- name    : actuarial_ruRuinDeficitMean
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:31:01.63303+00:00
-- url     : https://prove2.me/theorems/4c7952eb-6565-4f14-a94d-d7a6bda3b047
-- title:
--   Ruin events and finite-horizon Lundberg bound: ruRuinDeficitMean
-- statement:
--   Expected nonnegative terminal deficit across all scenarios, including the zero deficit on solvent paths.
--
--   Mathematical relation:
--
--   $$
--   ruMean p (fun ω => ruRuinDeficit (terminal ω))
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 18 and 23, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://ocw.mit.edu/courses/18-440-probability-and-random-variables-spring-2014/resources/mit18_440s14_lecture35/. The proposed model is rooted in Promislow chapter 18 and 23. The target Lean identity is an original derivation, not a verbatim published result. Published source page 426 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruMean
import Definitions.Def_actuarial_ruRuinDeficit

namespace ActuarialValuation

noncomputable def ruRuinDeficitMean {m : ℕ} (p : Fin m → ℝ) (terminal : Fin m → ℝ) : ℝ := ruMean p (fun ω => ruRuinDeficit (terminal ω))

end ActuarialValuation


