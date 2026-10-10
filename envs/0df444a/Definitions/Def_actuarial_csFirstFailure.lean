-- Prove2me | Definitions.Def_actuarial_csFirstFailure
-- name    : actuarial_csFirstFailure
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:28:35.590083+00:00
-- url     : https://prove2.me/theorems/5eff2db9-9e94-4f3f-9e38-c61f2c456187
-- title:
--   Actual joint-lifetime events and cause partition: csFirstFailure
-- statement:
--   First failure is the minimum of all three primitive causes, including the common shock.
--
--   Mathematical relation:
--
--   $$
--   min (U ω) (min (V ω) (Z ω))
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 11, 17 and 19, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1080/01621459.1967.10482885. The proposed model is rooted in Promislow chapter 11, 17 and 19. The target Lean identity is an original derivation, not a verbatim published result. Published source page 271 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace ActuarialValuation

noncomputable def csFirstFailure {Ω : Type*} (U V Z : Ω → ℝ) (ω : Ω) : ℝ := min (U ω) (min (V ω) (Z ω))

end ActuarialValuation


