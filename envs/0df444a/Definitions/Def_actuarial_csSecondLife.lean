-- Prove2me | Definitions.Def_actuarial_csSecondLife
-- name    : actuarial_csSecondLife
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:28:26.514596+00:00
-- url     : https://prove2.me/theorems/df09efcb-56d5-42fb-a996-a4faa9d9408b
-- title:
--   Actual joint-lifetime events and cause partition: csSecondLife
-- statement:
--   Observed second life ends at the minimum of its idiosyncratic and common-shock event times.
--
--   Mathematical relation:
--
--   $$
--   min (V ω) (Z ω)
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

noncomputable def csSecondLife {Ω : Type*} (V Z : Ω → ℝ) (ω : Ω) : ℝ := min (V ω) (Z ω)

end ActuarialValuation


