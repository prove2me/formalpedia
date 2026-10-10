-- Prove2me | Definitions.Def_actuarial_csCauseInsurancePV
-- name    : actuarial_csCauseInsurancePV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:30:52.754456+00:00
-- url     : https://prove2.me/theorems/344adde4-9929-4228-a4d8-14bdf8cac5d6
-- title:
--   Cause-contingent actuarial benefits and dependence: csCauseInsurancePV
-- statement:
--   Actual cause-contingent expected benefit present value at a common deterministic payment time, with separate amounts for each first-cause event.
--
--   Mathematical relation:
--
--   $$
--   disc * (b1 * (csCauseOne μ U V Z).toReal + b2 * (csCauseTwo μ U V Z).toReal + bz * (csShockCause μ U V Z).toReal)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 11, 17 and 19, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1080/01621459.1967.10482885. The proposed model is rooted in Promislow chapter 11, 17 and 19. The target Lean identity is an original derivation, not a verbatim published result. Published source page 271 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_csCauseOne
import Definitions.Def_actuarial_csCauseTwo
import Definitions.Def_actuarial_csShockCause

namespace ActuarialValuation

noncomputable def csCauseInsurancePV {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (U V Z : Ω → ℝ) (disc b1 b2 bz : ℝ) : ℝ := disc * (b1 * (csCauseOne μ U V Z).toReal + b2 * (csCauseTwo μ U V Z).toReal + bz * (csShockCause μ U V Z).toReal)

end ActuarialValuation


