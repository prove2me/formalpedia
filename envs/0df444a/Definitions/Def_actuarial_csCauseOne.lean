-- Prove2me | Definitions.Def_actuarial_csCauseOne
-- name    : actuarial_csCauseOne
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:28:59.651444+00:00
-- url     : https://prove2.me/theorems/e4068bc3-59a6-48b0-9633-656672ad7a69
-- title:
--   Actual joint-lifetime events and cause partition: csCauseOne
-- statement:
--   Probability that idiosyncratic cause one is strictly the first failure; primitive ties belong to a separate event.
--
--   Mathematical relation:
--
--   $$
--   μ {ω | U ω < V ω ∧ U ω < Z ω}
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

noncomputable def csCauseOne {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (U V Z : Ω → ℝ) : ENNReal := μ {ω | U ω < V ω ∧ U ω < Z ω}

end ActuarialValuation


