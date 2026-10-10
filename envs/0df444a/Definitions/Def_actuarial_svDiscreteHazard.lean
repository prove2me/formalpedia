-- Prove2me | Definitions.Def_actuarial_svDiscreteHazard
-- name    : actuarial_svDiscreteHazard
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:12:51.009098+00:00
-- url     : https://prove2.me/theorems/91a422e1-78f6-4789-8bad-0d0f79ecaea2
-- title:
--   Measurable lifetime distributions and conditional survival: svDiscreteHazard
-- statement:
--   Discrete conditional death probability at positive integer k, given survival strictly after k minus one; it requires a nonzero at-risk denominator.
--
--   Mathematical relation:
--
--   $$
--   svFailureMass μ T k / svSurvival μ T ((k:ℝ)-1)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 14, 8 and Appendix A, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.actuaries.org.uk/system/files/field/document/Technical%20Workshop%20October%202019%20Slide%20Deck.pdf. Published source page 211 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svFailureMass
import Definitions.Def_actuarial_svSurvival

namespace ActuarialValuation

noncomputable def svDiscreteHazard {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) (k : ℕ) : ENNReal := svFailureMass μ T k / svSurvival μ T ((k:ℝ)-1)

end ActuarialValuation


