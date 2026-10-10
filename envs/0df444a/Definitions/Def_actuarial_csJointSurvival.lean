-- Prove2me | Definitions.Def_actuarial_csJointSurvival
-- name    : actuarial_csJointSurvival
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:28:51.040782+00:00
-- url     : https://prove2.me/theorems/1eabd256-1158-476e-b278-6b650cd9ab2b
-- title:
--   Actual joint-lifetime events and cause partition: csJointSurvival
-- statement:
--   Genuine joint survival event, measured under a probability law with strict inequalities at each deadline.
--
--   Mathematical relation:
--
--   $$
--   μ {ω | s < csFirstLife U Z ω ∧ t < csSecondLife V Z ω}
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 11, 17 and 19, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1080/01621459.1967.10482885. The proposed model is rooted in Promislow chapter 11, 17 and 19. The target Lean identity is an original derivation, not a verbatim published result. Published source page 271 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_csFirstLife
import Definitions.Def_actuarial_csSecondLife

namespace ActuarialValuation

noncomputable def csJointSurvival {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (U V Z : Ω → ℝ) (s t : ℝ) : ENNReal := μ {ω | s < csFirstLife U Z ω ∧ t < csSecondLife V Z ω}

end ActuarialValuation


