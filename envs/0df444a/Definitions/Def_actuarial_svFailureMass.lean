-- Prove2me | Definitions.Def_actuarial_svFailureMass
-- name    : actuarial_svFailureMass
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:12:29.91848+00:00
-- url     : https://prove2.me/theorems/63f43f56-fe8e-4843-8cca-7c0bd6f1c336
-- title:
--   Measurable lifetime distributions and conditional survival: svFailureMass
-- statement:
--   Mass of exact failure at integer duration k; positive atoms belong to discrete lifetime models.
--
--   Mathematical relation:
--
--   $$
--   μ {ω | T ω = (k : ℝ)}
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 14, 8 and Appendix A, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.actuaries.org.uk/system/files/field/document/Technical%20Workshop%20October%202019%20Slide%20Deck.pdf. Published source page 211 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace ActuarialValuation

noncomputable def svFailureMass {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) (k : ℕ) : ENNReal := μ {ω | T ω = (k : ℝ)}

end ActuarialValuation


