-- Prove2me | Definitions.Def_actuarial_svShiftLifetime
-- name    : actuarial_svShiftLifetime
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:13:30.091266+00:00
-- url     : https://prove2.me/theorems/b13f738d-5bae-40ee-8049-d6afceeefad7
-- title:
--   Measurable lifetime distributions and conditional survival: svShiftLifetime
-- statement:
--   Shifted lifetime random variable measured from conditional valuation time s; conditioning is a separate probability operation.
--
--   Mathematical relation:
--
--   $$
--   T ω - s
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

noncomputable def svShiftLifetime {Ω : Type*} (T : Ω → ℝ) (s : ℝ) (ω : Ω) : ℝ := T ω - s

end ActuarialValuation


