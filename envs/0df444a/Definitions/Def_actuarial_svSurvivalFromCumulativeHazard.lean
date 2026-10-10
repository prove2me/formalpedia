-- Prove2me | Definitions.Def_actuarial_svSurvivalFromCumulativeHazard
-- name    : actuarial_svSurvivalFromCumulativeHazard
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:15:27.463663+00:00
-- url     : https://prove2.me/theorems/ee3cad3b-8f1d-4e87-bec3-2d448a1a0417
-- title:
--   Exponential Gompertz Makeham hazards and insurance valuation: svSurvivalFromCumulativeHazard
-- statement:
--   Recover model survival by exponentiating the negative cumulative hazard; proper lifetime distributions additionally require divergence of cumulative hazard at infinity.
--
--   Mathematical relation:
--
--   $$
--   Real.exp (-h)
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

noncomputable def svSurvivalFromCumulativeHazard (h : ℝ) : ℝ := Real.exp (-h)

end ActuarialValuation


