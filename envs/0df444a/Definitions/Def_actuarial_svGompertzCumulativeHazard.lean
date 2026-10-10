-- Prove2me | Definitions.Def_actuarial_svGompertzCumulativeHazard
-- name    : actuarial_svGompertzCumulativeHazard
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:14:36.475978+00:00
-- url     : https://prove2.me/theorems/4820f40e-7e44-4915-8d3d-7a50595675f2
-- title:
--   Exponential Gompertz Makeham hazards and insurance valuation: svGompertzCumulativeHazard
-- statement:
--   Gompertz cumulative hazard integrated from zero when the age slope c is nonzero.
--
--   Mathematical relation:
--
--   $$
--   (b/c) * (Real.exp (c*t)-1)
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

noncomputable def svGompertzCumulativeHazard (b c t : ℝ) : ℝ := (b/c) * (Real.exp (c*t)-1)

end ActuarialValuation


