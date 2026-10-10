-- Prove2me | Definitions.Def_actuarial_svMakehamCumulativeHazard
-- name    : actuarial_svMakehamCumulativeHazard
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:15:05.822983+00:00
-- url     : https://prove2.me/theorems/e98b8380-956d-4ffa-b68f-d2377e4fef57
-- title:
--   Exponential Gompertz Makeham hazards and insurance valuation: svMakehamCumulativeHazard
-- statement:
--   Cumulative Makeham hazard uses linear background and exponential age components, with c nonzero for the usual integral representation.
--
--   Mathematical relation:
--
--   $$
--   a*t+svGompertzCumulativeHazard b c t
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 14, 8 and Appendix A, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.actuaries.org.uk/system/files/field/document/Technical%20Workshop%20October%202019%20Slide%20Deck.pdf. Published source page 211 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svGompertzCumulativeHazard

namespace ActuarialValuation

noncomputable def svMakehamCumulativeHazard (a b c t : ℝ) : ℝ := a*t+svGompertzCumulativeHazard b c t

end ActuarialValuation


