-- Prove2me | Definitions.Def_actuarial_svExpCumulativeHazard
-- name    : actuarial_svExpCumulativeHazard
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:14:17.890545+00:00
-- url     : https://prove2.me/theorems/9a85b5a7-26fa-4640-b74d-b8e964b54775
-- title:
--   Exponential Gompertz Makeham hazards and insurance valuation: svExpCumulativeHazard
-- statement:
--   Cumulative hazard for a constant hazard rate over duration t, with lambda in inverse years.
--
--   Mathematical relation:
--
--   $$
--   lambda*t
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

noncomputable def svExpCumulativeHazard (lambda t : ℝ) : ℝ := lambda*t

end ActuarialValuation


