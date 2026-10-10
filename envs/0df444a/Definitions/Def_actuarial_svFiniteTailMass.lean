-- Prove2me | Definitions.Def_actuarial_svFiniteTailMass
-- name    : actuarial_svFiniteTailMass
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:13:49.681262+00:00
-- url     : https://prove2.me/theorems/77b00f49-ed3d-4d1d-83ca-ba3be2b002a0
-- title:
--   Discrete failure masses and finite life expectancy: svFiniteTailMass
-- statement:
--   Finite discrete strict-tail mass above age k, under support contained in zero through n.
--
--   Mathematical relation:
--
--   $$
--   ∑ j ∈ Finset.Icc (k+1) n, p j
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

noncomputable def svFiniteTailMass (p : ℕ → ℝ) (n k : ℕ) : ℝ := ∑ j ∈ Finset.Icc (k+1) n, p j

end ActuarialValuation


