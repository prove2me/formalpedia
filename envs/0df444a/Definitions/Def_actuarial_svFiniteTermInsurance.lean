-- Prove2me | Definitions.Def_actuarial_svFiniteTermInsurance
-- name    : actuarial_svFiniteTermInsurance
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:13:58.185317+00:00
-- url     : https://prove2.me/theorems/0fb07f4a-1990-461e-a4e9-99e1063866e7
-- title:
--   Discrete failure masses and finite life expectancy: svFiniteTermInsurance
-- statement:
--   End-of-year discrete term-insurance expected present value using deaths in policy year k and discount at year-end k plus one.
--
--   Mathematical relation:
--
--   $$
--   ∑ k ∈ Finset.range n, p k * d (k+1)
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

noncomputable def svFiniteTermInsurance (p d : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, p k * d (k+1)

end ActuarialValuation


