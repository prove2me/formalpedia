-- Prove2me | Definitions.Def_actuarial_svFiniteMassMean
-- name    : actuarial_svFiniteMassMean
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:13:39.779563+00:00
-- url     : https://prove2.me/theorems/b1e776bb-c8bf-482b-9634-a6f89f785e19
-- title:
--   Discrete failure masses and finite life expectancy: svFiniteMassMean
-- statement:
--   Expected integer failure age for a distribution with real probability masses restricted to zero through n, assuming mass normalisation.
--
--   Mathematical relation:
--
--   $$
--   ∑ k ∈ Finset.range (n+1), (k:ℝ) * p k
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

noncomputable def svFiniteMassMean (p : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range (n+1), (k:ℝ) * p k

end ActuarialValuation


