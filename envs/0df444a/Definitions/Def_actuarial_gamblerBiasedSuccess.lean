-- Prove2me | Definitions.Def_actuarial_gamblerBiasedSuccess
-- name    : actuarial_gamblerBiasedSuccess
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:29:37.675085+00:00
-- url     : https://prove2.me/theorems/c5392ca6-2c1d-48bd-bbab-3f2a46a2af8b
-- title:
--   Biased finite-capital upper-absorption harmonic candidate
-- statement:
--   For a biased unit-stake walk with r=(1−p)/p different from one and a positive upper barrier N, the formula gives the eventual probability of hitting N before zero: (1−r^i)/(1−r^N). The denominator must be nonzero. The fair p=1/2 case requires the separate linear formula.
--
--   **Mathematical statement**
--
--   $$
--   H_p(i)=(1-r^i)/(1-r^N)
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 427 (Library PDF page 453), parent framework: Examples 23.4–23.5 (gambler's ruin). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration actuarial_gamblerBiasedSuccess is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gamblerOddsRatio

namespace ActuarialValuation

noncomputable def gamblerBiasedSuccess
  (target capital : ℕ) (win : ℝ) : ℝ :=
  (1 - (gamblerOddsRatio win) ^ capital) /
    (1 - (gamblerOddsRatio win) ^ target)

end ActuarialValuation


