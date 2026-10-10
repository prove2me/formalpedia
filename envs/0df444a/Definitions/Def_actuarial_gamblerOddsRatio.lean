-- Prove2me | Definitions.Def_actuarial_gamblerOddsRatio
-- name    : actuarial_gamblerOddsRatio
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:29:12.426437+00:00
-- url     : https://prove2.me/theorems/b222ed3b-7189-4be5-b3e1-9d1e21a55bd3
-- title:
--   Downward-to-upward transition probability ratio
-- statement:
--   The fixed probability of an up step is p; the probability of a down step is 1−p. Their ratio (1−p)/p controls the biased harmonic solution and requires p>0 to be interpreted as transition odds.
--
--   **Mathematical statement**
--
--   $$
--   r=(1-p)/p
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 427 (Library PDF page 453), parent framework: Examples 23.4–23.5 (gambler's ruin). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration actuarial_gamblerOddsRatio is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def gamblerOddsRatio (win : ℝ) : ℝ :=
  (1 - win) / win

end ActuarialValuation


