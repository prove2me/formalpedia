-- Prove2me | Definitions.Def_actuarial_gamblerFiniteRuin
-- name    : actuarial_gamblerFiniteRuin
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:29:57.946462+00:00
-- url     : https://prove2.me/theorems/0f5d7a07-e6a7-4923-88ad-fcea3a2623fb
-- title:
--   Probability of reaching zero capital within finitely many steps
-- statement:
--   The second finite-horizon recursion tracks absorption at zero capital, the ruin boundary. Successful absorption at the upper target contributes zero ruin probability. At an interior state it mixes successor ruin probabilities, and paths still active at horizon n contribute to neither finite success nor finite ruin.
--
--   **Mathematical statement**
--
--   $$
--   R_0(i)=\mathbf1_{\{i=0\}},\quad R_{n+1}(i)=p R_n(i+1)+(1-p)R_n(i-1)
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 427 (Library PDF page 453), parent framework: Examples 23.4–23.5 (gambler's ruin). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration actuarial_gamblerFiniteRuin is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def gamblerFiniteRuin (target : ℕ) (win : ℝ) :
    ℕ → ℕ → ℝ
  | 0, capital =>
      if capital = 0 then 1 else 0
  | n + 1, capital =>
      if capital = 0 then 1 else if target ≤ capital then 0 else
        win * gamblerFiniteRuin target win n (capital + 1) +
          (1 - win) * gamblerFiniteRuin target win n (capital - 1)

end ActuarialValuation


