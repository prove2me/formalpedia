-- Prove2me | Definitions.Def_actuarial_gamblerFiniteSuccess
-- name    : actuarial_gamblerFiniteSuccess
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:29:47.889742+00:00
-- url     : https://prove2.me/theorems/b4153630-8f74-4c0b-93ad-455b26b8bfc0
-- title:
--   Probability of hitting upper capital target within finitely many steps
-- statement:
--   The bounded random walk makes unit upward jumps with probability p and unit downward jumps with probability 1−p. It is absorbed at capital zero or at or above target N. This finite-horizon recursion records only the probability of reaching the success barrier by time n; ongoing paths at the horizon remain unresolved.
--
--   **Mathematical statement**
--
--   $$
--   S_0(i)=\mathbf1_{\{i\ge N,i>0\}},\quad S_{n+1}(i)=p S_n(i+1)+(1-p)S_n(i-1)
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 427 (Library PDF page 453), parent framework: Examples 23.4–23.5 (gambler's ruin). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration actuarial_gamblerFiniteSuccess is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def gamblerFiniteSuccess (target : ℕ) (win : ℝ) :
    ℕ → ℕ → ℝ
  | 0, capital =>
      if capital = 0 then 0 else if target ≤ capital then 1 else 0
  | n + 1, capital =>
      if capital = 0 then 0 else if target ≤ capital then 1 else
        win * gamblerFiniteSuccess target win n (capital + 1) +
          (1 - win) * gamblerFiniteSuccess target win n (capital - 1)

end ActuarialValuation


