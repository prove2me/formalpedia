-- Prove2me | Definitions.Def_actuarial_ruinProbabilityFinite
-- name    : actuarial_ruinProbabilityFinite
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:27:53.709233+00:00
-- url     : https://prove2.me/theorems/5e7c38c2-9fc6-4c33-bd3c-5e21ac8665e0
-- title:
--   First-passage ruin probability over a finite number of annual periods
-- statement:
--   The probability of ruin by horizon n records whether surplus was ever strictly negative. Already-ruined integer states have probability one at any horizon. Otherwise the next-year claim distribution mixes the ruin probabilities of all possible updated signed surpluses, recursively for n further years. The horizon is finite and annual claims are modelled as conditionally independent copies of w.
--
--   **Mathematical statement**
--
--   $$
--   \psi_0(u)=\mathbf1_{\{u<0\}},\quad\psi_{n+1}(u)=\mathbf1_{\{u<0\}}+\mathbf1_{\{u\ge0\}}\sum_kw_k\psi_n(u+c-k)
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 432 (Library PDF page 458), parent framework: Theorem 23.4 (Lundberg ruin bound). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration actuarial_ruinProbabilityFinite is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinNextSurplus

namespace ActuarialValuation

noncomputable def ruinProbabilityFinite
  (w : ℕ → ℝ) (bound premium : ℕ) :
    ℕ → ℤ → ℝ
  | 0, u => if u < 0 then 1 else 0
  | n + 1, u =>
      if u < 0 then 1 else
        ∑ k ∈ Finset.range (bound + 1),
          w k * ruinProbabilityFinite w bound premium n
            (ruinNextSurplus u premium k)

end ActuarialValuation


