-- Prove2me | Definitions.Def_actuarial_ruinClaimMass
-- name    : actuarial_ruinClaimMass
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:27:24.332384+00:00
-- url     : https://prove2.me/theorems/21b89c31-72d6-4824-aafd-93902d4b1656
-- title:
--   Total annual claim probability on a bounded integer grid
-- statement:
--   The finite annual aggregate-claim model has possible integer loss amounts 0 through B. Its total probability is the sum of those coefficients, required to equal one in the genuine probability interpretation of the recursion.
--
--   **Mathematical statement**
--
--   $$
--   \sum_{k=0}^{B}w_k=1
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 432 (Library PDF page 458), parent framework: Theorem 23.4 (Lundberg ruin bound). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration actuarial_ruinClaimMass is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def ruinClaimMass (w : ℕ → ℝ) (bound : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (bound + 1), w k

end ActuarialValuation


