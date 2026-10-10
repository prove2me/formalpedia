-- Prove2me | Definitions.Def_actuarial_gamblerFairSuccess
-- name    : actuarial_gamblerFairSuccess
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:29:04.396386+00:00
-- url     : https://prove2.me/theorems/7f10b20e-a926-42a7-a387-a9f36c1c7513
-- title:
--   Fair finite-capital eventual upper-absorption harmonic candidate
-- statement:
--   A fair unit-stake random walk on capital states zero through positive target N has eventual upper-barrier success probability i/N when starting from integer capital i in the bounded interval. This source defines the harmonic candidate, not the underlying stochastic stopping-time construction.
--
--   **Mathematical statement**
--
--   $$
--   H_{\rm fair}(i)=i/N
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 427 (Library PDF page 453), parent framework: Examples 23.4–23.5 (gambler's ruin). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration actuarial_gamblerFairSuccess is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def gamblerFairSuccess (target capital : ℕ) : ℝ :=
  (capital : ℝ) / (target : ℝ)

end ActuarialValuation


