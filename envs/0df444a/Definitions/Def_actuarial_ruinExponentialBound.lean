-- Prove2me | Definitions.Def_actuarial_ruinExponentialBound
-- name    : actuarial_ruinExponentialBound
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:27:40.893592+00:00
-- url     : https://prove2.me/theorems/5646fb5a-48e7-4278-bfb9-dc0a5ae8fc6e
-- title:
--   Lundberg exponential benchmark for an integer initial surplus
-- statement:
--   The benchmark at current surplus u is exp(−Ru). For R≥0 this is at least one if u is negative, allowing it to bound an already-ruined state whose ruin indicator equals one; for a nonnegative initial reserve it falls exponentially with additional starting capital.
--
--   **Mathematical statement**
--
--   $$
--   L_R(u)=e^{-Ru}
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 432 (Library PDF page 458), parent framework: Theorem 23.4 (Lundberg ruin bound). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration actuarial_ruinExponentialBound is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def ruinExponentialBound (adjustment : ℝ) (surplus : ℤ) : ℝ :=
  Real.exp (-(adjustment * (surplus : ℝ)))

end ActuarialValuation


