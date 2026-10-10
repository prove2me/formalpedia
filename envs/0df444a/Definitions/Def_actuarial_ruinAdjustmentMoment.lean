-- Prove2me | Definitions.Def_actuarial_ruinAdjustmentMoment
-- name    : actuarial_ruinAdjustmentMoment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:27:31.203186+00:00
-- url     : https://prove2.me/theorems/3fff89aa-2108-41e6-aec3-f921e2349c52
-- title:
--   Exponential moment of one period's net insurance loss
-- statement:
--   The adjustment coefficient R compares the annual aggregate claim X with the premium c via the exponential moment E[exp(R(X−c))]. When this quantity is no greater than one and R≥0, the exponential capital bound becomes a supermartingale-style one-step estimate.
--
--   **Mathematical statement**
--
--   $$
--   M(R)=\sum_{k=0}^{B}w_k e^{R(k-c)}
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 432 (Library PDF page 458), parent framework: Theorem 23.4 (Lundberg ruin bound). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration actuarial_ruinAdjustmentMoment is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def ruinAdjustmentMoment
  (w : ℕ → ℝ) (bound premium : ℕ) (adjustment : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (bound + 1),
    w k * Real.exp (adjustment * ((k : ℝ) - (premium : ℝ)))

end ActuarialValuation


