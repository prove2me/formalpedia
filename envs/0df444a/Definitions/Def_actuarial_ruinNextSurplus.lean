-- Prove2me | Definitions.Def_actuarial_ruinNextSurplus
-- name    : actuarial_ruinNextSurplus
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:27:13.136713+00:00
-- url     : https://prove2.me/theorems/e9c2f86f-4fc0-4b2a-b9d6-9d260a5c18b6
-- title:
--   One-period integer insurance surplus update
-- statement:
--   The insurer begins a period with an integer surplus, receives a fixed nonnegative integer premium, then pays the period's aggregate integer claim. The next surplus can be negative, so it is represented as an integer rather than a natural number with saturating subtraction.
--
--   **Mathematical statement**
--
--   $$
--   U_{t+1}=U_t+c-X_{t+1}
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 432 (Library PDF page 458), parent framework: Theorem 23.4 (Lundberg ruin bound). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration actuarial_ruinNextSurplus is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def ruinNextSurplus (surplus : ℤ) (premium claim : ℕ) : ℤ :=
  surplus + (premium : ℤ) - (claim : ℤ)

end ActuarialValuation


