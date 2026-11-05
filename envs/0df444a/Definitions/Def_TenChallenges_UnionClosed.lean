-- Prove2me | Definitions.Def_TenChallenges_UnionClosed
-- name    : TenChallenges_UnionClosed
-- status  : Definition
-- author  : @utkuokur
-- created : 2026-11-04T20:46:59.407659+00:00
-- url     : https://prove2.me/theorems/dd7dca72-e512-47b6-8f89-944e4b02b5ab
-- title:
--   Union-closed families, occurrences, density, nondegeneracy
-- statement:
--   The definitions behind Challenge 9 of the Ten Challenges benchmark, for a finite family $\mathcal F$ of finite subsets of a type $U$.
--
--   1. **Union-closed.** $A\cup B\in\mathcal F$ whenever $A,B\in\mathcal F$.
--   2. **Occurrences.** $\mathrm{occ}_{\mathcal F}(x)$ is the number of members of $\mathcal F$ containing $x$.
--   3. **Density.** $\delta_{\mathcal F}(x)=\mathrm{occ}_{\mathcal F}(x)/\max(1,|\mathcal F|)$, a rational number; for nonempty $\mathcal F$ this is the fraction of members containing $x$.
--   4. **Nondegenerate.** $\mathcal F\ne\emptyset$ and $\mathcal F\ne\{\emptyset\}$, the two union-closed families excluded from the conjecture.
--
--   **Formalization Note.** Families are `Finset (Finset U)` with `[DecidableEq U]`; the density is a quotient in `ℚ`, with the denominator $\max(1,|\mathcal F|)$ avoiding division by zero.
-- source:
--   Ten Challenges repository, file Defs_and_Lems/UnionClosed.lean (commit ff14a56), https://github.com/TenChallenges/ten-challenges/blob/main/Defs_and_Lems/UnionClosed.lean; conjecture as in H. Bruhn, O. Schaudt, The journey of the union-closed sets conjecture, Graphs Combin. 31 (2015), Section 1.

import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Ring.Unbundled.Rat

variable {U : Type*} [DecidableEq U] (F : Finset (Finset U))

/-- A finite family of finite sets is union-closed. -/
def IsUnionClosed : Prop :=
  ∀ ⦃A B : Finset U⦄, A ∈ F → B ∈ F → A ∪ B ∈ F

/-- The number of members of the family containing `x`. -/
def occurrences (x : U) : ℕ :=
  (F.filter fun A => x ∈ A).card

/-- The density of an element with respect to a finite family. -/
def density (x : U) : ℚ :=
  (occurrences F x : ℚ) / max 1 F.card

/-- The two degenerate families excluded from the union-closed sets conjecture. -/
def Nondegenerate : Prop :=
  F ≠ ∅ ∧ F ≠ {∅}


