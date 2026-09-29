-- Prove2me | Definitions.Def_NoAdjacentBinaryStrings
-- name    : NoAdjacentBinaryStrings
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-09-25T17:09:11.817686+00:00
-- url     : https://prove2.me/theorems/e5a74c1d-5434-41bf-89bc-fc45f5aa473a
-- title:
--   Binary strings with no adjacent ones: definitions
-- statement:
--   Basic infrastructure for counting binary strings with no adjacent ones.
--
--   A binary string of length n is represented as a function f : Fin n → Bool. The predicate NoAdjacentOnes f states that no two consecutive positions are both true. The same family is represented as finsets of Fin n with no consecutive elements, via Finset.noAdjacent and the canonical equivalence boolFinsetEquiv between Fin n → Bool and Finset (Fin n).
--
--   For strings with exactly k ones, the carrier GapMono n k consists of strictly monotone position embeddings g : Fin k ↪ Fin n whose successive values differ by at least two; it is equipped with a Fintype instance. Four finset families are provided for the counting theorems:
--
--   1. noAdjacentStrings n — all length-n strings with no adjacent ones;
--   2. noAdjacentStringsCard n k — those with exactly k ones;
--   3. noAdjacentFinset n — finsets of Fin n with no consecutive elements;
--   4. noAdjacentFinsetCard n k — those with exactly k elements.
-- source:
--   Kenneth H. Rosen, Discrete Mathematics and Its Applications, 8th ed., McGraw-Hill 2019, Chapter 6 (Counting) and Section 8.1 (Applications of Recurrence Relations): bit strings of length n with no consecutive 1s, equivalently subsets of Fin n with no consecutive elements.

import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic

/-!
# Binary strings with no adjacent ones

A binary string of length `n` is represented, in the most Mathlib-native way, as a
function `f : Fin n → Bool`. A string has *no adjacent ones* when no two consecutive
positions are both `true`. The same family is equivalently the family of finite
subsets of `Fin n` with no two consecutive elements (the independent sets of a path
graph).

This file provides:

* `NoAdjacentOnes` and `Finset.noAdjacent` — the two formulations of the property;
* `boolFinsetEquiv` — the canonical equivalence `(Fin n → Bool) ≃ Finset (Fin n)`;
* `GapMono` — strictly monotone position tuples whose successive entries differ by at
  least two, the carrier used to count strings with exactly `k` ones;
* `noAdjacentStrings`, `noAdjacentStringsCard`, `noAdjacentFinset`,
  `noAdjacentFinsetCard` — the finset families that the counting theorems use.
-/

open Finset Function

/-- A binary string `f : Fin n → Bool` has no adjacent ones: whenever position `i` is
`true`, position `i+1` (if it exists) is `false`. -/
def NoAdjacentOnes {n : ℕ} (f : Fin n → Bool) : Prop :=
  ∀ (i : Fin n) (h : i.val + 1 < n), ¬ (f i ∧ f ⟨i.val + 1, h⟩)

/-- The finset of positions at which a binary string is `true`. -/
def supportFinset {n : ℕ} (f : Fin n → Bool) : Finset (Fin n) :=
  Finset.filter (fun x => f x = true) Finset.univ

/-- A finset of positions has no adjacent elements: whenever `x` belongs to it, the
next position (if it exists) does not. -/
def Finset.noAdjacent {n : ℕ} (s : Finset (Fin n)) : Prop :=
  ∀ (x : Fin n), x ∈ s → ∀ (h : x.val + 1 < n), (⟨x.val + 1, h⟩ : Fin n) ∉ s

/-- The canonical equivalence between binary functions on `Fin n` and finsets of
`Fin n`: a function is sent to the set of positions where it is `true`. -/
def boolFinsetEquiv (n : ℕ) : (Fin n → Bool) ≃ Finset (Fin n) where
  toFun := supportFinset
  invFun := fun s x => (x ∈ s : Bool)
  left_inv := by
    intro f
    ext i
    simp [supportFinset]
  right_inv := by
    intro s
    ext i
    simp [supportFinset]

/-- The carrier of strictly monotone position tuples `g : Fin k ↪ Fin n` whose
successive values differ by at least two. These enumerate the length-`n` binary
strings with exactly `k` ones and no adjacent ones. -/
def GapMono (n k : ℕ) : Type :=
  { g : Fin k ↪ Fin n //
    ∀ (i : Fin k) (h : i.val + 1 < k), (g ⟨i.val + 1, h⟩).val ≥ (g i).val + 2 }

/-- `GapMono` is a finite type: it is a subtype of the finite type of embeddings. -/
noncomputable instance gapMonoFintype (n k : ℕ) : Fintype (GapMono n k) := by
  classical
  exact Subtype.fintype _

/-- Length-`n` binary strings with no adjacent ones. -/
noncomputable def noAdjacentStrings (n : ℕ) : Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.filter NoAdjacentOnes

/-- Length-`n` binary strings with no adjacent ones and exactly `k` ones. -/
noncomputable def noAdjacentStringsCard (n k : ℕ) : Finset (Fin n → Bool) := by
  classical
  exact (noAdjacentStrings n).filter fun f => (supportFinset f).card = k

/-- Finsets of positions in `Fin n` containing no two consecutive positions. -/
noncomputable def noAdjacentFinset (n : ℕ) : Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter Finset.noAdjacent

/-- Finsets of positions in `Fin n` with no two consecutive positions and exactly
`k` elements. -/
noncomputable def noAdjacentFinsetCard (n k : ℕ) : Finset (Finset (Fin n)) := by
  classical
  exact (noAdjacentFinset n).filter fun s => s.card = k


