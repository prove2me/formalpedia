-- Prove2me | Definitions.Def_ChapterFreeFieldBornSignOrientationQuotient
-- name    : ChapterFreeFieldBornSignOrientationQuotient
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-10T08:35:11.727981+00:00
-- url     : https://prove2.me/theorems/387642bc-18d2-4d52-8ace-ab05b9db1583
-- title:
--   ChapterFreeFieldBornSignOrientationQuotient

import Theorems.Thm_BookProof_ChapterFreeFieldBornSignOrientationSubgroup_mem_orientationPreservingSigns_iff_even

import Definitions.Def_ChapterFreeFieldBornSignOrientationSubgroup
import Definitions.Def_ChapterFreeFieldBornSignHom
import Mathlib


/-!
# The orientation character and the two-element quotient

This file realizes the index-two result structurally. Summing the boolean flip
coordinates gives a homomorphism to `Bool`; it is the parity/orientation
character. Its kernel is exactly the orientation-preserving sign subgroup, and
in positive dimension the first isomorphism theorem identifies the quotient
with `Bool`.
-/

open BookProof.ChapterFreeFieldBornSignHom
open BookProof.ChapterFreeFieldBornSignOrientationSubgroup

namespace BookProof.ChapterFreeFieldBornSignOrientationQuotient

/-- The parity character of a boolean sign choice. Addition on `Bool` is xor. -/
def orientationCharacter (n : ℕ) : (Fin n → Bool) →+ Bool where
  toFun b := ∑ k, b k
  map_zero' := by simp
  map_add' := by
    intro b₁ b₂
    simp [Finset.sum_add_distrib]

@[simp] theorem orientationCharacter_apply {n : ℕ} (b : Fin n → Bool) :
    orientationCharacter n b = ∑ k, b k :=
  rfl

/-
The boolean parity sum vanishes exactly when the Hamming weight is even.
-/
theorem boolSum_eq_false_iff_even_card {α : Type*} (s : Finset α) (f : α → Bool) :
    (∑ k ∈ s, f k) = false ↔ Even (s.filter (fun k => f k = true)).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp; rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.filter_insert]
    cases hfa : f a with
    | false =>
      simpa [hfa] using
        show (∑ x ∈ s, f x) = 0 ↔ Even {k ∈ s | f k = true}.card from ih
    | true =>
      have hcard : (insert a (s.filter (fun k => f k = true))).card
          = (s.filter (fun k => f k = true)).card + 1 :=
        Finset.card_insert_of_notMem (by simp [ha])
      rw [if_pos rfl, hcard]
      cases hs : (∑ k ∈ s, f k) with
      | false => simp [Nat.even_add_one, ih.1 hs]
      | true =>
        have hno : ¬ Even (s.filter (fun k => f k = true)).card := by
          intro h; simpa [hs] using ih.2 h
        simp only [Nat.even_add_one, hno, not_false_iff, iff_true]
        decide

theorem orientationCharacter_eq_false_iff_even {n : ℕ} (b : Fin n → Bool) :
    orientationCharacter n b = false ↔ Even (flipCount b) := by
  simpa [orientationCharacter, flipCount] using boolSum_eq_false_iff_even_card Finset.univ b

/-
The orientation-preserving sign subgroup is the kernel of the parity
character.
-/
theorem orientationCharacter_ker (n : ℕ) :
    (orientationCharacter n).ker = orientationPreservingSigns n := by
  ext b
  rw [AddMonoidHom.mem_ker]
  change orientationCharacter n b = false ↔ b ∈ orientationPreservingSigns n
  rw [orientationCharacter_eq_false_iff_even,
    mem_orientationPreservingSigns_iff_even]

/-
In positive dimension the orientation character is onto: flipping the first
coordinate represents the orientation-reversing class.
-/
theorem orientationCharacter_surjective (n : ℕ) :
    Function.Surjective (orientationCharacter (n + 1)) := by
  intro x
  use fun k => if k = 0 then x else 0
  aesop

/-- The quotient of all boolean sign choices by the orientation-preserving
subgroup is the two-element group `Bool`. -/
noncomputable def orientationQuotientEquiv (n : ℕ) :
    ((Fin (n + 1) → Bool) ⧸ orientationPreservingSigns (n + 1)) ≃+ Bool :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (orientationCharacter_ker (n + 1)).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (orientationCharacter (n + 1)) (orientationCharacter_surjective n))

/-
The quotient equivalence sends the class of a sign choice to its parity
character.
-/


end BookProof.ChapterFreeFieldBornSignOrientationQuotient


