-- Prove2me | Definitions.Def_DeletionCode_CatalogueWords
-- name    : DeletionCode_CatalogueWords
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:11:57.432636+00:00
-- url     : https://prove2.me/theorems/906ebfbe-e27c-4c95-848c-cde27f0471b4
-- title:
--   Catalogue Words
-- statement:
--   Definitions and structural lemmas for Catalogue Words, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueWords.lean

import Definitions.Def_DeletionCode_GeneratingModel
import Init.Data.List.Nat.Erase
set_option autoImplicit true
namespace DeletionCode.CatalogueWords
open Windows HeaderRecovery GeneratingModel
def listLetters (word : List Bool) : Letters := fun i => word.getD i false
structure BubbleWord (k : ℕ) where
  left : List Bool
  right : List Bool
  rho : ℕ
  bit : Bool
  orientation : Orientation
  rho_lower : 1 ≤ rho
  rho_upper : rho ≤ k + 1
  left_length : left.length = windowLength k - rho
  right_length : right.length = windowLength k - rho
namespace BubbleWord
variable {k : ℕ}
def header (bubble : BubbleWord k) : Header :=
  ⟨bubble.orientation, bubble.rho, bubble.bit⟩
def longWord (bubble : BubbleWord k) : List Bool :=
  bubble.left ++ (List.replicate bubble.rho bubble.bit ++ bubble.right)
def shortWord (bubble : BubbleWord k) : List Bool :=
  bubble.left ++ (List.replicate (bubble.rho - 1) bubble.bit ++ bubble.right)
def negativeWord (bubble : BubbleWord k) : List Bool :=
  match bubble.orientation with
  | .deletion => bubble.longWord
  | .insertion => bubble.shortWord
def positiveWord (bubble : BubbleWord k) : List Bool :=
  match bubble.orientation with
  | .deletion => bubble.shortWord
  | .insertion => bubble.longWord
theorem edit_in_run (bubble : BubbleWord k) :
    bubble.left.length ≤ editOffset k ∧
      editOffset k - bubble.left.length < bubble.rho := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  rw [bubble.left_length]
  dsimp [editOffset, windowLength]
  omega
theorem header_bit (bubble : BubbleWord k) :
    listLetters bubble.longWord (editOffset k) = bubble.header.bit := by
  have hleft := bubble.edit_in_run.1
  have hrun := bubble.edit_in_run.2
  simp only [listLetters, longWord, header, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right hleft]
  rw [List.getElem?_append_left (by simpa only [List.length_replicate] using hrun)]
  rw [List.getElem?_replicate_of_lt hrun]
  rfl
end BubbleWord
def editedFamily {B : Type*} {k : ℕ} (bubbles : B → BubbleWord k) (rank : B → ℕ) :
    EditedFamily B k where
  header b := (bubbles b).header
  long b := listLetters (bubbles b).longWord
  rank := rank
  rho_lower b := (bubbles b).rho_lower
  rho_upper b := (bubbles b).rho_upper
  header_bit b := (bubbles b).header_bit
end DeletionCode.CatalogueWords


