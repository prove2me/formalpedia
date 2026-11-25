-- Prove2me | Definitions.Def_KneserLib_KneserLabel
-- name    : KneserLib_KneserLabel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:51:06.642785+00:00
-- url     : https://prove2.me/theorems/351730ae-085c-41f0-86c3-1ad272b778a7
-- title:
--   Kneser Label
-- statement:
--   Definitions and structural lemmas for Kneser Label, from Juan Pablo Traverso Gianini (jtraverso/kneser-lovasz; see pinned Apache-2.0 LICENSE and source headers)'s pinned Kneser's conjecture and the octahedral Tucker lemma development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean

module
public import Mathlib
public import Definitions.Def_KneserLib_TuckerParity
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace KneserColouring
open Finset
variable {n k q : ℕ}
def upperCol (hk : 0 < k) (s : {s : Finset (Fin n) // s.card = k}) : Fin (n - 2 * k + 2) :=
  ⟨min (s.1.min' (card_pos.1 (by rw [s.2]; exact hk))).val (n - 2 * k + 1), by omega⟩
def setCol (c : {s : Finset (Fin n) // s.card = k} → Fin q) (A : Finset (Fin n)) : ℕ :=
  if h : A.card = k then (c ⟨A, h⟩).val + 1 else 0
def maxCol (c : {s : Finset (Fin n) // s.card = k} → Fin q) (B : Finset (Fin n)) : ℕ :=
  (B.powersetCard k).sup (setCol c)
def posPart (x : Fin n → SignType) : Finset (Fin n) := univ.filter (fun i => x i = 1)
def negPart (x : Fin n → SignType) : Finset (Fin n) := univ.filter (fun i => x i = -1)
def suppCard (x : Fin n → SignType) : ℕ := (univ.filter (fun i => x i ≠ 0)).card
open Classical in
/-- Matoušek's labelling: `±|x|` if `|x| ≤ 2k - 2` (the sign chosen antipodally via the
lexicographic order), otherwise `±(2k - 2 + maximal shifted colour of a k-subset of x⁺ or x⁻)`,
with sign `+` iff the maximum is attained in `x⁺`. -/
noncomputable def kLab (c : {s : Finset (Fin n) // s.card = k} → Fin q)
    (x : Fin n → SignType) : ℤ :=
  if suppCard x ≤ 2 * k - 2 then
    (if toLex (-x) < toLex x then (suppCard x : ℤ) else -(suppCard x : ℤ))
  else if maxCol c (negPart x) < maxCol c (posPart x) then
    ((2 * k - 2 + maxCol c (posPart x) : ℕ) : ℤ)
  else -((2 * k - 2 + maxCol c (negPart x) : ℕ) : ℤ)
section Prec
variable {x y : Fin n → SignType} (hxy : ∀ i, x i ≠ 0 → x i = y i)
include hxy
end Prec
end KneserColouring


