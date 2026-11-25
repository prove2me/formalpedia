-- Prove2me | Definitions.Def_KneserLib_TuckerRooms
-- name    : KneserLib_TuckerRooms
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:45:01.172784+00:00
-- url     : https://prove2.me/theorems/1fe40c57-3d0c-495d-84b0-62c81c53d0df
-- title:
--   Tucker Rooms
-- statement:
--   Definitions and structural lemmas for Tucker Rooms, from Juan Pablo Traverso Gianini (jtraverso/kneser-lovasz; see pinned Apache-2.0 LICENSE and source headers)'s pinned Kneser's conjecture and the octahedral Tucker lemma development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerRooms.lean

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace KneserColouring
open Finset
variable {n : ℕ}
abbrev Room (n : ℕ) : Type := (Fin n → SignType) × Equiv.Perm (Fin n)
def pref (r : Room n) (i : ℕ) : Fin n → SignType :=
  fun c => if (r.2 c).val < i then r.1 c else 0
def IsRoom (k : ℕ) (r : Room n) : Prop :=
  (∀ c, r.1 c ≠ 0 ↔ c.val < k) ∧ ∀ c : Fin n, k ≤ c.val → r.2 c = c
instance (k : ℕ) (r : Room n) : Decidable (IsRoom k r) := by
  unfold IsRoom; infer_instance
def IsUpper (k : ℕ) (r : Room n) : Prop :=
  IsRoom k r ∧ ∀ c : Fin n, c.val + 1 = k → r.1 c = 1
instance (k : ℕ) (r : Room n) : Decidable (IsUpper k r) := by
  unfold IsUpper; infer_instance
def rlab (lab : (Fin n → SignType) → ℤ) (r : Room n) (i : ℕ) : ℤ := lab (pref r (i + 1))
def labSet (lab : (Fin n → SignType) → ℤ) (k : ℕ) (r : Room n) : Finset ℤ :=
  (range k).image (rlab lab r)
def altCount (lab : (Fin n → SignType) → ℤ) (k : ℕ) : ℕ :=
  (univ.filter (fun r : Room n => IsUpper k r ∧
    (IsAlt 0 (labSet lab k r) ∨ IsAlt 1 (labSet lab k r)) ∧ (labSet lab k r).card = k)).card
def door (lab : (Fin n → SignType) → ℤ) (K : ℕ) (r : Room n) (j : ℕ) : Prop :=
  (((range K).erase j).image (rlab lab r)).card + 1 = (range K).card ∧
    IsAlt 0 (((range K).erase j).image (rlab lab r))
instance (lab : (Fin n → SignType) → ℤ) (K : ℕ) (r : Room n) (j : ℕ) :
    Decidable (door lab K r j) := by
  unfold door; infer_instance
def doorPairs (lab : (Fin n → SignType) → ℤ) (K : ℕ) : Finset (Room n × ℕ) :=
  ((univ.filter (fun r : Room n => IsUpper K r)) ×ˢ range K).filter
    (fun p => door lab K p.1 p.2)
def NoCompLab (lab : (Fin n → SignType) → ℤ) : Prop :=
  ∀ x y : Fin n → SignType, x ≠ 0 → (∀ i, x i ≠ 0 → x i = y i) → lab x ≠ -lab y
def adjSwap (n j : ℕ) : Equiv.Perm (Fin n) :=
  if h : j + 1 < n then Equiv.swap ⟨j, by omega⟩ ⟨j + 1, h⟩ else 1
end KneserColouring


