-- Prove2me | Definitions.Def_DeletionCode_CanonicalIndex
-- name    : DeletionCode_CanonicalIndex
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:17:15.108882+00:00
-- url     : https://prove2.me/theorems/a1173a29-c0a4-4656-bc8e-4096c5ded04b
-- title:
--   Canonical Index
-- statement:
--   Definitions and structural lemmas for Canonical Index, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CanonicalIndex.lean

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_RuleReconstruction
import Mathlib.Logic.Equiv.Fin.Basic
set_option autoImplicit true
namespace DeletionCode.CanonicalIndex
open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport RuleReconstruction
open scoped BigOperators
def indexEquiv (t R : ℕ) : Fin (2 * t * R) ≃ Fin R × Fin (2 * t) :=
  (Equiv.cast (congrArg Fin (Nat.mul_comm (2 * t) R))).trans
    (@finProdFinEquiv R (2 * t)).symm
def group (t R : ℕ) (b : Fin (2 * t * R)) : Fin R := (indexEquiv t R b).1
def flatten {α : Type*} (t R : ℕ) (words : Fin R → Fin (2 * t) → α) :
    Fin (2 * t * R) → α :=
  fun b => words (indexEquiv t R b).1 (indexEquiv t R b).2
def unflatten {α : Type*} (t R : ℕ) (family : Fin (2 * t * R) → α) :
    Fin R → Fin (2 * t) → α :=
  fun r j => family ((indexEquiv t R).symm (r, j))
theorem flatten_at_pair {α : Type*} (t R : ℕ) (words : Fin R → Fin (2 * t) → α)
    (r : Fin R) (j : Fin (2 * t)) :
    flatten t R words ((indexEquiv t R).symm (r, j)) = words r j := by
  simp [flatten]
theorem unflatten_flatten {α : Type*} (t R : ℕ) (words : Fin R → Fin (2 * t) → α) :
    unflatten t R (flatten t R words) = words := by
  funext r j
  exact flatten_at_pair t R words r j
theorem flatten_unflatten {α : Type*} (t R : ℕ) (family : Fin (2 * t * R) → α) :
    flatten t R (unflatten t R family) = family := by
  funext b
  simp [flatten, unflatten]
def familyEquiv (α : Type*) (t R : ℕ) :
    (Fin (2 * t * R) → α) ≃ (Fin R → Fin (2 * t) → α) where
  toFun := unflatten t R
  invFun := flatten t R
  left_inv := flatten_unflatten t R
  right_inv := unflatten_flatten t R
def groupFiberEquiv (t R : ℕ) (r : Fin R) :
    {b : Fin (2 * t * R) // group t R b = r} ≃ Fin (2 * t) where
  toFun b := (indexEquiv t R b.val).2
  invFun j := ⟨(indexEquiv t R).symm (r, j), by simp [group]⟩
  left_inv b := by
    apply Subtype.ext
    apply (indexEquiv t R).injective
    simp only [Equiv.apply_symm_apply]
    exact Prod.ext b.property.symm rfl
  right_inv j := by simp
def pairFamily {k : ℕ} (t R : ℕ) (words : Fin R → Fin (2 * t) → BubbleWord k) :
    EditedFamily (Fin R × Fin (2 * t)) k :=
  editedFamily (fun p => words p.1 p.2) (fun p => p.1.val)
def flatFamily {k : ℕ} (t R : ℕ) (words : Fin R → Fin (2 * t) → BubbleWord k) :
    EditedFamily (Fin (2 * t * R)) k :=
  editedFamily (flatten t R words) (fun b => (group t R b).val)
end DeletionCode.CanonicalIndex


