-- Prove2me | Definitions.Def_LeanPool_UlmsTheorem_PGroups_Subgroups
-- name    : LeanPool_UlmsTheorem_PGroups_Subgroups
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:52:57.628019+00:00
-- url     : https://prove2.me/theorems/f6fb4ca7-7783-418c-b5d2-52a674c964af
-- title:
--   Subgroups
-- statement:
--   Definitions and structural lemmas for Subgroups, from Elan Roth; LeanPool contributors's pinned Ulm’s theorem for abelian p-groups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Subgroups.lean

module
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Module.NatInt
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace UlmsTheorem
variable (p : ℕ)
def pPow {G : Type*} [AddCommGroup G] (n : ℕ) : AddSubgroup G where
  carrier   := {x | ∃ y : G, p ^ n • y = x}
  zero_mem' := ⟨0, by simp⟩
  add_mem'  := by
    rintro a b ⟨ya, rfl⟩ ⟨yb, rfl⟩
    exact ⟨ya + yb, smul_add (p ^ n) ya yb⟩
  neg_mem'  := by
    rintro a ⟨y, rfl⟩
    exact ⟨-y, smul_neg (p ^ n) y⟩
section PowLemmas
variable {G : Type*} [AddCommGroup G]
@[simp] lemma pPow_mem_iff (x : G) (n : ℕ) :
    x ∈ pPow p n ↔ ∃ y : G, p ^ n • y = x := Iff.rfl
end PowLemmas
def pImage {G : Type*} [AddCommGroup G] (H : AddSubgroup G) : AddSubgroup G where
  carrier   := {x | ∃ y ∈ H, p • y = x}
  zero_mem' := ⟨0, H.zero_mem, by simp⟩
  add_mem'  := by
    rintro a b ⟨ya, hya, rfl⟩ ⟨yb, hyb, rfl⟩
    exact ⟨ya + yb, H.add_mem hya hyb, smul_add p ya yb⟩
  neg_mem'  := by
    rintro a ⟨y, hy, rfl⟩
    exact ⟨-y, H.neg_mem hy, smul_neg p y⟩
section PImageLemmas
variable {G : Type*} [AddCommGroup G]
end PImageLemmas
end UlmsTheorem


