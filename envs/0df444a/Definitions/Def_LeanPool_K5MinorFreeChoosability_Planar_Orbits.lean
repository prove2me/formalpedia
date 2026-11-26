-- Prove2me | Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
-- name    : LeanPool_K5MinorFreeChoosability_Planar_Orbits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:09:59.74516+00:00
-- url     : https://prove2.me/theorems/35c454e9-cc38-408e-ad89-46c482c5b7b1
-- title:
--   Orbits
-- statement:
--   Definitions and structural lemmas for Orbits, from Juan Pablo Traverso Gianini (jtraverso/alon-tarsi-choosability; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Alon-Tarsi theorem and 3-choosability of planar bipartite graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}
noncomputable def numClasses (s : Setoid α) : ℕ := Nat.card (Quotient s)
def addPairSetoid (s : Setoid α) (x y : α) : Setoid α where
  r a b := s a b ∨ (s a x ∧ s y b) ∨ (s a y ∧ s x b)
  iseqv := by
    refine ⟨fun a => Or.inl (s.refl a), ?_, ?_⟩
    · rintro a b (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl (s.symm h)
      · exact Or.inr (Or.inr ⟨s.symm h2, s.symm h1⟩)
      · exact Or.inr (Or.inl ⟨s.symm h2, s.symm h1⟩)
    · rintro a b c (h | ⟨h1, h2⟩ | ⟨h1, h2⟩) (k | ⟨k1, k2⟩ | ⟨k1, k2⟩)
      · exact Or.inl (s.trans h k)
      · exact Or.inr (Or.inl ⟨s.trans h k1, k2⟩)
      · exact Or.inr (Or.inr ⟨s.trans h k1, k2⟩)
      · exact Or.inr (Or.inl ⟨h1, s.trans h2 k⟩)
      · exact Or.inr (Or.inl ⟨h1, k2⟩)
      · exact Or.inl (s.trans h1 k2)
      · exact Or.inr (Or.inr ⟨h1, s.trans h2 k⟩)
      · exact Or.inl (s.trans h1 k2)
      · exact Or.inr (Or.inr ⟨h1, k2⟩)
noncomputable def cycleCount (π : Perm α) : ℕ := numClasses (SameCycle.setoid π)
variable [DecidableEq α]
def removeFromCycle (π : Perm α) (z : α) : Perm α := π * swap (π⁻¹ z) z
end LeanPool.K5MinorFreeChoosability


