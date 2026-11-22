-- Prove2me | Definitions.Def_LeanPool_UlmsTheorem_PGroups_Socle
-- name    : LeanPool_UlmsTheorem_PGroups_Socle
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:54:57.454167+00:00
-- url     : https://prove2.me/theorems/8300b9cb-b2b2-48a4-88e2-3d520e571322
-- title:
--   Socle
-- statement:
--   Definitions and structural lemmas for Socle, from Elan Roth; LeanPool contributors's pinned Ulm’s theorem for abelian p-groups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Socle.lean

module
public import Mathlib.Algebra.Module.ZMod
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmSubgroups
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
attribute [local simp] UlmsTheorem.mem_pImage
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff
attribute [local simp] UlmsTheorem.ulmSubgroup_zero


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace UlmsTheorem
open Ordinal
variable (p : ℕ)
def pSocle {G : Type*} [AddCommGroup G] : AddSubgroup G where
  carrier   := {x | p • x = 0}
  zero_mem' := by simp
  add_mem'  := by
    rintro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [smul_add, ha, hb, add_zero]
  neg_mem'  := by
    rintro a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [smul_neg, ha, neg_zero]
section SocleLemmas
variable {G : Type*} [AddCommGroup G]
@[simp] lemma mem_pSocle (x : G) : x ∈ pSocle p (G := G) ↔ p • x = 0 := Iff.rfl
noncomputable def pSocleAt (α : Ordinal) : AddSubgroup G :=
  pSocle p ⊓ ulmSubgroup p α
@[simp] lemma mem_pSocleAt (α : Ordinal) (x : G) :
    x ∈ pSocleAt p α (G := G) ↔ p • x = 0 ∧ x ∈ ulmSubgroup p α := Iff.rfl
noncomputable instance pSocleZModModule :
    Module (ZMod p) (pSocle p (G := G)) := by
  classical
  refine AddCommGroup.zmodModule (n := p) (G := pSocle p (G := G)) ?_
  intro x
  apply Subtype.ext
  exact x.property
noncomputable instance pSocleAtZModModule (α : Ordinal) :
    Module (ZMod p) (pSocleAt p α (G := G)) := by
  classical
  refine AddCommGroup.zmodModule (n := p) (G := pSocleAt p α (G := G)) ?_
  intro x
  have hx : p • (x : G) = 0 := (mem_pSocleAt p α (x : G)).1 x.property |>.1
  ext
  simp [hx]
noncomputable def pSocleAtSuccSubgroupOf (α : Ordinal) :
    AddSubgroup (pSocleAt p α (G := G)) :=
  (pSocleAt p (Order.succ α) (G := G)).comap
    (AddSubgroup.subtype (pSocleAt p α))
noncomputable instance pSocleAtQuotModule (α : Ordinal) :
    Module (ZMod p) ((pSocleAt p α (G := G)) ⧸ pSocleAtSuccSubgroupOf p α) := by
  classical
  refine QuotientAddGroup.zmodModule (n := p)
    (G := pSocleAt p α (G := G)) (H := pSocleAtSuccSubgroupOf p α) ?_
  intro x
  have hx' : p • (x : G) = 0 := (mem_pSocleAt p α (x : G)).1 x.property |>.1
  have hx : p • x = 0 := by
    ext
    simp [hx']
  simp [hx]
end SocleLemmas
end UlmsTheorem


