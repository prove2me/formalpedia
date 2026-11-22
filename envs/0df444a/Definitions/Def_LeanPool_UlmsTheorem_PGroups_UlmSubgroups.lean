-- Prove2me | Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmSubgroups
-- name    : LeanPool_UlmsTheorem_PGroups_UlmSubgroups
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:53:14.556929+00:00
-- url     : https://prove2.me/theorems/e50a6a6d-6257-4566-a490-909c511b9abe
-- title:
--   Ulm Subgroups
-- statement:
--   Definitions and structural lemmas for Ulm Subgroups, from Elan Roth; LeanPool contributors's pinned Ulm’s theorem for abelian p-groups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmSubgroups.lean

module
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Algebra.Group.Subgroup.Map
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Subgroups
public import Mathlib.Algebra.Module.NatInt
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace UlmsTheorem
open Ordinal
variable (p : ℕ)
noncomputable def ulmSubgroup {G : Type*} [AddCommGroup G] (α : Ordinal) :
    AddSubgroup G :=
  α.limitRecOn
    ⊤
    (fun _β Hβ ↦ pImage p Hβ)
    (fun o _ho IH ↦ ⨅ (β : Ordinal) (_ : β < o), IH β ‹_›)
section UlmSubgroupLemmas
variable {G : Type*} [AddCommGroup G]
end UlmSubgroupLemmas
end UlmsTheorem


