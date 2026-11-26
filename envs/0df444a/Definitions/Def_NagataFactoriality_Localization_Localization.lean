-- Prove2me | Definitions.Def_NagataFactoriality_Localization_Localization
-- name    : NagataFactoriality_Localization_Localization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T05:50:39.462593+00:00
-- url     : https://prove2.me/theorems/f26b10e2-c15b-4e41-9cee-6ff44827491c
-- title:
--   Localization
-- statement:
--   Definitions and structural lemmas for Localization, from Arthur Freitas Ramos, David Barros Hulak, and Ruy J. G. B. de Queiroz (Arthur742Ramos/NagataFactoriality; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Prime-generated Nagata factoriality theorem for Noetherian integral domains development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Theorems.Thm_NagataFactoriality_Submonoid_le_nonZeroDivisors

set_option autoImplicit false
namespace NagataFactoriality
abbrev Localization {α : Type*} [CommRing α] (S : Submonoid α) := _root_.Localization S
namespace Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}
def mk (a s : α) (hs : s ∈ S) : Localization S :=
  _root_.Localization.mk a ⟨s, hs⟩
def of (a : α) : Localization S :=
  algebraMap α (Localization S) a
section Nonzero
variable [IsDomain α] [Fact ((0 : α) ∉ S)]
instance : IsDomain (Localization S) :=
  IsLocalization.isDomain_localization (M := S) (Submonoid.le_nonZeroDivisors (S := S))
end Nonzero
section Nonzero
variable [IsDomain α] [Fact ((0 : α) ∉ S)]
end Nonzero
end Localization
end NagataFactoriality


