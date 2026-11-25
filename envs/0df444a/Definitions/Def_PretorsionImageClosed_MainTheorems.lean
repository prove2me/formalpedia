-- Prove2me | Definitions.Def_PretorsionImageClosed_MainTheorems
-- name    : PretorsionImageClosed_MainTheorems
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T06:46:28.01289+00:00
-- url     : https://prove2.me/theorems/a262167d-8362-428d-8500-acac7ed33fdd
-- title:
--   Main Theorems
-- statement:
--   Definitions and structural lemmas for Main Theorems, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/MainTheorems.lean

module
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Definitions.Def_PretorsionImageClosed_Length_Modules
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffRestriction
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction
public import Theorems.Thm_PretorsionImageClosed_isArtinianRing_mop

set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed
open CategoryTheory Limits Statement
universe u
def modHasLength (k : Type u) [Field k] (Λ : Type u) [Ring Λ] [Algebra k Λ]
    [FiniteDimensional k Λ] :
    haveI := isNoetherianRing_mop k Λ
    HasLength (Mod k Λ) :=
  haveI := isNoetherianRing_mop k Λ
  haveI := isArtinianRing_mop k Λ
  inferInstance
end PretorsionImageClosed


