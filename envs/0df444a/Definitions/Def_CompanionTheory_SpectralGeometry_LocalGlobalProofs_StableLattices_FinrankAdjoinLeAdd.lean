-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FinrankAdjoinLeAdd
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FinrankAdjoinLeAdd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:41.112993+00:00
-- url     : https://prove2.me/theorems/c36d3265-7ce1-4e99-bd60-ffe64d633866
-- title:
--   Finrank Adjoin Le Add
-- statement:
--   Definitions and structural lemmas for Finrank Adjoin Le Add, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FinrankAdjoinLeAdd.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.CompanionTheory.CommSplit
open Module
variable {V : Type} [AddCommGroup V] [Module ℂ V]
noncomputable def compr (W W' : Submodule ℂ V) (hc : IsCompl W W') :
    End ℂ V →ₗ[ℂ] End ℂ W where
  toFun b := (W.linearProjOfIsCompl W' hc) ∘ₗ b ∘ₗ W.subtype
  map_add' b c := by ext w; simp
  map_smul' t b := by ext w; simp
end GlobalTheory.CompanionTheory.CommSplit


