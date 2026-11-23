-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FrameOfAnisotropicPlaneSplitting
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FrameOfAnisotropicPlaneSplitting
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:34.697525+00:00
-- url     : https://prove2.me/theorems/89db5443-ea90-41a3-8042-09f02ee9f49b
-- title:
--   Frame Of Anisotropic Plane Splitting
-- statement:
--   Definitions and structural lemmas for Frame Of Anisotropic Plane Splitting, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FrameOfAnisotropicPlaneSplitting.lean

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
namespace GlobalTheory.CompanionTheory.HermFrame
section Steps
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}
theorem herm_right_zero (hh : IsHerm s h) (x : V) : h x 0 = 0 := by
  have := hh.2.1 (0 : L) x 0
  simpa using this
def orthPair (hh : IsHerm s h) (e f : V) : Submodule L V where
  carrier := {x | h e x = 0 ∧ h f x = 0}
  add_mem' := by
    intro a b ha hb
    exact ⟨by rw [hh.1, ha.1, hb.1, add_zero], by rw [hh.1, ha.2, hb.2, add_zero]⟩
  zero_mem' := ⟨herm_right_zero hh e, herm_right_zero hh f⟩
  smul_mem' := by
    intro c x hx
    exact ⟨by rw [hh.2.1, hx.1, mul_zero], by rw [hh.2.1, hx.2, mul_zero]⟩
end Steps
end GlobalTheory.CompanionTheory.HermFrame
end


