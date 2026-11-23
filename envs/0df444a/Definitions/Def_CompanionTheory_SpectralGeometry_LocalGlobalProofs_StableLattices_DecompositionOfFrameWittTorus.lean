-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfFrameWittTorus
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfFrameWittTorus
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:49.42086+00:00
-- url     : https://prove2.me/theorems/3a5fceb8-7f1d-4b84-9045-a63fc2a94777
-- title:
--   Decomposition Of Frame Witt Torus
-- statement:
--   Definitions and structural lemmas for Decomposition Of Frame Witt Torus, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean

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
noncomputable section
namespace GlobalTheory.CompanionTheory.FlDecomp
open CompanionTheory.Rg.FlB
section SlopeTestRemainingChoices
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
def pull (k : V ≃ₗ[L] V) (Λ : AddSubgroup V) : AddSubgroup V := Λ.comap k.toLinearMap.toAddMonoidHom
end SlopeTestRemainingChoices
section Lem
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
variable {s : L →+* L} {δ : L} {h : V → V → L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}
def hl (hh : IsHerm s h) (x : V) : V →ₗ[L] L where
  toFun := h x
  map_add' := hh.1 x
  map_smul' a y := by simpa using hh.2.1 a x y
def permMap (hh : IsHerm s h) (δ : L) (e f : Fin l → V) (τ : Equiv.Perm (Fin l)) : V →ₗ[L] V :=
  LinearMap.id + ∑ i, (((s δ)⁻¹ • hl hh (f i)).smulRight (e (τ i) - e i) +
    (δ⁻¹ • hl hh (e i)).smulRight (f (τ i) - f i))
end Lem
end GlobalTheory.CompanionTheory.FlDecomp
end


