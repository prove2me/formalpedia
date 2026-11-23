-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorusStatement
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorusStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:06.97627+00:00
-- url     : https://prove2.me/theorems/77e1a007-6f17-4136-b9a1-9290ef768935
-- title:
--   Torus Statement
-- statement:
--   Definitions and structural lemmas for Torus Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TorusStatement.lean

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
namespace GlobalTheory.CompanionTheory.FrameTorus
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
def gens {l : ℕ} (e f : Fin l → V) (W : Submodule L V) : Set V :=
  Set.range e ∪ Set.range f ∪ (W : Set V)
def pair {s : L →+* L} {h : V → V → L} (hH : IsHerm s h) (x : V) : V →ₗ[L] L where
  toFun := h x
  map_add' := hH.1 x
  map_smul' a y := by simp [hH.2.1]
def tor {s : L →+* L} {h : V → V → L} (hH : IsHerm s h) (δ : L) {l : ℕ} (e f : Fin l → V)
    (u : Fin l → L) : V →ₗ[L] V :=
  LinearMap.id + (∑ i, ((u i - 1) * (s δ)⁻¹) • (pair hH (f i)).smulRight (e i)) +
    ∑ i, (((s (u i))⁻¹ - 1) * δ⁻¹) • (pair hH (e i)).smulRight (f i)
section Frame
variable {s : L →+* L} {h : V → V → L} {δ : L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}
end Frame
end GlobalTheory.CompanionTheory.FrameTorus
end


