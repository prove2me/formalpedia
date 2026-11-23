-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdEApply
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdEApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:58.145653+00:00
-- url     : https://prove2.me/theorems/c3edd764-ea46-4d2d-a33e-3618c220f62f
-- title:
--   Ad EApply
-- statement:
--   Definitions and structural lemmas for Ad EApply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdEApply.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.StableLatCount
def adE (E : Type) [Field E] {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂]
    (g₁ : A₁) (g₂ : A₂) : (A₂ →ₗ[E] A₁) →ₗ[E] (A₂ →ₗ[E] A₁) :=
  LinearMap.llcomp E A₂ A₁ A₁ (LinearMap.mulLeft E g₁) - LinearMap.lcomp E A₁ (LinearMap.mulLeft E g₂)
def homLat (E : Type) [Field E] {O A₁ A₂ : Type} [CommRing O] [Algebra O E] [CommRing A₁] [CommRing A₂]
    [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁]
    (M₁ : Submodule O A₁) (M₂ : Submodule O A₂) : Submodule O (A₂ →ₗ[E] A₁) where
  carrier := {ψ | ∀ x ∈ M₂, ψ x ∈ M₁}
  add_mem' := fun ha hb x hx => by simpa using M₁.add_mem (ha x hx) (hb x hx)
  zero_mem' := fun x _ => by simp
  smul_mem' := fun c ψ hψ x hx => by simpa using M₁.smul_mem c (hψ x hx)
end GlobalTheory.StableLatCount


