-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:14.222082+00:00
-- url     : https://prove2.me/theorems/0263f3b9-e2c5-45e3-93f3-5fb63b32090a
-- title:
--   Exists Alg Hom Of Is Base Change
-- statement:
--   Definitions and structural lemmas for Exists Alg Hom Of Is Base Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsAlgHomOfIsBaseChange.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
namespace GlobalTheory
namespace TopForm
section BaseChange
variable {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
def extProj (A M : Type*) [CommRing A] [AddCommGroup M] [Module A M] (D : ℕ) :
    ExteriorAlgebra A M →ₗ[A] ⋀[A]^D M :=
  (DirectSum.component A ℕ (fun i => ⋀[A]^i M) D).comp
    (DirectSum.decomposeLinearEquiv (fun i => ⋀[A]^i M)).toLinearMap
def IsFreeGen (A : Type*) {M : Type*} [CommRing A] [AddCommGroup M] [Module A M] (ω : M) : Prop :=
  Function.Bijective fun a : A => a • ω
end BaseChange
section FreeGen
variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] {ω : M}
def IsFreeGen.repr (h : IsFreeGen A ω) : M ≃ₗ[A] A :=
  (LinearEquiv.ofBijective (LinearMap.toSpanSingleton A M ω) h).symm
end FreeGen
section Ring
variable {k A B C : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing C]
abbrev Omega (α : k →+* A) : Type _ := letI := α.toAlgebra; Ω[A⁄k]
abbrev Forms (α : k →+* A) (D : ℕ) : Type _ := ⋀[A]^D (Omega α)
abbrev dFun (α : k →+* A) (f : A) : Omega α := letI := α.toAlgebra; KaehlerDifferential.D k A f
variable {D : ℕ}
def dForm (α : k →+* A) (f : Fin D → A) : Forms α D := letI := α.toAlgebra; dWedge k f
variable {α : k →+* A} {β : k →+* B} {γ : k →+* C}
variable (D) in

def formMap (ρ : A →+* B) (h : ρ.comp α = β) : Forms α D →ₛₗ[ρ] Forms β D :=
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' h.symm
  { toFun := exteriorPowerMapOver B D (KaehlerDifferential.map k k A B)
    map_add' := map_add _
    map_smul' := fun a x => by
      rw [map_smul, ← algebraMap_smul B]
      rfl }
end Ring
end TopForm
end GlobalTheory


