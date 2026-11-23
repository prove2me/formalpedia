-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:43.89044+00:00
-- url     : https://prove2.me/theorems/a25592c4-86ac-4186-ba18-f7c014bf2240
-- title:
--   Alternating Map Sum Smul Eq Det Smul
-- statement:
--   Definitions and structural lemmas for Alternating Map Sum Smul Eq Det Smul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AlternatingMapSumSmulEqDetSmul.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
open scoped BigOperators
section JetWedge
variable {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  {D : ℕ}
noncomputable def jetWedge (ω : M [⋀^Fin D]→ₗ[A] N) : (A × M) [⋀^Fin (D + 1)]→ₗ[A] N :=
  AlternatingMap.alternatizeUncurryFin
    ((LinearMap.fst A A M).smulRight (ω.compLinearMap (LinearMap.snd A A M)))
end JetWedge
section JacForm
variable {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module A M] [Module R M] [AddCommGroup N] [Module A N] {D : ℕ}
noncomputable def jacForm (d : Derivation R A M) (ω : M [⋀^Fin D]→ₗ[A] N)
    (f : Fin (D + 1) → A) : N :=
  ∑ i : Fin (D + 1), ((-1 : A) ^ (i : ℕ) * f i) • ω (fun k => d (f (i.succAbove k)))
variable (d : Derivation R A M) (ω : M [⋀^Fin D]→ₗ[A] N)
variable [Module R N] [IsScalarTower R A N] [IsScalarTower R A M]
noncomputable def jacobianMultilinearTo : A [⋀^Fin (D + 1)]→ₗ[R] N where
  toMultilinearMap := ((jetWedge ω).toMultilinearMap.restrictScalars R).compLinearMap
    (fun _ => (LinearMap.id : A →ₗ[R] A).prod (d : A →ₗ[R] M))
  map_eq_zero_of_eq' v i j hv hij :=
    (jetWedge ω).map_eq_zero_of_eq (fun i => (v i, d (v i))) (by simp only [hv]) hij
end JacForm
section RestrictScalars
variable (A : Type*) {B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
  [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] {D : ℕ}
def altRestrictScalars (ω : M [⋀^Fin D]→ₗ[B] N) : M [⋀^Fin D]→ₗ[A] N where
  toMultilinearMap := ω.toMultilinearMap.restrictScalars A
  map_eq_zero_of_eq' v _ _ hv hij := ω.map_eq_zero_of_eq v hv hij
variable {A} {L : Type*} [AddCommGroup L] [Module A L]
variable (B D) in

noncomputable def exteriorPowerMapOver (φ : L →ₗ[A] M) : (⋀[A]^D L) →ₗ[A] (⋀[B]^D M) :=
  exteriorPower.alternatingMapLinearEquiv
    ((altRestrictScalars A (exteriorPower.ιMulti B D (M := M))).compLinearMap φ)
noncomputable def wedgeContract (φ : Fin D → L →ₗ[A] B) : (⋀[A]^D L) →ₗ[A] B :=
  exteriorPower.alternatingMapLinearEquiv
    ((altRestrictScalars A (Matrix.detRowAlternating : (Fin D → B) [⋀^Fin D]→ₗ[B] B)).compLinearMap
      (LinearMap.pi φ))
end RestrictScalars
section Jac
variable (R : Type*) {A : Type*} [CommRing R] [CommRing A] [Algebra R A] {D : ℕ}
open KaehlerDifferential
noncomputable def dWedge (g : Fin D → A) : ⋀[A]^D Ω[A⁄R] :=
  exteriorPower.ιMulti A D (fun k => KaehlerDifferential.D R A (g k))
noncomputable def jac (f : Fin (D + 1) → A) : ⋀[A]^D Ω[A⁄R] :=
  ∑ i : Fin (D + 1), ((-1 : A) ^ (i : ℕ) * f i) • dWedge R (fun k => f (i.succAbove k))
variable (A D) in

noncomputable def jacobianMultilinear : A [⋀^Fin (D + 1)]→ₗ[R] (⋀[A]^D Ω[A⁄R]) :=
  jacobianMultilinearTo (KaehlerDifferential.D R A) (exteriorPower.ιMulti A D)
variable {R}
variable (R A D)
end Jac
end GlobalTheory


