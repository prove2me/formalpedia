-- Prove2me | solution 1 for Algebra.norm_algebraMap_eq_of_isPushout_of_isFractionRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/6bb19990-8c06-5b73-bf98-3b796aafbe92

import Mathlib
import Theorems.Thm_Algebra_norm_one_tmul_eq_algebraMap_norm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_norm_algebraMap_eq_of_isPushout_of_isFractionRing

set_option autoImplicit false

universe u

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Algebra
p2m_export "Algebra" "IsPushout algebraMap norm_eq_of_algEquiv norm algebraMapSubmonoid IsPushout.equiv IsPushout.symm IsIntegral.of_finite IsAlgebraic.isAlgebraic IsIntegral.isAlgebraic IsPushout.comp_iff IsPushout.equiv_tmul TensorProduct.rightAlgebra norm_one_tmul_eq_algebraMap_norm"
namespace NormBaseChange
p2m_open "Algebra"

theorem isLocalization_of_finite (A B L : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
    [Module.Finite A B] [Field L] [Algebra B L] [IsFractionRing B L] (h : Function.Injective (algebraMap A B)) :
    IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L := by
  haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite _ _
  haveI : Algebra.IsAlgebraic A B := Algebra.IsIntegral.isAlgebraic
  refine (IsLocalization.iff_of_le_of_exists_dvd (Algebra.algebraMapSubmonoid B (nonZeroDivisors A))
    (nonZeroDivisors B) ?_ ?_).mpr inferInstance
  · rintro _ ⟨r, hr, rfl⟩
    apply mem_nonZeroDivisors_of_ne_zero
    rw [map_ne_zero_iff _ h]
    exact nonZeroDivisors.ne_zero hr
  · intro n hn
    obtain ⟨r, hr, hdvd⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A) n).exists_nonzero_dvd hn
    exact ⟨algebraMap _ _ r, ⟨r, mem_nonZeroDivisors_of_ne_zero hr, rfl⟩, hdvd⟩

theorem isPushout_of_finite (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
    [Module.Finite A B] [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] (h : Function.Injective (algebraMap A B)) :
    Algebra.IsPushout A K B L :=
  ⟨(isLocalizedModule_iff_isBaseChange (nonZeroDivisors A) K _).mp
    (isLocalizedModule_iff_isLocalization.mpr (isLocalization_of_finite A B L h))⟩

end Algebra.NormBaseChange

open Algebra.NormBaseChange in
theorem solution
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [IsDomain A] [IsDomain B] [IsDomain A'] [IsDomain B']
    [Algebra A B] [Algebra A A'] [Algebra B B'] [Algebra A' B'] [Algebra A B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [Algebra.IsPushout A B A' B']
    [Module.Finite A B] (hAB : Function.Injective (algebraMap A B)) (hA'B' : Function.Injective (algebraMap A' B'))
    (K L K' L' : Type u) [Field K] [Field L] [Field K'] [Field L']
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra A' K'] [IsFractionRing A' K'] [Algebra B' L'] [IsFractionRing B' L']
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [Algebra K' L'] [Algebra A' L'] [IsScalarTower A' K' L'] [IsScalarTower A' B' L']
    (φ : K →+* K') (hφ : φ.comp (algebraMap A K) = (algebraMap A' K').comp (algebraMap A A'))
    (b : B) :
    φ (Algebra.norm K (algebraMap B L b)) = Algebra.norm K' (algebraMap B' L' (algebraMap B B' b)) := by
  classical

  letI algKK' : Algebra K K' := φ.toAlgebra
  letI algAK' : Algebra A K' := ((algebraMap A' K').comp (algebraMap A A')).toAlgebra
  haveI : IsScalarTower A A' K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A K K' := IsScalarTower.of_algebraMap_eq fun a => (RingHom.congr_fun hφ a).symm
  letI algBL' : Algebra B L' := ((algebraMap B' L').comp (algebraMap B B')).toAlgebra
  haveI : IsScalarTower B B' L' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI algAL' : Algebra A L' := ((algebraMap A' L').comp (algebraMap A A')).toAlgebra
  haveI : IsScalarTower A A' L' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A K' L' := IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap A' L' (algebraMap A A' a) = algebraMap K' L' (algebraMap A' K' (algebraMap A A' a))
    rw [IsScalarTower.algebraMap_apply A' K' L']
  haveI : IsScalarTower A B L' := IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap A' L' (algebraMap A A' a) = algebraMap B' L' (algebraMap B B' (algebraMap A B a))
    rw [IsScalarTower.algebraMap_apply A' B' L', ← IsScalarTower.algebraMap_apply A A' B',
      IsScalarTower.algebraMap_apply A B B']
  haveI : IsScalarTower A B' L' := IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap A' L' (algebraMap A A' a) = algebraMap B' L' (algebraMap A B' a)
    rw [IsScalarTower.algebraMap_apply A' B' L', ← IsScalarTower.algebraMap_apply A A' B']

  letI algBT : Algebra B (K' ⊗[K] L) := ((algebraMap L (K' ⊗[K] L)).comp (algebraMap B L)).toAlgebra
  haveI : IsScalarTower B L (K' ⊗[K] L) := IsScalarTower.of_algebraMap_eq fun _ => rfl

  have hAKT : ∀ a : A, algebraMap A (K' ⊗[K] L) a = algebraMap K (K' ⊗[K] L) (algebraMap A K a) := fun a => by
    rw [IsScalarTower.algebraMap_apply A K' (K' ⊗[K] L), IsScalarTower.algebraMap_apply A K K',
      ← IsScalarTower.algebraMap_apply K K' (K' ⊗[K] L)]
  haveI : IsScalarTower A K (K' ⊗[K] L) := IsScalarTower.of_algebraMap_eq hAKT
  haveI : IsScalarTower A B (K' ⊗[K] L) := IsScalarTower.of_algebraMap_eq fun a => by
    rw [hAKT, IsScalarTower.algebraMap_apply B L (K' ⊗[K] L), ← IsScalarTower.algebraMap_apply A B L,
      IsScalarTower.algebraMap_apply A K L, ← IsScalarTower.algebraMap_apply K L (K' ⊗[K] L)]
  haveI : IsScalarTower A L (K' ⊗[K] L) := IsScalarTower.of_algebraMap_eq fun a => by
    rw [hAKT, IsScalarTower.algebraMap_apply A K L, ← IsScalarTower.algebraMap_apply K L (K' ⊗[K] L)]

  haveI : Algebra.IsPushout A A' B B' := Algebra.IsPushout.symm inferInstance
  haveI : Module.Finite A' B' :=
    Module.Finite.equiv (R := A') (Algebra.IsPushout.equiv A A' B B').toLinearEquiv
  have P1 : Algebra.IsPushout A K B L := isPushout_of_finite A B K L hAB
  have P2 : Algebra.IsPushout A' K' B' L' := isPushout_of_finite A' B' K' L' hA'B'
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L := isLocalization_of_finite A B L hAB
  haveI : Module.Finite K L := Module.Finite.of_isLocalization A B (nonZeroDivisors A)
  haveI : Module.Free K L := Module.Free.of_divisionRing K L

  have big1 : Algebra.IsPushout A K' B L' := (Algebra.IsPushout.comp_iff A A' B B').mpr P2
  haveI := P1
  have big2 : Algebra.IsPushout A K' B (K' ⊗[K] L) := (Algebra.IsPushout.comp_iff A K B L).mpr inferInstance

  let e₁ : TensorProduct A K' B ≃ₐ[K'] L' := @Algebra.IsPushout.equiv A K' _ _ _ B L' _ _ _ _ _ _ _ _ big1
  let e₂ : TensorProduct A K' B ≃ₐ[K'] (K' ⊗[K] L) := @Algebra.IsPushout.equiv A K' _ _ _ B (K' ⊗[K] L) _ _ _ _ _ _ _ _ big2
  have h1 : e₁ ((1 : K') ⊗ₜ[A] b) = algebraMap B' L' (algebraMap B B' b) := by
    show Algebra.IsPushout.equiv A K' B L' ((1 : K') ⊗ₜ[A] b) = _
    rw [Algebra.IsPushout.equiv_tmul, map_one, one_mul]; rfl
  have h2 : e₂ ((1 : K') ⊗ₜ[A] b) = (1 : K') ⊗ₜ[K] algebraMap B L b := by
    show Algebra.IsPushout.equiv A K' B (K' ⊗[K] L) ((1 : K') ⊗ₜ[A] b) = _
    rw [Algebra.IsPushout.equiv_tmul, map_one, one_mul]; rfl
  calc φ (Algebra.norm K (algebraMap B L b))
      = algebraMap K K' (Algebra.norm K (algebraMap B L b)) := rfl
    _ = Algebra.norm K' ((1 : K') ⊗ₜ[K] algebraMap B L b) := (Algebra.norm_one_tmul_eq_algebraMap_norm K' _).symm
    _ = Algebra.norm K' ((e₂.symm.trans e₁) ((1 : K') ⊗ₜ[K] algebraMap B L b)) := (Algebra.norm_eq_of_algEquiv _ _).symm
    _ = Algebra.norm K' (algebraMap B' L' (algebraMap B B' b)) := by
        congr 1
        show e₁ (e₂.symm ((1 : K') ⊗ₜ[K] algebraMap B L b)) = _
        rw [← h2, AlgEquiv.symm_apply_apply, h1]

end S_Algebra_norm_algebraMap_eq_of_isPushout_of_isFractionRing
end P2MW
export P2MW.S_Algebra_norm_algebraMap_eq_of_isPushout_of_isFractionRing (solution)
