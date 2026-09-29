-- Prove2me | solution 1 for AlgebraicGeometry.isIso_stalkMap_pullback_fst_and_ringKrullDim_stalk_le_of_isFractionRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6220e5f3-99a7-55d4-a6d0-53bc4825a95d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isIso_stalkMap_pullback_fst_and_ringKrullDim_stalk_le_of_isFractionRing

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) :
    (∀ y : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
        IsIso ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).stalkMap y)) ∧
    ∀ (n : ℕ),
      (∀ y : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
          ringKrullDim ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).presheaf.stalk y) ≤ n) →
      ∀ x : X, (f.base x).asIdeal = ⊥ → ringKrullDim (X.presheaf.stalk x) ≤ n := by
  haveI hpre : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  haveI : IsPreimmersion (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  haveI hflat : Flat (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).mpr
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R)))
  haveI : Flat (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have hiso : ∀ y : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      IsIso ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).stalkMap y) := by
    intro y
    set φ := (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).stalkMap y with hφ
    have hsurj : Function.Surjective φ.hom :=
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).stalkMap_surjective y
    have hinj : Function.Injective φ.hom := by
      have hfl : φ.hom.Flat := Flat.stalkMap _ y
      let A : Type u := ↑(X.presheaf.stalk ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).base y))
      let B : Type u := ↑((pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).presheaf.stalk y)
      have hloc : IsLocalHom φ.hom := inferInstance
      letI : Algebra A B := φ.hom.toAlgebra
      haveI : Module.Flat A B := hfl
      haveI : IsLocalHom (algebraMap A B) := hloc
      have hff : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
      have hinj' : Function.Injective (algebraMap A B) := (RingHom.faithfullyFlat_algebraMap_iff.mpr hff).injective
      exact hinj'
    haveI : IsIso ((forget CommRingCat).map φ) := (isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
    exact isIso_of_reflects_iso φ (forget CommRingCat)
  refine ⟨hiso, fun n hn x hx => ?_⟩

  let pt : ↥(Spec (CommRingCat.of K)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  have hpt : f.base x = (Spec.map (CommRingCat.ofHom (algebraMap R K))).base pt := by
    apply PrimeSpectrum.ext
    rw [hx]
    change (⊥ : Ideal R) = Ideal.comap (algebraMap R K) (⊥ : Ideal K)
    exact (Ideal.comap_bot_of_injective (algebraMap R K) (IsFractionRing.injective R K)).symm
  obtain ⟨y, hy, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f)
    (g := Spec.map (CommRingCat.ofHom (algebraMap R K))) x pt hpt
  haveI := hiso y
  let e : ↑(X.presheaf.stalk ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).base y)) ≃+*
      ↑((pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).presheaf.stalk y) :=
    (asIso ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).stalkMap y)).commRingCatIsoToRingEquiv
  have hxy : ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).base y) = x := hy
  rw [← hxy, ringKrullDim_eq_of_ringEquiv e]
  exact hn y

end S_AlgebraicGeometry_isIso_stalkMap_pullback_fst_and_ringKrullDim_stalk_le_of_isFractionRing
end P2MW
export P2MW.S_AlgebraicGeometry_isIso_stalkMap_pullback_fst_and_ringKrullDim_stalk_le_of_isFractionRing (solution)
