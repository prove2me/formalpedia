-- Prove2me | solution 1 for AlgebraicGeometry.isIntegral_pullback_specMap_algebraMap_of_isFractionRing_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/f9a4669e-ca0a-5674-a69d-82f75b841460

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isIntegral_pullback_specMap_algebraMap_of_isFractionRing_of_flat

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace GenFibreInt

theorem isDomain_tensor_of_injective {R : Type u} [CommRing R] [IsDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Type u) [Field S] [Algebra R S] (hinj : Function.Injective (algebraMap R S)) :
    IsDomain (S ⊗[R] K) := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) (S ⊗[R] K) :=
    IsLocalization.tensor (R := R) (S := S) K (nonZeroDivisors R)
  refine IsLocalization.isDomain_of_le_nonZeroDivisors (S ⊗[R] K)
    (M := Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) ?_
  intro x hx
  obtain ⟨r, hr, rfl⟩ := Submonoid.mem_map.mp hx
  refine mem_nonZeroDivisors_of_ne_zero ?_
  intro h
  apply nonZeroDivisors.ne_zero hr
  apply hinj
  rw [map_zero]
  exact h

end GenFibreInt

open GenFibreInt

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsIntegral X] [Flat f] :
    IsIntegral (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := by
  classical

  have hfξ : (⊥ : PrimeSpectrum R) = f (genericPoint X) := by
    obtain ⟨x', -, hfx'⟩ := Flat.generalizingMap f
      (show (⊥ : PrimeSpectrum R) ⤳ f (genericPoint X) from
        (PrimeSpectrum.le_iff_specializes _ _).mp bot_le)
    have h2 : f (genericPoint X) ⤳ f x' := (genericPoint_specializes x').map f.continuous
    rw [hfx'] at h2
    exact (le_bot_iff.mp ((PrimeSpectrum.le_iff_specializes _ _).mpr h2)).symm

  set σ : Spec (X.residueField (genericPoint X)) ⟶ X := X.fromSpecResidueField (genericPoint X)
    with hσ
  let S : Type u := X.residueField (genericPoint X)
  let φ : CommRingCat.of R ⟶ X.residueField (genericPoint X) := Spec.preimage (σ ≫ f)
  letI : Algebra R S := φ.hom.toAlgebra
  have hφ' : CommRingCat.ofHom (algebraMap R S) = φ := rfl
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap R S)) = σ ≫ f := by
    rw [hφ']
    exact Spec.map_preimage _
  have hinj : Function.Injective (algebraMap R S) := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_comap_bot]
    have hpt : (σ ≫ f) default = f (genericPoint X) := by
      rw [Scheme.Hom.comp_apply, hσ, Scheme.fromSpecResidueField_apply]
    rw [← hφ, ← hfξ, Spec.map_apply] at hpt
    have := congrArg PrimeSpectrum.asIdeal hpt
    have hb : (default : ↥(Spec (X.residueField (genericPoint X)))).asIdeal = ⊥ :=
      Ideal.eq_bot_of_prime _
    rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.asIdeal_bot, CommRingCat.hom_ofHom, hb] at this
    exact this

  haveI : QuasiCompact σ := ⟨fun U _ _ => (Set.toFinite _).isCompact⟩
  haveI : IsDominant σ := ⟨by
    rw [denseRange_iff_closure_range, hσ, Scheme.range_fromSpecResidueField]
    exact genericPoint_closure X⟩
  haveI : IsSchemeTheoreticallyDominant σ := .of_isDominant σ

  haveI : Flat (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
    rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
    exact IsLocalization.flat K (nonZeroDivisors R)

  haveI : IsDomain (S ⊗[R] K) := isDomain_tensor_of_injective K S hinj
  let g := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  let q := pullback.snd σ g
  have e : pullback σ g ≅ Spec (.of (S ⊗[R] K)) :=
    pullbackRightPullbackFstIso f (Spec.map (CommRingCat.ofHom (algebraMap R K))) σ ≪≫
      pullback.congrHom hφ.symm rfl ≪≫ pullbackSpecIso R S K
  haveI : IsIntegral (pullback σ g) := IsIntegral.of_isIso e.inv
  haveI : IsSchemeTheoreticallyDominant q := inferInstance
  haveI : QuasiCompact q := inferInstance
  haveI : IsReduced (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :=
    IsSchemeTheoreticallyDominant.isReduced q
  haveI : IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := by
    have hd : DenseRange q := q.denseRange
    have h1 : IsIrreducible (Set.range (fun x => q x)) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _ q.continuous.continuousOn
    have h2 := h1.closure
    rw [hd.closure_range] at h2
    exact (irreducibleSpace_def _).mpr h2
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end S_AlgebraicGeometry_isIntegral_pullback_specMap_algebraMap_of_isFractionRing_of_flat
end P2MW
export P2MW.S_AlgebraicGeometry_isIntegral_pullback_specMap_algebraMap_of_isFractionRing_of_flat (solution)
