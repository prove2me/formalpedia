-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.schemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/ccc653aa-4625-5706-a425-3e9ecd74bc06

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_schemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

namespace RigidityGeomPoints

universe u

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K] [IsAlgClosed K] [Algebra R K]

local notation "bK" => Spec.map (CommRingCat.ofHom (algebraMap R K))

theorem range_specMap_eq (hinj : Function.Injective (algebraMap R K)) :
    Set.range (bK).base = {(⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum R)} := by
  ext p
  simp only [Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨q, rfl⟩
    rw [Spec.map_base]
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R K) q.asIdeal = ⊥
    have hq : q.asIdeal = ⊥ := by
      haveI := q.isPrime
      exact Ideal.eq_bot_of_prime q.asIdeal
    rw [hq, Ideal.comap_bot_of_injective _ hinj]
  · rintro rfl
    refine ⟨⟨⊥, Ideal.bot_prime⟩, ?_⟩
    rw [Spec.map_base]
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R K) ⊥ = ⊥
    exact Ideal.comap_bot_of_injective _ hinj

theorem dense_preimage_genericPoint {D : Scheme.{u}} (t : D ⟶ Spec (CommRingCat.of R)) [Flat t] :
    Dense (t.base ⁻¹' {(⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum R)}) := by
  intro p

  have hgen : (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum R) ⤳ t.base p := by
    rw [← PrimeSpectrum.le_iff_specializes]
    exact bot_le
  obtain ⟨q, hq, htq⟩ := Flat.generalizingMap t hgen

  have hqmem : q ∈ t.base ⁻¹' {(⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum R)} := htq
  apply closure_mono (Set.singleton_subset_iff.mpr hqmem)
  exact hq.mem_closure

theorem dense_range_of_points (hinj : Function.Injective (algebraMap R K))
    {D : Scheme.{u}} (t : D ⟶ Spec (CommRingCat.of R)) [Flat t] [LocallyOfFiniteType t] :
    Dense (⋃ x : {x : Spec (CommRingCat.of K) ⟶ D // x ≫ t = bK},
      Set.range x.1.base) := by

  let P := pullback t bK
  haveI : LocallyOfFiniteType (pullback.snd t bK) := inferInstance
  haveI : JacobsonSpace P := LocallyOfFiniteType.jacobsonSpace (pullback.snd t bK)

  have hsub : (pullback.fst t bK).base '' closedPoints P ⊆
      ⋃ x : {x : Spec (CommRingCat.of K) ⟶ D // x ≫ t = bK}, Set.range x.1.base := by
    rintro _ ⟨p, hp, rfl⟩
    let y := (pointEquivClosedPoint (pullback.snd t bK)).symm ⟨p, hp⟩
    have hy : y.1 ≫ pullback.fst t bK ≫ t = bK := by
      rw [pullback.condition, ← Category.assoc, y.2, Category.id_comp]
    refine Set.mem_iUnion.mpr ⟨⟨y.1 ≫ pullback.fst t bK, by rw [Category.assoc]; exact hy⟩,
      ⟨IsLocalRing.closedPoint K, ?_⟩⟩
    change (pullback.fst t bK).base (y.1.base (IsLocalRing.closedPoint K)) = _
    congr 1
    have := pointEquivClosedPoint_symm_apply_coe (pullback.snd t bK) ⟨p, hp⟩
    change y.1 = _ at this
    rw [this, pointOfClosedPoint_apply]

  have hdenseP : Dense (closedPoints P) := by
    rw [dense_iff_closure_eq]
    have := JacobsonSpace.closure_inter_closedPoints_eq_closure (X := P) isOpen_univ.isLocallyClosed
    rw [Set.univ_inter, closure_univ] at this
    exact this
  have hrange : Set.range (pullback.fst t bK).base = t.base ⁻¹' {(⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum R)} := by
    rw [Scheme.Pullback.range_fst, range_specMap_eq hinj]

  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro d
  have h1 : d ∈ closure (t.base ⁻¹' {(⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum R)}) :=
    dense_preimage_genericPoint t d
  have h2 : t.base ⁻¹' {(⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum R)} ⊆
      closure ((pullback.fst t bK).base '' closedPoints P) := by
    rw [← hrange]
    rintro _ ⟨p, rfl⟩
    have : p ∈ closure (closedPoints P) := hdenseP p
    exact (map_mem_closure (pullback.fst t bK).base.hom.continuous this fun q hq => ⟨q, hq, rfl⟩)
  have h3 := closure_mono h2
  rw [closure_closure] at h3
  exact closure_mono hsub (h3 h1)

theorem ext_of_forall_geometric_point (hinj : Function.Injective (algebraMap R K))
    {D : Scheme.{u}} (t : D ⟶ Spec (CommRingCat.of R))
    [Flat t] [LocallyOfFiniteType t] [IsSeparated t] [IsReduced D]
    (φ ψ : D ⟶ D) (hφ : φ ≫ t = t) (hψ : ψ ≫ t = t)
    (h : ∀ x : Spec (CommRingCat.of K) ⟶ D, x ≫ t = bK → x ≫ φ = x ≫ ψ) : φ = ψ := by
  let I := {x : Spec (CommRingCat.of K) ⟶ D // x ≫ t = bK}
  let W : Scheme.{u} := ∐ fun _ : I => Spec (CommRingCat.of K)
  let ι : W ⟶ D := Sigma.desc fun x : I => x.1
  haveI : IsDominant ι := by
    rw [isDominant_iff]
    have hd := dense_range_of_points (K := K) hinj t
    refine Dense.mono ?_ hd
    intro d hd'
    obtain ⟨x, ⟨p, rfl⟩⟩ := Set.mem_iUnion.mp hd'
    refine ⟨(Sigma.ι (fun _ : I => Spec (CommRingCat.of K)) x).base p, ?_⟩
    change (Sigma.ι (fun _ : I => Spec (CommRingCat.of K)) x ≫ ι).base p = _
    rw [Sigma.ι_desc]
  refine ext_of_isDominant_of_isSeparated t (hφ.trans hψ.symm) ι ?_
  apply Sigma.hom_ext
  intro x
  rw [← Category.assoc, ← Category.assoc, Sigma.ι_desc]
  exact h x.1 x.2

end RigidityGeomPoints

section RIGAssembly
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian

theorem RigidityGeomPoints.algebraMap_ratLocalizedAt_injective (ℓ : ℕ) :
    Function.Injective (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)) := by
  rw [IsScalarTower.algebraMap_eq ↥(GaloisRep.ratLocalizedAt ℓ) ℚ (AlgebraicClosure ℚ)]
  exact (algebraMap ℚ (AlgebraicClosure ℚ)).injective.comp Subtype.val_injective

theorem RigidityGeomPoints.rig
    (ℓ : ℕ) [Fact ℓ.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
    (D : RelativePic0Designation ↥(GaloisRep.ratLocalizedAt ℓ) c)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase) [IsReduced D.P]
    (φ ψ : SchemeHomOver D.toBase D.toBase)
    (h : ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) D.toBase,
      x.1 ≫ φ.1 = x.1 ≫ ψ.1) :
    φ = ψ := by
  haveI := hsm
  haveI := hpr
  apply Subtype.ext
  exact RigidityGeomPoints.ext_of_forall_geometric_point (K := AlgebraicClosure ℚ)
    (RigidityGeomPoints.algebraMap_ratLocalizedAt_injective ℓ) D.toBase φ.1 ψ.1 φ.2 ψ.2
    (fun x hx => h ⟨x, hx⟩)

end RIGAssembly

set_option maxHeartbeats 3200000 in
theorem solution
    (ℓ : ℕ) [Fact ℓ.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))) c)
    (D : RelativePic0Designation ↥(GaloisRep.ratLocalizedAt ℓ) c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase) (hgc : GeometricallyConnected D.toBase)
    [IsReduced D.P]
    (φ ψ : SchemeHomOver D.toBase D.toBase)
    (h : ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) D.toBase,
      x.1 ≫ φ.1 = x.1 ≫ ψ.1) :
    φ = ψ :=
  RigidityGeomPoints.rig ℓ c D hsm hpr φ ψ h

end S_AlgebraicGeometry_RelPicard_schemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_schemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced (solution)
