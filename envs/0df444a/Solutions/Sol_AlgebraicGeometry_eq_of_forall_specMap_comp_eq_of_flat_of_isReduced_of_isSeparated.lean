-- Prove2me | solution 1 for AlgebraicGeometry.eq_of_forall_specMap_comp_eq_of_flat_of_isReduced_of_isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/285fede8-a633-57b2-a59c-4e7a770412c0

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_eq_of_forall_specMap_comp_eq_of_flat_of_isReduced_of_isSeparated

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_eq_of_forall_specMap_comp_eq_of_flat_of_isReduced_of_isSeparated.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "ext_of_fromSpecResidueField_eq Surjective Spec.map_apply Scheme.Hom Flat.SpecMap_iff pointOfClosedPoint Scheme.Pullback.range_fst LocallyOfFiniteType Spec Spec.map Scheme LocallyOfFiniteType.jacobsonSpace Flat pointOfClosedPoint_comp_assoc Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc IsReduced IsSeparated Flat.epi_of_flat_of_surjective LocallyOfFinitePresentation"
p2m_open "AlgebraicGeometry"

theorem epi_SpecMap_of_field {K L : Type u} [Field K] [Field L]
    (e : CommRingCat.of K ⟶ CommRingCat.of L) : Epi (Spec.map e) := by
  have hflat : Flat (Spec.map e) := by
    rw [Flat.SpecMap_iff]
    letI := e.hom.toAlgebra
    show Module.Flat K L
    infer_instance
  have hsurj : Surjective (Spec.map e) := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem epi_SpecMap_residueFieldMap {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    Epi (Spec.map (f.residueFieldMap x)) :=
  epi_SpecMap_of_field (K := Y.residueField (f x)) (L := X.residueField x) (f.residueFieldMap x)

theorem dense_preimage_genericPoint_of_flat {R : Type u} [CommRing R] [IsDomain R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] [LocallyOfFinitePresentation f] :
    Dense ((⇑f) ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)}) := by
  have hopen : IsOpenMap f := f.isOpenMap
  rw [dense_iff_inter_open]
  rintro U hU ⟨u, hu⟩
  have hη : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ⤳ f u :=
    (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  obtain ⟨v, hv, hv'⟩ := hη.mem_open (hopen U hU) ⟨u, hu, rfl⟩
  exact ⟨v, hv, hv'⟩

end AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] [IsDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    [Flat f] [LocallyOfFinitePresentation f] [IsReduced X] [IsSeparated g]
    (φ ψ : X ⟶ Y) (hφ : φ ≫ g = f) (hψ : ψ ≫ g = f)
    (h : ∀ x : Spec (CommRingCat.of Ω) ⟶ X,
      x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R Ω)) → x ≫ φ = x ≫ ψ) :
    φ = ψ := by
  classical

  set iΩ : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R Ω)) with hiΩ
  let F : Scheme.{u} := pullback f iΩ
  let p₁ : F ⟶ X := pullback.fst f iΩ
  let q : F ⟶ Spec (CommRingCat.of Ω) := pullback.snd f iΩ
  haveI : LocallyOfFiniteType q := inferInstance
  haveI : JacobsonSpace F := LocallyOfFiniteType.jacobsonSpace q

  let η : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  have hinj : Function.Injective (algebraMap R Ω) := by
    rw [IsScalarTower.algebraMap_eq R K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective R K)
  have hηΩ : ∀ t : Spec (CommRingCat.of Ω), iΩ t = η := by
    intro t
    apply PrimeSpectrum.ext
    rw [hiΩ, Spec.map_apply]
    simp only [CommRingCat.hom_ofHom, PrimeSpectrum.comap_asIdeal]
    rw [Ideal.eq_bot_of_prime t.asIdeal]
    exact Ideal.comap_bot_of_injective _ hinj

  have hD : Dense (Set.range ⇑p₁) := by
    refine (AlgebraicGeometry.dense_preimage_genericPoint_of_flat f).mono ?_
    rw [Scheme.Pullback.range_fst]
    exact Set.preimage_mono (Set.singleton_subset_iff.mpr ⟨default, hηΩ default⟩)

  let S : Set X := (⇑p₁) '' closedPoints F
  have hS : Dense S :=
    DenseRange.dense_image hD p₁.continuous (dense_iff_closure_eq.mpr closure_closedPoints)
  refine ext_of_fromSpecResidueField_eq φ ψ g S hS ?_ (hφ.trans hψ.symm)
  rintro _ ⟨c, hc, rfl⟩
  have hc' : IsClosed ({c} : Set F) := hc

  let pt : Spec (CommRingCat.of Ω) ⟶ X := pointOfClosedPoint q c hc' ≫ p₁
  have hpt : pt ≫ f = iΩ := by
    simp only [pt, Category.assoc]
    rw [pullback.condition, pointOfClosedPoint_comp_assoc]
  have key := h pt hpt
  simp only [pt, pointOfClosedPoint, Category.assoc] at key
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc,
    ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc] at key
  haveI := AlgebraicGeometry.epi_SpecMap_residueFieldMap p₁ c
  rwa [cancel_epi, cancel_epi] at key

end S_AlgebraicGeometry_eq_of_forall_specMap_comp_eq_of_flat_of_isReduced_of_isSeparated
end P2MW
export P2MW.S_AlgebraicGeometry_eq_of_forall_specMap_comp_eq_of_flat_of_isReduced_of_isSeparated (solution)
