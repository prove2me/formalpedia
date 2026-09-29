-- Prove2me | solution 1 for AlgebraicGeometry.exists_isFinite_isOpenImmersion_disjoint_cover_of_locallyQuasiFinite_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/8d07cac0-5b2b-5ab7-af5a-dc6a49c178eb

import Mathlib
import Theorems.Thm_HenselianLocalRing_exists_isIdempotentElem_moduleFinite_quotient_of_quasiFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isFinite_isOpenImmersion_disjoint_cover_of_locallyQuasiFinite_of_henselianLocalRing

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.opensRange_homOfLE Spec.map_preimage Surjective Spec.map_apply IsProper Scheme.Opens.range_ι Scheme.Hom LocallyQuasiFinite UniversallyClosed IsFinite QuasiCompact isPullback_morphismRestrict LocallyOfFiniteType Spec Spec.map Scheme QuasiCompact.compactSpace_of_compactSpace IsOpenImmersion universallyClosed_eq IsSeparated Spec.preimage HasRingHomProperty.Spec_iff Scheme.Hom.continuous IsFinite.SpecMap_iff Scheme.Opens.ι_apply IsAffineOpen Scheme.homOfLE_ι_assoc Scheme.Opens HasRingHomProperty Scheme.Hom.isoOpensRange_hom_ι IsFinite.of_isProper_of_locallyQuasiFinite Scheme.Hom.comp_apply Scheme.Hom.coe_opensRange"
p2m_open "AlgebraicGeometry"

namespace QFHens

theorem universallyClosed_of_finite_cover {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type*} [Finite ι]
    {V : ι → Scheme.{u}} (q : ∀ i, V i ⟶ X) [∀ i, IsOpenImmersion (q i)]
    (hcov : ⋃ i, Set.range (q i) = Set.univ) (hUC : ∀ i, UniversallyClosed (q i ≫ f)) :
    UniversallyClosed f := by

  let U : ι → X.Opens := fun i ↦ (q i).opensRange
  have hU : ∀ i, UniversallyClosed ((U i).ι ≫ f) := fun i ↦ by
    have e : (U i).ι = (q i).isoOpensRange.inv ≫ q i :=
      (Iso.eq_inv_comp _).mpr (Scheme.Hom.isoOpensRange_hom_ι (q i))
    rw [e, Category.assoc, MorphismProperty.cancel_left_of_respectsIso @UniversallyClosed]
    exact hUC i
  have hUcov : ⋃ i, (U i : Set X) = Set.univ := by
    simpa only [U, Scheme.Hom.coe_opensRange] using hcov
  rw [universallyClosed_eq]
  intro X' Y' i₁ i₂ f' H

  have hpiece : ∀ i, IsClosedMap ((i₁ ⁻¹ᵁ U i).ι ≫ f') := fun i ↦ by
    have sq : IsPullback ((i₁ ⁻¹ᵁ U i).ι ≫ f') (i₁ ∣_ U i) i₂ ((U i).ι ≫ f) :=
      ((isPullback_morphismRestrict i₁ (U i)).paste_vert H.flip).flip
    have := hU i
    rw [universallyClosed_eq] at this
    exact this _ _ _ sq

  have hcovX' : ∀ x : X', ∃ i, x ∈ i₁ ⁻¹ᵁ U i := fun x ↦ by
    have hx : i₁ x ∈ ⋃ i, (U i : Set X) := hUcov ▸ Set.mem_univ _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨i, hi⟩

  intro C hC
  have : f' '' C = ⋃ i, ((i₁ ⁻¹ᵁ U i).ι ≫ f') '' (((i₁ ⁻¹ᵁ U i).ι) ⁻¹' C) := by
    ext y
    simp only [Set.mem_image, Set.mem_iUnion, Set.mem_preimage, Scheme.Hom.comp_apply,
      Scheme.Opens.ι_apply]
    constructor
    · rintro ⟨x, hxC, rfl⟩
      obtain ⟨i, hi⟩ := hcovX' x
      exact ⟨i, ⟨x, hi⟩, hxC, rfl⟩
    · rintro ⟨i, x, hxC, rfl⟩
      exact ⟨x.1, hxC, rfl⟩
  rw [this]
  exact isClosed_iUnion_of_finite fun i ↦ hpiece i _ (hC.preimage (Scheme.Hom.continuous _))

theorem affine_piece {R : Type u} [CommRing R] [HenselianLocalRing R] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of R)) [LocallyOfFiniteType g] [LocallyQuasiFinite g] [IsSeparated g]
    {U : X.Opens} (hU : IsAffineOpen U) :
    ∃ V : X.Opens, V ≤ U ∧ IsFinite (V.ι ≫ g) ∧ IsClosed (V : Set X) ∧
      ∀ x : X, x ∈ U → g x = IsLocalRing.closedPoint R → x ∈ V := by
  classical
  let φ : CommRingCat.of R ⟶ Γ(X, U) := Spec.preimage (hU.fromSpec ≫ g)
  have hφ : Spec.map φ = hU.fromSpec ≫ g := Spec.map_preimage _
  letI alg : Algebra R Γ(X, U) := φ.hom.toAlgebra
  haveI : Algebra.FiniteType R Γ(X, U) := by
    have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this
  haveI : Algebra.QuasiFinite R Γ(X, U) := by
    have : LocallyQuasiFinite (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mp this
  obtain ⟨e, he, hfin, hprime⟩ :=
    HenselianLocalRing.exists_isIdempotentElem_moduleFinite_quotient_of_quasiFinite
      (R := R) (S := Γ(X, U))

  let L : Type u := Localization.Away e
  let ψ : Spec (.of L) ⟶ X := Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) L)) ≫ hU.fromSpec
  have hψg : ψ ≫ g = Spec.map (φ ≫ CommRingCat.ofHom (algebraMap Γ(X, U) L)) := by
    simp only [ψ, Category.assoc, ← hφ, Spec.map_comp]
  haveI hfinψ : IsFinite (ψ ≫ g) := by
    rw [hψg, IsFinite.SpecMap_iff, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    suffices hL : Module.Finite R L by
      have h := RingHom.finite_algebraMap.mpr hL
      rwa [IsScalarTower.algebraMap_eq R Γ(X, U) L] at h
    have h1 : algebraMap Γ(X, U) L (1 - e) = 0 := by
      have hu := IsLocalization.Away.algebraMap_isUnit (S := L) e
      rw [← hu.mul_left_eq_zero, ← map_mul, sub_mul, one_mul, he.eq, sub_self, map_zero]
    have hker : ∀ a ∈ Ideal.span ({1 - e} : Set Γ(X, U)),
        (IsScalarTower.toAlgHom R Γ(X, U) L) a = 0 := by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp [h1]
    let qh : (Γ(X, U) ⧸ Ideal.span ({1 - e} : Set Γ(X, U))) →ₐ[R] L :=
      Ideal.Quotient.liftₐ _ (IsScalarTower.toAlgHom R Γ(X, U) L) hker
    have hsurj : Function.Surjective qh := by
      intro y
      obtain ⟨s, rfl⟩ := IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem e he (S := L) y
      exact ⟨Ideal.Quotient.mk _ s, rfl⟩
    exact Module.Finite.of_surjective qh.toLinearMap hsurj
  refine ⟨ψ.opensRange, ?_, ?_, ?_, ?_⟩
  ·
    change (ψ.opensRange : Set X) ⊆ U
    rw [Scheme.Hom.coe_opensRange, ← hU.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    exact ⟨_, (Scheme.Hom.comp_apply _ _ y).symm⟩
  ·
    rw [(Iso.eq_inv_comp _).mpr (Scheme.Hom.isoOpensRange_hom_ι ψ), Category.assoc,
      MorphismProperty.cancel_left_of_respectsIso @IsFinite]
    exact hfinψ
  ·
    rw [Scheme.Hom.coe_opensRange]
    have : UniversallyClosed ψ := .of_comp_of_isSeparated ψ g
    exact ψ.isClosedMap.isClosed_range
  ·
    intro x hxU hgx
    change x ∈ (ψ.opensRange : Set X)
    rw [Scheme.Hom.coe_opensRange]
    set p := hU.primeIdealOf ⟨x, hxU⟩ with hpdef
    have hp : hU.fromSpec p = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
    have hep : e ∉ p.asIdeal := by
      refine hprime p.asIdeal inferInstance ?_
      change Ideal.comap φ.hom p.asIdeal = _
      rw [← PrimeSpectrum.comap_asIdeal, ← Spec.map_apply, hφ, Scheme.Hom.comp_apply, hp, hgx]
      rfl
    have hrange : Set.range (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) L))) =
        (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum Γ(X, U))) := by
      rw [← PrimeSpectrum.localization_away_comap_range L e]
      congr 1
    obtain ⟨y, hy⟩ : p ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) L))) := by
      rw [hrange]; exact hep
    exact ⟨y, by rw [Scheme.Hom.comp_apply, hy, hp]⟩

end QFHens

end AlgebraicGeometry

p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isFinite_isOpenImmersion_disjoint_cover_of_locallyQuasiFinite_of_henselianLocalRing.AlgebraicGeometry"

theorem solution
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of R))
    [LocallyOfFiniteType g] [LocallyQuasiFinite g] [IsSeparated g] [QuasiCompact g] :
    ∃ (Xf X' : Scheme.{u}) (i : Xf ⟶ X) (j : X' ⟶ X) (_ : IsOpenImmersion i)
      (_ : IsOpenImmersion j),
      IsFinite (i ≫ g) ∧
      Set.range i ∪ Set.range j = Set.univ ∧
      Disjoint (Set.range i) (Set.range j) ∧
      IsLocalRing.closedPoint R ∉ Set.range (j ≫ g) := by
  classical
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace g

  obtain ⟨t, ht⟩ : ∃ t : Finset X.affineOpens, ∀ x : X, ∃ W ∈ t, x ∈ (W : X.Opens) := by
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
      (fun W : X.affineOpens ↦ ((W : X.Opens) : Set X)) (fun W ↦ (W : X.Opens).isOpen)
      (fun x _ ↦ by
        obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
          X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
        exact Set.mem_iUnion.mpr ⟨⟨W, hW⟩, hxW⟩)
    refine ⟨t, fun x ↦ ?_⟩
    simpa [Set.mem_iUnion] using ht (Set.mem_univ x)
  choose V hVle hVfin hVcl hVmem using fun W : X.affineOpens ↦ QFHens.affine_piece g W.2
  let Xf : X.Opens := ⨆ W : t, V W.1
  have hXfcl : IsClosed (Xf : Set X) := by
    rw [Opens.coe_iSup]
    exact isClosed_iUnion_of_finite fun W ↦ hVcl W.1
  let Xo : X.Opens := ⟨(Xf : Set X)ᶜ, hXfcl.isOpen_compl⟩
  have hsp : ∀ x : X, g x = IsLocalRing.closedPoint R → x ∈ Xf := fun x hx ↦ by
    obtain ⟨W, hWt, hxW⟩ := ht x
    exact Opens.mem_iSup.mpr ⟨⟨W, hWt⟩, hVmem W x hxW hx⟩

  haveI : UniversallyClosed (Xf.ι ≫ g) := by
    refine QFHens.universallyClosed_of_finite_cover (Xf.ι ≫ g)
      (fun W : t ↦ X.homOfLE (le_iSup (fun W : t ↦ V W.1) W)) ?_ fun W ↦ ?_
    · apply Set.eq_univ_of_forall
      intro x
      obtain ⟨W, hW⟩ := Opens.mem_iSup.mp x.2
      refine Set.mem_iUnion.mpr ⟨W, ?_⟩
      rw [← Scheme.Hom.coe_opensRange, Scheme.opensRange_homOfLE]
      show Xf.ι x ∈ V W.1
      rw [Scheme.Opens.ι_apply]
      exact hW
    · rw [Scheme.homOfLE_ι_assoc]
      haveI := hVfin W.1
      infer_instance
  haveI : IsProper (Xf.ι ≫ g) := {}
  have hfin : IsFinite (Xf.ι ≫ g) := IsFinite.of_isProper_of_locallyQuasiFinite _
  refine ⟨Xf, Xo, Xf.ι, Xo.ι, inferInstance, inferInstance, hfin, ?_, ?_, ?_⟩
  · rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    exact Set.union_compl_self _
  · rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    exact disjoint_compl_right
  · rintro ⟨y, hy⟩
    rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] at hy
    exact y.2 (hsp _ hy)

end S_AlgebraicGeometry_exists_isFinite_isOpenImmersion_disjoint_cover_of_locallyQuasiFinite_of_henselianLocalRing
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isFinite_isOpenImmersion_disjoint_cover_of_locallyQuasiFinite_of_henselianLocalRing (solution)
