-- Prove2me | solution 1 for AlgebraicGeometry.finrank_sections_eq_finrank_tensorProduct_of_isPullback_residue_of_isFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/a29f03f0-d7b7-55f4-b7e5-21de07de8081

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_algEquiv_globalSections_pullback_spec_tensorProduct
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_finrank_sections_eq_finrank_tensorProduct_of_isPullback_residue_of_isFinite

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X Xf X' Y : Scheme.{u}} (g : X ⟶ Spec (.of R))
    (i : Xf ⟶ X) [IsOpenImmersion i] [IsFinite (i ≫ g)] (j : X' ⟶ X)
    (hcover : Set.range i ∪ Set.range j = Set.univ)
    (hempty : IsLocalRing.closedPoint R ∉ Set.range (j ≫ g))
    (q : Y ⟶ Spec (.of (IsLocalRing.ResidueField R))) (π : Y ⟶ X)
    (hY : IsPullback π q g (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom q ⊤
    letI : Algebra R Γ(Xf, ⊤) := ((Scheme.ΓSpecIso (.of R)).inv ≫ (i ≫ g).appTop).hom.toAlgebra
    Module.Finite (IsLocalRing.ResidueField R) Γ(Y, ⊤) ∧
    Module.finrank (IsLocalRing.ResidueField R) Γ(Y, ⊤) =
      Module.finrank (IsLocalRing.ResidueField R) (TensorProduct R (IsLocalRing.ResidueField R) Γ(Xf, ⊤)) := by
  classical

  set κ := IsLocalRing.ResidueField R with hκdef
  let sκ : Spec (.of κ) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R κ))
  have hY' : IsPullback π q g sκ := hY

  obtain ⟨hXf, -⟩ :=
    (HasAffineProperty.iff_of_isAffine (P := @IsFinite) (f := i ≫ g)).mp inferInstance
  haveI : IsAffine Xf := hXf
  letI algY : Algebra κ Γ(Y, ⊤) := Scheme.TwoAffineOpenCover.algebraOfHom q ⊤
  letI algB : Algebra R Γ(Xf, ⊤) :=
    ((Scheme.ΓSpecIso (.of R)).inv ≫ (i ≫ g).appTop).hom.toAlgebra

  let PB := pullback (i ≫ g) sκ
  letI algPB : Algebra κ Γ(PB, ⊤) :=
    ((Scheme.ΓSpecIso (.of κ)).inv ≫ (pullback.snd (i ≫ g) sκ).appTop).hom.toAlgebra
  have hbig : IsPullback (pullback.snd (i ≫ g) sκ) (pullback.fst (i ≫ g) sκ) sκ (i ≫ g) :=
    (IsPullback.of_hasPullback (i ≫ g) sκ).flip
  have hsq : IsPullback (hY'.flip.lift (pullback.snd (i ≫ g) sκ) (pullback.fst (i ≫ g) sκ ≫ i)
      (by rw [hbig.w, Category.assoc])) (pullback.fst (i ≫ g) sκ) π i :=
    IsPullback.of_right' hbig hY'.flip
  set u := hY'.flip.lift (pullback.snd (i ≫ g) sκ) (pullback.fst (i ≫ g) sκ ≫ i)
      (by rw [hbig.w, Category.assoc]) with hudef
  have huq : u ≫ q = pullback.snd (i ≫ g) sκ := hY'.flip.lift_fst _ _ _
  have huπ : u ≫ π = pullback.fst (i ≫ g) sκ ≫ i := hY'.flip.lift_snd _ _ _

  haveI : IsOpenImmersion u :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) hsq.flip
      inferInstance

  have hsurj : Function.Surjective u := by
    intro y

    have h1 : π y ∈ Set.range i ∪ Set.range j := by rw [hcover]; trivial
    have hnotj : π y ∉ Set.range j := by
      rintro ⟨z, hz⟩
      apply hempty
      refine ⟨z, ?_⟩
      rw [Scheme.Hom.comp_apply, hz]
      have hw : g (π y) = sκ (q y) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hY'.w]
      rw [hw]
      change PrimeSpectrum.comap (algebraMap R κ) (q y) = IsLocalRing.closedPoint R
      exact IsLocalRing.PrimeSpectrum.comap_residue R (q y)
    have hi : π y ∈ Set.range i := h1.resolve_right hnotj

    have hrange : Set.range u = π ⁻¹' Set.range i := by
      rw [← hsq.isoPullback_hom_fst, ← Scheme.Pullback.range_fst π i]
      ext x
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨hsq.isoPullback.hom a, by rw [Scheme.Hom.comp_apply]⟩
      · rintro ⟨b, rfl⟩
        obtain ⟨a, rfl⟩ := (hsq.isoPullback.hom).surjective b
        exact ⟨a, by rw [Scheme.Hom.comp_apply]⟩
    have hy : y ∈ Set.range u := by rw [hrange]; exact hi
    exact hy
  haveI : IsIso u := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    ext1
    exact Set.range_eq_univ.mpr hsurj

  haveI : IsIso u.appTop := by
    change IsIso (u.app ⊤)
    infer_instance
  let eΓ : Γ(Y, ⊤) ≅ Γ(PB, ⊤) := asIso u.appTop
  have happ : q.appLE ⊤ ⊤ le_top = q.appTop := by
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
  have hcomm : ∀ c : κ, eΓ.hom.hom (algebraMap κ Γ(Y, ⊤) c) = algebraMap κ Γ(PB, ⊤) c := by
    intro c
    change u.appTop.hom ((q.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (.of κ)).inv.hom c)) =
      (pullback.snd (i ≫ g) sκ).appTop.hom ((Scheme.ΓSpecIso (.of κ)).inv.hom c)
    rw [happ, ← huq]
    rfl
  let eY : Γ(Y, ⊤) ≃ₐ[κ] Γ(PB, ⊤) :=
    AlgEquiv.ofRingEquiv (f := eΓ.commRingCatIsoToRingEquiv) hcomm

  obtain ⟨eT, -⟩ :=
    AlgebraicGeometry.exists_algEquiv_globalSections_pullback_spec_tensorProduct (i ≫ g) κ
  have E : TensorProduct R κ Γ(Xf, ⊤) ≃ₗ[κ] Γ(Y, ⊤) :=
    (eT.trans eY.symm).toLinearEquiv
  haveI : Module.Finite R Γ(Xf, ⊤) := by
    obtain ⟨-, hfin⟩ :=
      (HasAffineProperty.iff_of_isAffine (P := @IsFinite) (f := i ≫ g)).mp inferInstance
    have h1 : RingHom.Finite ((Scheme.ΓSpecIso (.of R)).inv ≫ (i ≫ g).appTop).hom := by
      rw [CommRingCat.hom_comp]
      refine RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ ?_)
      exact (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.surjective
    exact h1
  refine ⟨Module.Finite.equiv E, ?_⟩
  exact (LinearEquiv.finrank_eq E).symm

end S_AlgebraicGeometry_finrank_sections_eq_finrank_tensorProduct_of_isPullback_residue_of_isFinite
end P2MW
export P2MW.S_AlgebraicGeometry_finrank_sections_eq_finrank_tensorProduct_of_isPullback_residue_of_isFinite (solution)
