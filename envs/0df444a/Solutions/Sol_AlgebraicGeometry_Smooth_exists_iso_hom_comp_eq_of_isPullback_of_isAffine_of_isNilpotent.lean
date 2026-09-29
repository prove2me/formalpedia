-- Prove2me | solution 1 for AlgebraicGeometry.Smooth.exists_iso_hom_comp_eq_of_isPullback_of_isAffine_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/47e8496b-926e-5a63-bddd-466862c922ec

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Theorems.Thm_Algebra_FormallySmooth_exists_algEquiv_comp_eq_of_isNilpotent_of_ker_eq_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Smooth_exists_iso_hom_comp_eq_of_isPullback_of_isAffine_of_isNilpotent

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

namespace LiftIsoAffine

section Pushout

variable {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
  (A : Type u) [CommRing A] [Algebra T' A]

abbrev J : Ideal A := (RingHom.ker π).map (algebraMap T' A)

noncomputable def πbar : T →+* A ⧸ J π A :=
  (Ideal.Quotient.lift (RingHom.ker π) ((Ideal.Quotient.mk (J π A)).comp (algebraMap T' A)) (fun x hx => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.mem_map_of_mem _ hx)).comp
    (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom

theorem πbar_apply (x : T') : πbar π hπ A (π x) = Ideal.Quotient.mk (J π A) (algebraMap T' A x) := by
  have : (RingHom.quotientKerEquivOfSurjective hπ).symm (π x) = Ideal.Quotient.mk _ x := by
    apply (RingHom.quotientKerEquivOfSurjective hπ).injective
    rw [RingEquiv.apply_symm_apply, RingHom.quotientKerEquivOfSurjective_apply_mk]
  simp [πbar, this]

theorem isPushout_quotient :
    IsPushout (CommRingCat.ofHom (algebraMap T' A)) (CommRingCat.ofHom π)
      (CommRingCat.ofHom (Ideal.Quotient.mk (J π A))) (CommRingCat.ofHom (πbar π hπ A)) := by
  have w : CommSq (CommRingCat.ofHom (algebraMap T' A)) (CommRingCat.ofHom π)
      (CommRingCat.ofHom (Ideal.Quotient.mk (J π A))) (CommRingCat.ofHom (πbar π hπ A)) :=
    ⟨by ext x; simp [πbar_apply]⟩
  refine IsPushout.of_isColimit' w (PushoutCocone.IsColimit.mk _ (fun s => ?_) (fun s => ?_) (fun s => ?_) ?_)
  · have hker : J π A ≤ RingHom.ker s.inl.hom := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker]
      have := CategoryTheory.congr_fun s.condition x
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at this
      rw [this, (RingHom.mem_ker).mp hx, map_zero]
    exact CommRingCat.ofHom (Ideal.Quotient.lift _ s.inl.hom fun a ha => hker ha)
  · ext a; rfl
  · ext t
    obtain ⟨x, rfl⟩ := hπ t
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom, πbar_apply,
      Ideal.Quotient.lift_mk]
    have := CategoryTheory.congr_fun s.condition x
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  · intro s m hm₁ hm₂
    ext a
    have := CategoryTheory.congr_fun hm₁ a
    simpa using this

end Pushout

end LiftIsoAffine

open LiftIsoAffine in
theorem solution
    {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {V Y Y' : Scheme.{u}} (v : V ⟶ Spec (CommRingCat.of T))
    (q : Y ⟶ Spec (CommRingCat.of T')) [IsAffine Y] (hq : Smooth q)
    (q' : Y' ⟶ Spec (CommRingCat.of T')) [IsAffine Y'] (hq' : Smooth q')
    (g : V ⟶ Y) (hg : IsPullback g v q (Spec.map (CommRingCat.ofHom π)))
    (g' : V ⟶ Y') (hg' : IsPullback g' v q' (Spec.map (CommRingCat.ofHom π))) :
    ∃ φ : Y ≅ Y', φ.hom ≫ q' = q ∧ g ≫ φ.hom = g' := by

  obtain ⟨φq, hφq⟩ := Spec.map_surjective (Y.isoSpec.inv ≫ q)
  obtain ⟨φq', hφq'⟩ := Spec.map_surjective (Y'.isoSpec.inv ≫ q')
  let A : Type u := Γ(Y, ⊤)
  let A' : Type u := Γ(Y', ⊤)
  letI : Algebra T' A := φq.hom.toAlgebra
  letI : Algebra T' A' := φq'.hom.toAlgebra

  haveI : Smooth (Y.isoSpec.inv ≫ q) := by haveI := hq; infer_instance
  haveI : Smooth (Y'.isoSpec.inv ≫ q') := by haveI := hq'; infer_instance
  have hsA : Algebra.FormallySmooth T' A := by
    have : RingHom.Smooth φq.hom := (HasRingHomProperty.Spec_iff (P := @Smooth)).mp (hφq.symm ▸ inferInstance)
    exact this.formallySmooth
  have hsA' : Algebra.FormallySmooth T' A' := by
    have : RingHom.Smooth φq'.hom := (HasRingHomProperty.Spec_iff (P := @Smooth)).mp (hφq'.symm ▸ inferInstance)
    exact this.formallySmooth

  have hq1 : q = Y.isoSpec.hom ≫ Spec.map φq := by rw [hφq, Iso.hom_inv_id_assoc]
  have hq1' : q' = Y'.isoSpec.hom ≫ Spec.map φq' := by rw [hφq', Iso.hom_inv_id_assoc]
  have hg₁ : IsPullback (g ≫ Y.isoSpec.hom) v (Spec.map φq) (Spec.map (CommRingCat.ofHom π)) :=
    hg.of_iso (Iso.refl _) Y.isoSpec (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp [hq1]) (by simp)
  have hg₁' : IsPullback (g' ≫ Y'.isoSpec.hom) v (Spec.map φq') (Spec.map (CommRingCat.ofHom π)) :=
    hg'.of_iso (Iso.refl _) Y'.isoSpec (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp [hq1']) (by simp)
  have hpb := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quotient π hπ A)
  have hpb' := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quotient π hπ A')

  have eφ : CommRingCat.ofHom (algebraMap T' A) = φq := rfl
  have eφ' : CommRingCat.ofHom (algebraMap T' A') = φq' := rfl
  rw [eφ] at hpb
  rw [eφ'] at hpb'
  let ε : V ≅ Spec (CommRingCat.of (A ⧸ J π A)) := hg₁.isoIsPullback _ _ hpb
  let ε' : V ≅ Spec (CommRingCat.of (A' ⧸ J π A')) := hg₁'.isoIsPullback _ _ hpb'
  have hε₁ : ε.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J π A))) = g ≫ Y.isoSpec.hom :=
    hg₁.isoIsPullback_hom_fst _ _ hpb
  have hε₂ : ε.hom ≫ Spec.map (CommRingCat.ofHom (πbar π hπ A)) = v := hg₁.isoIsPullback_hom_snd _ _ hpb
  have hε₁' : ε'.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J π A'))) = g' ≫ Y'.isoSpec.hom :=
    hg₁'.isoIsPullback_hom_fst _ _ hpb'
  have hε₂' : ε'.hom ≫ Spec.map (CommRingCat.ofHom (πbar π hπ A')) = v := hg₁'.isoIsPullback_hom_snd _ _ hpb'

  obtain ⟨κ₁, hκ₁⟩ := Spec.map_surjective (ε.inv ≫ ε'.hom)
  obtain ⟨κ₂, hκ₂⟩ := Spec.map_surjective (ε'.inv ≫ ε.hom)
  have h12 : κ₂ ≫ κ₁ = 𝟙 _ := Spec.map_injective (by
    rw [Spec.map_comp, hκ₁, hκ₂, Category.assoc, ε'.hom_inv_id_assoc, ε.inv_hom_id, Spec.map_id])
  have h21 : κ₁ ≫ κ₂ = 𝟙 _ := Spec.map_injective (by
    rw [Spec.map_comp, hκ₁, hκ₂, Category.assoc, ε.hom_inv_id_assoc, ε'.inv_hom_id, Spec.map_id])

  have hκlin : ∀ x : T', κ₁.hom (algebraMap T' (A' ⧸ J π A') x) = algebraMap T' (A ⧸ J π A) x := by
    intro x
    have hv : Spec.map κ₁ ≫ Spec.map (CommRingCat.ofHom (πbar π hπ A')) = Spec.map (CommRingCat.ofHom (πbar π hπ A)) := by
      rw [hκ₁, Category.assoc, hε₂', ← hε₂, ε.inv_hom_id_assoc]
    have hv' : CommRingCat.ofHom (πbar π hπ A') ≫ κ₁ = CommRingCat.ofHom (πbar π hπ A) :=
      Spec.map_injective (by rw [Spec.map_comp]; exact hv)
    have := congrArg (fun f : CommRingCat.of T ⟶ _ => f.hom (π x)) hv'
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply, πbar_apply] at this
    rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap]
    exact this
  let κ : (A' ⧸ J π A') →ₐ[T'] (A ⧸ J π A) :=
    { toRingHom := κ₁.hom, commutes' := hκlin }
  have hκinj : Function.Injective κ := by
    intro a b h
    have := congrArg κ₂.hom h
    change (κ₁ ≫ κ₂).hom a = (κ₁ ≫ κ₂).hom b at this
    rwa [h21] at this
  have hκsurj : Function.Surjective κ := by
    intro b
    refine ⟨κ₂.hom b, ?_⟩
    change (κ₂ ≫ κ₁).hom b = b
    rw [h12]; rfl

  let gA : A →ₐ[T'] A ⧸ J π A := Ideal.Quotient.mkₐ T' (J π A)
  let gA' : A' →ₐ[T'] A ⧸ J π A := κ.comp (Ideal.Quotient.mkₐ T' (J π A'))
  have hgA : Function.Surjective gA := Ideal.Quotient.mkₐ_surjective T' _
  have hgA' : Function.Surjective gA' := hκsurj.comp (Ideal.Quotient.mkₐ_surjective T' _)
  have hkA : RingHom.ker gA.toRingHom = (RingHom.ker π).map (algebraMap T' A) := Ideal.Quotient.mkₐ_ker T' _
  have hkA' : RingHom.ker gA'.toRingHom = (RingHom.ker π).map (algebraMap T' A') := by
    ext a
    rw [RingHom.mem_ker]
    change κ (Ideal.Quotient.mkₐ T' (J π A') a) = 0 ↔ _
    rw [← map_zero κ, hκinj.eq_iff, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]

  haveI := hsA
  haveI := hsA'
  obtain ⟨e, he⟩ := Algebra.FormallySmooth.exists_algEquiv_comp_eq_of_isNilpotent_of_ker_eq_map (RingHom.ker π) hker
    gA gA' hgA hgA' hkA hkA'

  let eC : Γ(Y, ⊤) ≅ Γ(Y', ⊤) := e.toRingEquiv.toCommRingCatIso
  let φmid : Spec Γ(Y, ⊤) ≅ Spec Γ(Y', ⊤) :=
    { hom := Spec.map eC.inv, inv := Spec.map eC.hom,
      hom_inv_id := by rw [← Spec.map_comp, eC.hom_inv_id, Spec.map_id],
      inv_hom_id := by rw [← Spec.map_comp, eC.inv_hom_id, Spec.map_id] }
  refine ⟨Y.isoSpec ≪≫ φmid ≪≫ Y'.isoSpec.symm, ?_, ?_⟩
  ·
    have h1 : φq' ≫ eC.inv = φq := by
      ext x
      change e.symm (algebraMap T' A' x) = algebraMap T' A x
      exact e.symm.commutes x
    change (Y.isoSpec.hom ≫ Spec.map eC.inv ≫ Y'.isoSpec.inv) ≫ q' = q
    simp only [Category.assoc]
    rw [hq1', Y'.isoSpec.inv_hom_id_assoc, ← Spec.map_comp, h1, ← hq1]
  ·
    have h2 : CommRingCat.ofHom gA'.toRingHom = CommRingCat.ofHom (Ideal.Quotient.mk (J π A')) ≫ κ₁ := rfl
    have h3 : CommRingCat.ofHom gA.toRingHom = CommRingCat.ofHom (Ideal.Quotient.mk (J π A)) := rfl
    have h4 : eC.inv ≫ CommRingCat.ofHom gA.toRingHom = CommRingCat.ofHom gA'.toRingHom := by
      ext a
      change gA (e.symm a) = gA' a
      rw [← he]; simp
    change g ≫ (Y.isoSpec.hom ≫ Spec.map eC.inv ≫ Y'.isoSpec.inv) = g'
    have hε' : ε'.hom = ε.hom ≫ Spec.map κ₁ := by rw [hκ₁, ε.hom_inv_id_assoc]
    rw [← Category.assoc, ← hε₁]
    simp only [Category.assoc]
    rw [← Category.assoc, ← Category.assoc, Iso.comp_inv_eq, ← hε₁', hε']
    simp only [Category.assoc]
    rw [← Spec.map_comp, ← Spec.map_comp, ← h3, h4, ← h2]

end S_AlgebraicGeometry_Smooth_exists_iso_hom_comp_eq_of_isPullback_of_isAffine_of_isNilpotent
end P2MW
export P2MW.S_AlgebraicGeometry_Smooth_exists_iso_hom_comp_eq_of_isPullback_of_isAffine_of_isNilpotent (solution)
