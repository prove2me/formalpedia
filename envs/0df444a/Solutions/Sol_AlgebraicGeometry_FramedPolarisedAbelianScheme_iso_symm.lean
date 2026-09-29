-- Prove2me | solution 1 for AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_symm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/6e3bb41c-46bf-5a68-a67a-5aed23d95f2e

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_symm

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

noncomputable section

namespace FramedIso31

universe u

variable {g N n : ℕ}

theorem mul_val_congr {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (ht : t₁ = t₂) (P₁ Q₁ : SchemeHomOver t₁ f)
    (P₂ Q₂ : SchemeHomOver t₂ f) (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (L.mul t₁ P₁ Q₁).1 = (L.mul t₂ P₂ Q₂).1 := by
  subst ht
  cases Subtype.ext hP
  cases Subtype.ext hQ
  rfl

noncomputable def restrictPolIso {S : Type u} [CommRing S] {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    {f' : A' ⟶ Spec (CommRingCat.of S)} (k : A' ⟶ A) (hk : k ≫ f = f') (U : (Spec (CommRingCat.of S)).Opens)
    (M M' : A.Modules)
    (e : (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M ≅ (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M') :
    (Scheme.Modules.pullback (f' ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback k).obj M) ≅
      (Scheme.Modules.pullback (f' ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback k).obj M') := by
  have hle : f' ⁻¹ᵁ U ≤ k ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, hk]
  let r := k.resLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ U) hle
  have hr : r ≫ (f ⁻¹ᵁ U).ι = (f' ⁻¹ᵁ U).ι ≫ k := Scheme.Hom.resLE_comp_ι _ _
  refine ((Scheme.Modules.pullbackComp (f' ⁻¹ᵁ U).ι k).app M) ≪≫
    (Scheme.Modules.pullbackCongr hr.symm).app M ≪≫ ((Scheme.Modules.pullbackComp r (f ⁻¹ᵁ U).ι).app M).symm ≪≫
    (Scheme.Modules.pullback r).mapIso e ≪≫ ((Scheme.Modules.pullbackComp r (f ⁻¹ᵁ U).ι).app M') ≪≫
    (Scheme.Modules.pullbackCongr hr).app M' ≪≫ ((Scheme.Modules.pullbackComp (f' ⁻¹ᵁ U).ι k).app M').symm

noncomputable def shrinkPolIso {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    {U U' : (Spec (CommRingCat.of S)).Opens} (hU : U' ≤ U) (M M' : A.Modules)
    (e : (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M ≅ (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M') :
    (Scheme.Modules.pullback (f ⁻¹ᵁ U').ι).obj M ≅ (Scheme.Modules.pullback (f ⁻¹ᵁ U').ι).obj M' := by
  have hle : f ⁻¹ᵁ U' ≤ f ⁻¹ᵁ U := f.preimage_mono hU
  have hι : A.homOfLE hle ≫ (f ⁻¹ᵁ U).ι = (f ⁻¹ᵁ U').ι := Scheme.homOfLE_ι _ _
  refine (Scheme.Modules.pullbackCongr hι.symm).app M ≪≫ ((Scheme.Modules.pullbackComp _ _).app M).symm ≪≫
    (Scheme.Modules.pullback (A.homOfLE hle)).mapIso e ≪≫ ((Scheme.Modules.pullbackComp _ _).app M') ≪≫
    (Scheme.Modules.pullbackCongr hι).app M'

theorem iso_symm {S : Type u} [CommRing S] (X X' : FramedPolarisedAbelianScheme g N n S)
    (h : FramedPolarisedAbelianScheme.Iso X X') : FramedPolarisedAbelianScheme.Iso X' X := by
  obtain ⟨e, he, hproj, hmul, hP, hpol⟩ := h
  have he' : e.inv ≫ X.f = X'.f := by rw [Iso.inv_comp_eq, he]
  refine ⟨e.symm, he', ?_, ?_, ?_, ?_⟩
  · rw [Iso.symm_hom, Iso.inv_comp_eq, hproj]
  · intro T t x y
    have key := hmul t ⟨x.1 ≫ e.symm.hom, by rw [Category.assoc]; erw [he']; exact x.2⟩
      ⟨y.1 ≫ e.symm.hom, by rw [Category.assoc]; erw [he']; exact y.2⟩
    have key' : (X.L.mul t ⟨x.1 ≫ e.symm.hom, by rw [Category.assoc]; erw [he']; exact x.2⟩
        ⟨y.1 ≫ e.symm.hom, by rw [Category.assoc]; erw [he']; exact y.2⟩).1 ≫ e.hom = (X'.L.mul t x y).1 := by
      rw [key]
      apply mul_val_congr X'.L rfl <;> simp
    calc (X'.L.mul t x y).1 ≫ e.symm.hom
        = ((X.L.mul t ⟨x.1 ≫ e.symm.hom, by rw [Category.assoc]; erw [he']; exact x.2⟩
            ⟨y.1 ≫ e.symm.hom, by rw [Category.assoc]; erw [he']; exact y.2⟩).1 ≫ e.hom) ≫ e.symm.hom := by rw [key']
      _ = _ := by simp
  · intro i
    rw [Iso.symm_hom, ← hP i, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · intro p
    obtain ⟨U, hpU, ⟨eU⟩⟩ := hpol p
    refine ⟨U, hpU, ⟨?_⟩⟩
    have r := restrictPolIso e.inv he' U _ _ eU
    refine ?_ ≪≫ r.symm ≪≫ ?_
    · exact Iso.refl _
    · refine ((Scheme.Modules.pullback (X'.f ⁻¹ᵁ U).ι).mapIso ?_)
      exact ((Scheme.Modules.pullbackComp e.inv e.hom).app X'.pol) ≪≫
        (Scheme.Modules.pullbackCongr e.inv_hom_id).app X'.pol ≪≫ (Scheme.Modules.pullbackId X'.A).app X'.pol

theorem iso_trans {S : Type u} [CommRing S] (X X' X'' : FramedPolarisedAbelianScheme g N n S)
    (h : FramedPolarisedAbelianScheme.Iso X X') (h' : FramedPolarisedAbelianScheme.Iso X' X'') :
    FramedPolarisedAbelianScheme.Iso X X'' := by
  obtain ⟨e, he, hproj, hmul, hP, hpol⟩ := h
  obtain ⟨e', he', hproj', hmul', hP', hpol'⟩ := h'
  have hee' : (e ≪≫ e').hom ≫ X''.f = X.f := by rw [Iso.trans_hom, Category.assoc, he', he]
  refine ⟨e ≪≫ e', hee', ?_, ?_, ?_, ?_⟩
  · rw [Iso.trans_hom, Category.assoc, hproj', hproj]
  · intro T t x y
    calc (X.L.mul t x y).1 ≫ (e ≪≫ e').hom = ((X.L.mul t x y).1 ≫ e.hom) ≫ e'.hom := by simp
      _ = _ := by
        rw [hmul t x y, hmul']
        apply mul_val_congr X''.L rfl <;> simp
  · intro i
    rw [Iso.trans_hom, ← Category.assoc, hP i, hP' i]
  · intro p
    obtain ⟨U, hpU, ⟨eU⟩⟩ := hpol p
    obtain ⟨U', hpU', ⟨eU'⟩⟩ := hpol' p
    refine ⟨U ⊓ U', ⟨hpU, hpU'⟩, ⟨?_⟩⟩
    have a := shrinkPolIso (f := X.f) (inf_le_left : U ⊓ U' ≤ U) _ _ eU
    have b := shrinkPolIso (f := X'.f) (inf_le_right : U ⊓ U' ≤ U') _ _ eU'
    have b' := restrictPolIso e.hom he (U ⊓ U') _ _ b
    refine ?_ ≪≫ b' ≪≫ a
    refine (Scheme.Modules.pullback (X.f ⁻¹ᵁ (U ⊓ U')).ι).mapIso ?_
    exact ((Scheme.Modules.pullbackComp e.hom e'.hom).app X''.pol).symm

theorem iso_of_isPullback_of_isPullback {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    (X : FramedPolarisedAbelianScheme g N n S) (Y Y' : FramedPolarisedAbelianScheme g N n S')
    (h : FramedPolarisedAbelianScheme.IsPullback φ X Y) (h' : FramedPolarisedAbelianScheme.IsPullback φ X Y') :
    FramedPolarisedAbelianScheme.Iso Y Y' := by
  letI : Algebra S S' := φ.toAlgebra
  obtain ⟨gY, hg, hmul, hP, ⟨eY⟩, hproj⟩ := h
  obtain ⟨gY', hg', hmul', hP', ⟨eY'⟩, hproj'⟩ := h'

  let eh : Y.A ⟶ Y'.A := hg'.lift gY Y.f hg.w
  let ei : Y'.A ⟶ Y.A := hg.lift gY' Y'.f hg'.w
  have eh_g : eh ≫ gY' = gY := hg'.lift_fst _ _ _
  have eh_f : eh ≫ Y'.f = Y.f := hg'.lift_snd _ _ _
  have ei_g : ei ≫ gY = gY' := hg.lift_fst _ _ _
  have ei_f : ei ≫ Y.f = Y'.f := hg.lift_snd _ _ _
  let e : Y.A ≅ Y'.A :=
    { hom := eh, inv := ei,
      hom_inv_id := by
        apply hg.hom_ext
        · rw [Category.assoc, ei_g, eh_g, Category.id_comp]
        · rw [Category.assoc, ei_f, eh_f, Category.id_comp]
      inv_hom_id := by
        apply hg'.hom_ext
        · rw [Category.assoc, eh_g, ei_g, Category.id_comp]
        · rw [Category.assoc, eh_f, ei_f, Category.id_comp] }
  have ehom : e.hom = eh := rfl
  have eh_g' : e.hom ≫ gY' = gY := eh_g
  have eh_f' : e.hom ≫ Y'.f = Y.f := eh_f
  refine ⟨e, eh_f, ?_, ?_, ?_, ?_⟩
  ·
    apply (ProjSpace.isPullback_map S S' N).hom_ext
    · rw [Category.assoc, hproj', ← Category.assoc, ehom, eh_g, hproj]
    · rw [Category.assoc, Y'.frame.toProj_π, Y.frame.toProj_π, ehom, eh_f]
  · intro T t x y
    apply hg'.hom_ext
    · rw [Category.assoc, eh_g', hmul t x y, hmul']
      apply mul_val_congr X.L rfl
      · simp only [Category.assoc, eh_g']
      · simp only [Category.assoc, eh_g']
    · rw [Category.assoc, eh_f', (Y.L.mul t x y).2, (Y'.L.mul t _ _).2]
  · intro i
    apply hg'.hom_ext
    · rw [Category.assoc, ehom, eh_g, hP i, hP' i]
    · rw [Category.assoc, ehom, eh_f, (Y.P i).2, (Y'.P i).2]
  · intro p
    refine ⟨⊤, trivial, ⟨(Scheme.Modules.pullback (Y.f ⁻¹ᵁ ⊤).ι).mapIso ?_⟩⟩
    exact (Scheme.Modules.pullback e.hom).mapIso eY'.symm ≪≫ (Scheme.Modules.pullbackComp e.hom gY').app X.pol ≪≫
      (Scheme.Modules.pullbackCongr (by rw [ehom, eh_g] : e.hom ≫ gY' = gY)).app X.pol ≪≫ eY

end FramedIso31

end

theorem solution
    {g N n : ℕ} {S : Type} [CommRing S] (X X' : FramedPolarisedAbelianScheme g N n S)
    (h : FramedPolarisedAbelianScheme.Iso X X') : FramedPolarisedAbelianScheme.Iso X' X :=
  FramedIso31.iso_symm X X' h

end S_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_symm
end P2MW
export P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_symm (solution)
