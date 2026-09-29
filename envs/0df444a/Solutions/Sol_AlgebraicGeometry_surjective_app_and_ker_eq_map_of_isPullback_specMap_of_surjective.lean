-- Prove2me | solution 1 for AlgebraicGeometry.surjective_app_and_ker_eq_map_of_isPullback_specMap_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/12bb3c25-eaa4-54b2-9698-ac666683554f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_surjective_app_and_ker_eq_map_of_isPullback_specMap_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace EDaux

theorem isPushout_appTop_of_isPullback {P X Y Z : Scheme.{u}} [IsAffine P] [IsAffine X] [IsAffine Y] [IsAffine Z]
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (H : IsPullback fst snd f g) :
    IsPushout g.appTop f.appTop snd.appTop fst.appTop := by
  haveI : ∀ i : WalkingCospan, IsAffine ((cospan f g).obj i) := fun i => by
    rcases i with _ | _ | _
    · change IsAffine Z; infer_instance
    · change IsAffine X; infer_instance
    · change IsAffine Y; infer_instance
  have H' := H.map Scheme.Γ.rightOp
  exact H'.unop

theorem isPushout_appLE_of_isPullback {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {iX : X ⟶ S} {iY : Y ⟶ T}
    (H : IsPullback g iY iX f)
    {US : S.Opens} (hUS : IsAffineOpen US) {UT : T.Opens} (hUT : IsAffineOpen UT)
    {UX : X.Opens} (hUX : IsAffineOpen UX) {UY : Y.Opens} (hUY' : IsAffineOpen UY)
    (hUST : UT ≤ f ⁻¹ᵁ US) (hUSX : UX ≤ iX ⁻¹ᵁ US) (hUY : UY = g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT)
    (eg : UY ≤ g ⁻¹ᵁ UX) (eY : UY ≤ iY ⁻¹ᵁ UT) :
    IsPushout (f.appLE US UT hUST) (iX.appLE US UX hUSX) (iY.appLE UT UY eY) (g.appLE UX UY eg) := by
  have H1 := Scheme.Hom.isPullback_resLE H hUST hUSX hUY
  haveI : IsAffine (US : Scheme.{u}) := hUS
  haveI : IsAffine (UT : Scheme.{u}) := hUT
  haveI : IsAffine (UX : Scheme.{u}) := hUX
  haveI : IsAffine (UY : Scheme.{u}) := hUY'
  have H2 := isPushout_appTop_of_isPullback H1
  refine H2.of_iso US.topIso UT.topIso UX.topIso UY.topIso ?_ ?_ ?_ ?_
  all_goals
    dsimp only [Scheme.Hom.appTop]
    rw [Scheme.Hom.resLE_app_top]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem surjective_and_ker_eq_of_isPushout {R S A B : CommRingCat.{u}} {f : R ⟶ S} {g : R ⟶ A} {inl : S ⟶ B} {inr : A ⟶ B}
    (h : IsPushout f g inl inr) (hf : Function.Surjective f.hom) :
    Function.Surjective inr.hom ∧ RingHom.ker inr.hom = (RingHom.ker f.hom).map g.hom := by
  classical
  set I : Ideal A := (RingHom.ker f.hom).map g.hom with hIdef
  have hw : ∀ r : R, inl.hom (f.hom r) = inr.hom (g.hom r) := fun r => by
    have := congrArg (fun k => k.hom r) h.w
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using this
  have hI : ∀ a ∈ I, inr.hom a = 0 := by
    have : I ≤ RingHom.ker inr.hom := by
      rw [hIdef, Ideal.map_le_iff_le_comap]
      intro r hr
      rw [RingHom.mem_ker] at hr
      rw [Ideal.mem_comap, RingHom.mem_ker, ← hw, hr, map_zero]
    exact fun a ha => this ha

  let v : A ⧸ I →+* B := Ideal.Quotient.lift I inr.hom hI

  let r₀ : R →+* A ⧸ I := (Ideal.Quotient.mk I).comp g.hom
  have hr₀ : ∀ x ∈ RingHom.ker f.hom, r₀ x = 0 := fun x hx => by
    show Ideal.Quotient.mk I (g.hom x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, hIdef]
    exact Ideal.mem_map_of_mem _ hx
  let r : S →+* A ⧸ I :=
    (Ideal.Quotient.lift (RingHom.ker f.hom) r₀ hr₀).comp (RingHom.quotientKerEquivOfSurjective hf).symm.toRingHom
  have hr : ∀ x : R, r (f.hom x) = Ideal.Quotient.mk I (g.hom x) := fun x => by
    show Ideal.Quotient.lift (RingHom.ker f.hom) r₀ hr₀ ((RingHom.quotientKerEquivOfSurjective hf).symm (f.hom x)) = _
    rw [RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.Quotient.lift_mk]
    rfl

  have hcomm : f ≫ CommRingCat.ofHom r = g ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) := by
    ext x
    simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] using hr x
  let u : B ⟶ CommRingCat.of (A ⧸ I) := h.desc (CommRingCat.ofHom r) (CommRingCat.ofHom (Ideal.Quotient.mk I)) hcomm
  have hu_inr : ∀ a : A, u.hom (inr.hom a) = Ideal.Quotient.mk I a := fun a => by
    have := congrArg (fun k => k.hom a) (h.inr_desc (CommRingCat.ofHom r) (CommRingCat.ofHom (Ideal.Quotient.mk I)) hcomm)
    simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] using this
  have hu_inl : ∀ s : S, u.hom (inl.hom s) = r s := fun s => by
    have := congrArg (fun k => k.hom s) (h.inl_desc (CommRingCat.ofHom r) (CommRingCat.ofHom (Ideal.Quotient.mk I)) hcomm)
    simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] using this

  have hvu : u ≫ CommRingCat.ofHom v = 𝟙 B := by
    apply h.hom_ext
    · ext s
      obtain ⟨x, rfl⟩ := hf s
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, Category.comp_id]
      rw [hu_inl, hr, Ideal.Quotient.lift_mk, ← hw]
    · ext a
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, Category.comp_id]
      rw [hu_inr, Ideal.Quotient.lift_mk]
  have hvu' : ∀ b : B, v (u.hom b) = b := fun b => by
    have := congrArg (fun k => k.hom b) hvu
    simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] using this
  refine ⟨fun b => ?_, ?_⟩
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u.hom b)
    refine ⟨a, ?_⟩
    rw [← hvu' b, ← ha, Ideal.Quotient.lift_mk]
  · apply le_antisymm
    · intro x hx
      rw [RingHom.mem_ker] at hx
      have : Ideal.Quotient.mk I x = 0 := by rw [← hu_inr, hx, map_zero]
      rwa [Ideal.Quotient.eq_zero_iff_mem] at this
    · exact fun a ha => (RingHom.mem_ker).2 (hI a ha)

end EDaux

open EDaux in
theorem solution
    {A A' : CommRingCat.{u}} (φ : A ⟶ A') (hφ : Function.Surjective φ.hom)
    {Y Y' : Scheme.{u}} {g : Y' ⟶ Y} {iY : Y ⟶ Spec A} {iY' : Y' ⟶ Spec A'}
    (H : IsPullback g iY' iY (Spec.map φ))
    (W : Y.Opens) (hW : IsAffineOpen W) :
    Function.Surjective (g.app W).hom ∧
      RingHom.ker (g.app W).hom = Ideal.map ((Scheme.ΓSpecIso A).inv ≫ iY.appLE ⊤ W le_top).hom (RingHom.ker φ.hom) := by
  classical

  haveI : IsAffineHom (Spec.map φ) := inferInstance
  haveI hg : IsAffineHom g := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  have hW' : IsAffineOpen (g ⁻¹ᵁ W) := hW.preimage g

  have H1 : IsPushout ((Spec.map φ).appLE ⊤ ⊤ le_top) (iY.appLE ⊤ W le_top) (iY'.appLE ⊤ (g ⁻¹ᵁ W) le_top)
      (g.appLE W (g ⁻¹ᵁ W) le_rfl) :=
    isPushout_appLE_of_isPullback H (isAffineOpen_top _) (isAffineOpen_top _) hW hW' le_top le_top (by simp) le_rfl le_top
  have H2 : IsPushout φ ((Scheme.ΓSpecIso A).inv ≫ iY.appLE ⊤ W le_top)
      ((Scheme.ΓSpecIso A').inv ≫ iY'.appLE ⊤ (g ⁻¹ᵁ W) le_top) (g.appLE W (g ⁻¹ᵁ W) le_rfl) := by
    refine H1.of_iso (Scheme.ΓSpecIso A) (Scheme.ΓSpecIso A') (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · have htop : (Spec.map φ).appLE ⊤ ⊤ le_top = (Spec.map φ).appTop := by
        rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; congr 1
      rw [htop, Scheme.ΓSpecIso_naturality]
    · simp
    · simp
    · simp
  obtain ⟨hsurj, hker⟩ := surjective_and_ker_eq_of_isPushout H2 hφ
  rw [Scheme.Hom.app_eq_appLE]
  exact ⟨hsurj, hker⟩

end S_AlgebraicGeometry_surjective_app_and_ker_eq_map_of_isPullback_specMap_of_surjective
end P2MW
export P2MW.S_AlgebraicGeometry_surjective_app_and_ker_eq_map_of_isPullback_specMap_of_surjective (solution)
