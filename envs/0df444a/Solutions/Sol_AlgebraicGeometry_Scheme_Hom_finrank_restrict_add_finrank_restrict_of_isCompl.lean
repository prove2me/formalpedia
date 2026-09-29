-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.finrank_restrict_add_finrank_restrict_of_isCompl
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/1e78cfd7-746d-5584-9fd7-29ab12c0cb54

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_finrank_restrict_add_finrank_restrict_of_isCompl

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace E160RC

open TopologicalSpace Opposite

theorem finrank_add_of_bijective_prod {R A A₁ A₂ : Type*} [CommRing R] [CommRing A]
    [CommRing A₁] [CommRing A₂] (φ : R →+* A) (r₁ : A →+* A₁) (r₂ : A →+* A₂)
    (hbij : Function.Bijective (RingHom.prod r₁ r₂))
    (h₁fin : (r₁.comp φ).Finite) (h₁flat : (r₁.comp φ).Flat)
    (h₂fin : (r₂.comp φ).Finite) (h₂flat : (r₂.comp φ).Flat) (x : PrimeSpectrum R) :
    (r₁.comp φ).finrank x + (r₂.comp φ).finrank x = φ.finrank x := by
  letI iA : Algebra R A := φ.toAlgebra
  letI i₁ : Algebra R A₁ := (r₁.comp φ).toAlgebra
  letI i₂ : Algebra R A₂ := (r₂.comp φ).toAlgebra
  haveI : Module.Finite R A₁ := h₁fin
  haveI : Module.Flat R A₁ := h₁flat
  haveI : Module.Finite R A₂ := h₂fin
  haveI : Module.Flat R A₂ := h₂flat
  let e : A ≃ₗ[R] A₁ × A₂ :=
    { toFun := fun a => (r₁ a, r₂ a)
      map_add' := fun a b => by simp
      map_smul' := fun c a => by
        ext
        · change r₁ (φ c * a) = (r₁.comp φ) c * r₁ a
          rw [map_mul]; rfl
        · change r₂ (φ c * a) = (r₂.comp φ) c * r₂ a
          rw [map_mul]; rfl
      invFun := fun p => (Equiv.ofBijective _ hbij).symm p
      left_inv := fun a => (Equiv.ofBijective _ hbij).left_inv a
      right_inv := fun p => (Equiv.ofBijective _ hbij).right_inv p }
  change Module.rankAtStalk A₁ x + Module.rankAtStalk A₂ x = Module.rankAtStalk A x
  rw [Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_prod]
  rfl

theorem bijective_restrict_prod {X : Scheme.{u}} (U V : X.Opens) (hUV : U ⊔ V = ⊤) (hdisj : U ⊓ V = ⊥) :
    Function.Bijective (RingHom.prod (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
      (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom) := by
  have hnot : ∀ x : X, x ∉ U ⊓ V := by
    intro x hx; rw [hdisj] at hx; exact hx
  constructor
  · intro a b hab
    have h1 : X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op b :=
      congrArg Prod.fst hab
    have h2 : X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op a = X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op b :=
      congrArg Prod.snd hab
    apply TopCat.Presheaf.section_ext X.sheaf ⊤ a b
    intro x hx
    have hx' : x ∈ U ⊔ V := by rw [hUV]; trivial
    rcases hx' with hU | hV
    · have ha := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (le_top : U ≤ ⊤)) x hU a
      have hb := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (le_top : U ≤ ⊤)) x hU b
      change X.presheaf.germ ⊤ x _ a = X.presheaf.germ ⊤ x _ b
      rw [← ha, ← hb, h1]
    · have ha := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (le_top : V ≤ ⊤)) x hV a
      have hb := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (le_top : V ≤ ⊤)) x hV b
      change X.presheaf.germ ⊤ x _ a = X.presheaf.germ ⊤ x _ b
      rw [← ha, ← hb, h2]
  · rintro ⟨b, c⟩
    let p : RingHom.eqLocus
        (RingHom.comp (X.sheaf.obj.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op).hom
          (RingHom.fst (X.sheaf.obj.obj <| op U) (X.sheaf.obj.obj <| op V)))
        (RingHom.comp (X.sheaf.obj.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op).hom
          (RingHom.snd (X.sheaf.obj.obj <| op U) (X.sheaf.obj.obj <| op V))) :=
      ⟨(b, c), TopCat.Presheaf.section_ext X.sheaf (U ⊓ V) _ _ (fun x hx => absurd hx (hnot x))⟩
    let s : X.presheaf.obj (op (U ⊔ V)) := (X.sheaf.objSupIsoProdEqLocus U V).inv p
    have hsU : X.presheaf.map (homOfLE (le_sup_left : U ≤ U ⊔ V)).op s = b :=
      TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst X.sheaf U V p
    have hsV : X.presheaf.map (homOfLE (le_sup_right : V ≤ U ⊔ V)).op s = c :=
      TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd X.sheaf U V p
    have htop : (⊤ : X.Opens) ≤ U ⊔ V := hUV.symm.le
    refine ⟨X.presheaf.map (homOfLE htop).op s, ?_⟩
    ext
    · change X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (X.presheaf.map (homOfLE htop).op s) = b
      rw [← CategoryTheory.comp_apply, ← X.presheaf.map_comp, ← op_comp]
      have : homOfLE (le_top : U ≤ ⊤) ≫ homOfLE htop = homOfLE (le_sup_left : U ≤ U ⊔ V) :=
        Subsingleton.elim _ _
      rw [this, hsU]
    · change X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (X.presheaf.map (homOfLE htop).op s) = c
      rw [← CategoryTheory.comp_apply, ← X.presheaf.map_comp, ← op_comp]
      have : homOfLE (le_top : V ≤ ⊤) ≫ homOfLE htop = homOfLE (le_sup_right : V ≤ U ⊔ V) :=
        Subsingleton.elim _ _
      rw [this, hsV]

theorem finrank_eq_finrank_appTop {R : CommRingCat.{u}} {Z : Scheme.{u}} [IsAffine Z]
    (k : Z ⟶ Spec R) [IsFinite k] [Flat k] (x : Spec R) :
    k.finrank x = ((Scheme.ΓSpecIso R).inv ≫ k.appTop).hom.finrank x := by
  have hk : k = Z.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ k.appTop) := by
    rw [Spec.map_comp, ← Category.assoc]
    change k = (Z.toSpecΓ ≫ Spec.map k.appTop) ≫ Spec.map (Scheme.ΓSpecIso R).inv
    rw [← Scheme.toSpecΓ_naturality, Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]
  have hk' : Spec.map ((Scheme.ΓSpecIso R).inv ≫ k.appTop) = Z.isoSpec.inv ≫ k :=
    (Iso.eq_inv_comp Z.isoSpec).mpr hk.symm
  haveI : IsFinite (Spec.map ((Scheme.ΓSpecIso R).inv ≫ k.appTop)) := by rw [hk']; infer_instance
  haveI : Flat (Spec.map ((Scheme.ΓSpecIso R).inv ≫ k.appTop)) := by rw [hk']; infer_instance
  have h1 : ((Scheme.ΓSpecIso R).inv ≫ k.appTop).hom.Finite := (IsFinite.SpecMap_iff _).mp inferInstance
  have h2 : ((Scheme.ΓSpecIso R).inv ≫ k.appTop).hom.Flat := Flat.SpecMap_iff.mp inferInstance
  conv_lhs => rw [hk]
  rw [Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_eq_finrank h1 h2]

theorem finrank_add_affine {R : CommRingCat.{u}} {Y : Scheme.{u}} (h : Y ⟶ Spec R)
    [IsFinite h] [Flat h] [LocallyOfFinitePresentation h]
    (U V : Y.Opens) (hUV : U ⊔ V = ⊤) (hdisj : U ⊓ V = ⊥) (x : Spec R) :
    (U.ι ≫ h).finrank x + (V.ι ≫ h).finrank x = h.finrank x := by
  haveI : IsAffine Y := isAffine_of_isAffineHom h

  have hUc : IsClosed (U : Set Y) := by
    have : (U : Set Y) = (V : Set Y)ᶜ := by
      ext y; constructor
      · intro hy hy'; have : y ∈ U ⊓ V := ⟨hy, hy'⟩; rw [hdisj] at this; exact this
      · intro hy; have : y ∈ U ⊔ V := by rw [hUV]; trivial
        rcases this with h | h; exact h; exact absurd h hy
    rw [this, isClosed_compl_iff]; exact V.isOpen
  have hVc : IsClosed (V : Set Y) := by
    have : (V : Set Y) = (U : Set Y)ᶜ := by
      ext y; constructor
      · intro hy hy'; have : y ∈ U ⊓ V := ⟨hy', hy⟩; rw [hdisj] at this; exact this
      · intro hy; have : y ∈ U ⊔ V := by rw [hUV]; trivial
        rcases this with h | h; exact absurd h hy; exact h
    rw [this, isClosed_compl_iff]; exact U.isOpen
  haveI : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hUc)
  haveI : IsClosedImmersion V.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hVc)
  haveI : IsAffine (U : Scheme.{u}) := isAffine_of_isAffineHom (U.ι ≫ h)
  haveI : IsAffine (V : Scheme.{u}) := isAffine_of_isAffineHom (V.ι ≫ h)
  rw [finrank_eq_finrank_appTop h, finrank_eq_finrank_appTop (U.ι ≫ h),
    finrank_eq_finrank_appTop (V.ι ≫ h)]

  set φ : R →+* Γ(Y, ⊤) := ((Scheme.ΓSpecIso R).inv ≫ h.appTop).hom with hφ
  have hU' : ((Scheme.ΓSpecIso R).inv ≫ (U.ι ≫ h).appTop).hom = U.ι.appTop.hom.comp φ := rfl
  have hV' : ((Scheme.ΓSpecIso R).inv ≫ (V.ι ≫ h).appTop).hom = V.ι.appTop.hom.comp φ := rfl
  rw [hU', hV']

  have hsurj : Function.Surjective (Scheme.ΓSpecIso R).inv.hom := by
    intro y; refine ⟨(Scheme.ΓSpecIso R).hom y, ?_⟩
    change ((Scheme.ΓSpecIso R).hom ≫ (Scheme.ΓSpecIso R).inv) y = y
    rw [Iso.hom_inv_id]; rfl
  have hbijι : Function.Bijective (Scheme.ΓSpecIso R).inv.hom :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv
  have h₁fin : (U.ι.appTop.hom.comp φ).Finite := by
    rw [← hU']; exact ((U.ι ≫ h).finite_appTop).comp (RingHom.Finite.of_surjective _ hsurj)
  have h₁flat : (U.ι.appTop.hom.comp φ).Flat := by
    rw [← hU']; exact (RingHom.Flat.of_bijective hbijι).comp (U.ι ≫ h).flat_appTop
  have h₂fin : (V.ι.appTop.hom.comp φ).Finite := by
    rw [← hV']; exact ((V.ι ≫ h).finite_appTop).comp (RingHom.Finite.of_surjective _ hsurj)
  have h₂flat : (V.ι.appTop.hom.comp φ).Flat := by
    rw [← hV']; exact (RingHom.Flat.of_bijective hbijι).comp (V.ι ≫ h).flat_appTop

  have hbij : Function.Bijective (RingHom.prod U.ι.appTop.hom V.ι.appTop.hom) := by
    have hUV' : (U.ι ''ᵁ ⊤) ⊔ (V.ι ''ᵁ ⊤) = ⊤ := by rw [Scheme.Opens.ι_image_top, Scheme.Opens.ι_image_top, hUV]
    have hdisj' : (U.ι ''ᵁ ⊤) ⊓ (V.ι ''ᵁ ⊤) = ⊥ := by rw [Scheme.Opens.ι_image_top, Scheme.Opens.ι_image_top, hdisj]
    exact bijective_restrict_prod (U.ι ''ᵁ ⊤) (V.ι ''ᵁ ⊤) hUV' hdisj'
  exact finrank_add_of_bijective_prod φ U.ι.appTop.hom V.ι.appTop.hom hbij h₁fin h₁flat h₂fin h₂flat x

end E160RC

theorem solution
    {Y S : Scheme.{u}} (f : Y ⟶ S) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    (U V : Y.Opens) (hUV : U ⊔ V = ⊤) (hdisj : U ⊓ V = ⊥) (s : S) :
    (U.ι ≫ f).finrank s + (V.ι ≫ f).finrank s = f.finrank s := by

  have hUc : IsClosed (U : Set Y) := by
    have : (U : Set Y) = (V : Set Y)ᶜ := by
      ext y; constructor
      · intro hy hy'; have : y ∈ U ⊓ V := ⟨hy, hy'⟩; rw [hdisj] at this; exact this
      · intro hy; have : y ∈ U ⊔ V := by rw [hUV]; trivial
        rcases this with h | h; exact h; exact absurd h hy
    rw [this, isClosed_compl_iff]; exact V.isOpen
  have hVc : IsClosed (V : Set Y) := by
    have : (V : Set Y) = (U : Set Y)ᶜ := by
      ext y; constructor
      · intro hy hy'; have : y ∈ U ⊓ V := ⟨hy', hy⟩; rw [hdisj] at this; exact this
      · intro hy; have : y ∈ U ⊔ V := by rw [hUV]; trivial
        rcases this with h | h; exact absurd h hy; exact h
    rw [this, isClosed_compl_iff]; exact U.isOpen
  haveI : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hUc)
  haveI : IsClosedImmersion V.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hVc)

  obtain ⟨R, g, hg, s', rfl⟩ := S.exists_Spec_apply_eq s
  have sqY : IsPullback (pullback.fst f g) (pullback.snd f g) f g := IsPullback.of_hasPullback f g
  have sqU := (isPullback_morphismRestrict (pullback.fst f g) U).paste_vert sqY
  have sqV := (isPullback_morphismRestrict (pullback.fst f g) V).paste_vert sqY
  rw [← Scheme.Hom.finrank_of_isPullback _ _ _ _ sqY s',
    ← Scheme.Hom.finrank_of_isPullback _ _ _ _ sqU s',
    ← Scheme.Hom.finrank_of_isPullback _ _ _ _ sqV s']
  apply E160RC.finrank_add_affine (pullback.snd f g)
  · rw [← Scheme.Hom.preimage_sup, hUV]; rfl
  · rw [← Scheme.Hom.preimage_inf, hdisj]; rfl

end S_AlgebraicGeometry_Scheme_Hom_finrank_restrict_add_finrank_restrict_of_isCompl
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_finrank_restrict_add_finrank_restrict_of_isCompl (solution)
