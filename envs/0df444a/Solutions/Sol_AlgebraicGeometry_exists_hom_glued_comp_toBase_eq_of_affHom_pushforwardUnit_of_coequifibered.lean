-- Prove2me | solution 1 for AlgebraicGeometry.exists_hom_glued_comp_toBase_eq_of_affHom_pushforwardUnit_of_coequifibered
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/4a05441a-8d45-55e7-8a69-6a37e22affe7

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_exists_coequifibered_iso_glued_comp_toBase_eq_of_isAffineHom
import Theorems.Thm_AlgebraicGeometry_Scheme_AffineZariskiSite_exists_hom_glued_comp_toBase_eq_of_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_hom_glued_comp_toBase_eq_of_affHom_pushforwardUnit_of_coequifibered

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]

    (sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))))
    (tR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1 + 1))))
    (htR : ∀ n : ℕ, tR n ≫ sR (n + 1) = sR n)

    (xn : ∀ n : ℕ, Limits.pullback f (sR n) ⟶ Limits.pullback f (sR (n + 1)))
    (hxn₁ : ∀ n : ℕ, xn n ≫ Limits.pullback.fst f (sR (n + 1)) = Limits.pullback.fst f (sR n))
    (hxn₂ : ∀ n : ℕ, xn n ≫ Limits.pullback.snd f (sR (n + 1)) = Limits.pullback.snd f (sR n) ≫ tR n)

    (Y : ℕ → Scheme.{u}) (g : ∀ n : ℕ, Y n ⟶ Limits.pullback f (sR n)) [∀ n : ℕ, IsFinite (g n)]
    (yn : ∀ n : ℕ, Y n ⟶ Y (n + 1))
    (hY : ∀ n : ℕ, IsPullback (yn n) (g n) (g (n + 1)) (xn n))

    (F : OModulePresheaf f)
    (ψ : ∀ n : ℕ, OModulePresheaf.AffHom F (OModulePresheaf.pushforwardUnit f (g n ≫ pullback.fst f (sR n))))
    (hψc : ∀ (n : ℕ) (U : X.affineOpens) (x : F.obj U.1),
      (ψ n).app U x =
        ((yn n).appLE ((g (n + 1) ≫ pullback.fst f (sR (n + 1))) ⁻¹ᵁ U.1) ((g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.1)
          (by rw [← Scheme.Hom.comp_preimage, ← Category.assoc, (hY n).w, Category.assoc, hxn₁])).hom
          ((ψ (n + 1)).app U x))

    (A : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u})
    (α : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ A) (Hco : α.Coequifibered)
    (e : ∀ U : X.AffineZariskiSite, A.obj (op U) ≃+ F.obj U.1)
    (hlin : ∀ (U : X.AffineZariskiSite) (a : Γ(X, U.1)) (x : A.obj (op U)),
      e U ((α.app (op U)).hom a * x) = a • e U x)
    (hnat : ∀ (U V : X.AffineZariskiSite) (i : V ⟶ U) (x : A.obj (op U)),
      e V ((A.map i.op).hom x) = F.res (Scheme.AffineZariskiSite.toOpens_mono i.le) (e U x))
    (r : ∀ (n : ℕ) (U : X.AffineZariskiSite), A.obj (op U) →+* Γ(Y n, (g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.1))
    (hr : ∀ (n : ℕ) (U : X.AffineZariskiSite) (x : A.obj (op U)), r n U x = (ψ n).app ⟨U.1, U.2⟩ (e U x)) :
    ∃ φ : ∀ n : ℕ, Y n ⟶ (Scheme.AffineZariskiSite.relativeGluingData Hco).glued,
      (∀ n : ℕ, φ n ≫ (Scheme.AffineZariskiSite.relativeGluingData Hco).toBase = g n ≫ pullback.fst f (sR n)) ∧
      (∀ n : ℕ, yn n ≫ φ (n + 1) = φ n) ∧
      (∀ (n : ℕ) (U : X.AffineZariskiSite),
        ((g n) ⁻¹ᵁ ((pullback.fst f (sR n)) ⁻¹ᵁ U.1)).ι ≫ φ n =
          ((g n) ⁻¹ᵁ ((pullback.fst f (sR n)) ⁻¹ᵁ U.1)).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (r n U)) ≫
            (Scheme.AffineZariskiSite.relativeGluingData Hco).cover.f U) := by
  classical
  let D := Scheme.AffineZariskiSite.relativeGluingData Hco
  haveI : (D.functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

  have hci : ∀ n : ℕ, IsClosedImmersion (sR n) := fun n => by
    rw [hsR]; exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hfst : ∀ n : ℕ, IsClosedImmersion (pullback.fst f (sR n)) := fun n => by
    haveI := hci n; exact MorphismProperty.pullback_fst _ _ inferInstance
  haveI haff : ∀ n : ℕ, IsAffineHom (g n ≫ pullback.fst f (sR n)) := fun n => by haveI := hfst n; infer_instance
  have hyf : ∀ n : ℕ, yn n ≫ (g (n + 1) ≫ pullback.fst f (sR (n + 1))) = (g n ≫ pullback.fst f (sR n)) := fun n => by
    rw [← Category.assoc, (hY n).w, Category.assoc, hxn₁]

  have step_a := fun n : ℕ =>
    AlgebraicGeometry.Scheme.Hom.exists_coequifibered_iso_glued_comp_toBase_eq_of_isAffineHom (g n ≫ pullback.fst f (sR n))
  choose H₁ e₁ he₁ hloc₁ using step_a

  let β : ∀ n : ℕ, (A ⟶ (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ ((g n ≫ pullback.fst f (sR n)).base _* (Y n).presheaf)) := fun n =>
    { app := fun U => CommRingCat.ofHom (r n U.unop)
      naturality := fun U W i => by
        ext x
        change r n W.unop ((A.map i).hom x) = ((Y n).presheaf.map _).hom (r n U.unop x)
        rw [hr, hr]
        erw [hnat U.unop W.unop i.unop x]
        have nat := LinearMap.congr_fun ((ψ n).naturality (U := ⟨W.unop.1, W.unop.2⟩) (U' := ⟨U.unop.1, U.unop.2⟩)
          (Scheme.AffineZariskiSite.toOpens_mono i.unop.le)) (e U.unop x)
        simp only [LinearMap.coe_comp, Function.comp_apply] at nat
        rw [nat, ← hr]
        rfl }
  have hβ : ∀ n : ℕ, α ≫ β n = (Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft (g n ≫ pullback.fst f (sR n)).c := by
    intro n
    ext U a
    change r n U.unop ((α.app U).hom a) = ((g n ≫ pullback.fst f (sR n)).c.app (op U.unop.1)).hom a
    rw [hr, ← mul_one ((α.app U).hom a)]
    erw [hlin U.unop a 1, (ψ n).app_smul]
    rw [← hr, map_one]
    change (Scheme.Hom.appLE (g n ≫ pullback.fst f (sR n)) U.unop.1 ((g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.unop.1) le_rfl).hom a * 1 = _
    rw [mul_one, Scheme.Hom.appLE_eq_app]

  have step_c := fun n : ℕ =>
    AlgebraicGeometry.Scheme.AffineZariskiSite.exists_hom_glued_comp_toBase_eq_of_comp_eq (H₁ n) Hco (β n) (hβ n)
  choose φ' hφ'₁ hφ'₂ huniq hiso using step_c

  have key : ∀ (n : ℕ) (U : X.AffineZariskiSite),
      ((g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.1).ι ≫ (e₁ n).hom ≫ φ' n = ((g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map ((β n).app (op U)) ≫ D.cover.f U := by
    intro n U
    rw [← Category.assoc, hloc₁ n U]
    erw [Category.assoc, hφ'₂ n U]
    rfl
  refine ⟨fun n => (e₁ n).hom ≫ φ' n, fun n => ?_, fun n => ?_, fun n U => ?_⟩
  ·
    rw [Category.assoc, hφ'₁, he₁]
  ·
    suffices h : (e₁ n).inv ≫ yn n ≫ (e₁ (n + 1)).hom ≫ φ' (n + 1) = φ' n by
      show yn n ≫ (e₁ (n + 1)).hom ≫ φ' (n + 1) = (e₁ n).hom ≫ φ' n
      rw [← h, Iso.hom_inv_id_assoc]
    apply huniq n
    intro U
    have hV : IsAffineOpen ((g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.1) := U.2.preimage _
    have hV' : IsAffineOpen ((g (n + 1) ≫ pullback.fst f (sR (n + 1))) ⁻¹ᵁ U.1) := U.2.preimage _
    have hle : ((g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.1) ≤ (yn n) ⁻¹ᵁ ((g (n + 1) ≫ pullback.fst f (sR (n + 1))) ⁻¹ᵁ U.1) :=
      le_of_eq (by rw [← Scheme.Hom.comp_preimage, hyf])

    have hc : (Scheme.AffineZariskiSite.relativeGluingData (H₁ n)).cover.f U ≫ (e₁ n).inv = hV.fromSpec := by
      have h1 : hV.isoSpec.inv ≫ (((g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.1).ι ≫ (e₁ n).hom) = (Scheme.AffineZariskiSite.relativeGluingData (H₁ n)).cover.f U :=
        (Iso.inv_comp_eq _).mpr (hloc₁ n U)
      rw [← h1]
      exact (show (hV.isoSpec.inv ≫ ((g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.1).ι ≫ (e₁ n).hom) ≫ (e₁ n).inv = hV.isoSpec.inv ≫ ((g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.1).ι by simp)
    have k'' : hV'.fromSpec ≫ (e₁ (n + 1)).hom ≫ φ' (n + 1) = Spec.map ((β (n + 1)).app (op U)) ≫ D.cover.f U := by
      rw [← IsAffineOpen.isoSpec_inv_ι hV', Category.assoc, key (n + 1) U, ← IsAffineOpen.isoSpec_hom hV',
        Iso.inv_hom_id_assoc]
      try rfl
    have hrr : (β (n + 1)).app (op U) ≫ (yn n).appLE _ _ hle = (β n).app (op U) := by
      ext x
      change ((yn n).appLE _ _ hle).hom (r (n + 1) U x) = r n U x
      rw [hr, hr, hψc n ⟨U.1, U.2⟩ (e U x)]
    rw [← Category.assoc, hc]
    change hV.fromSpec ≫ yn n ≫ (e₁ (n + 1)).hom ≫ φ' (n + 1) = Spec.map ((β n).app (op U)) ≫ D.cover.f U
    rw [← Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec (yn n) hV' hV hle, Category.assoc, k'',
      ← hrr]
    have smc : ∀ {R₁ R₂ R₃ : CommRingCat.{u}} (a : R₁ ⟶ R₂) (b : R₂ ⟶ R₃) {W : Scheme.{u}} (c : Spec R₁ ⟶ W),
        Spec.map b ≫ Spec.map a ≫ c = Spec.map (a ≫ b) ≫ c := by
      intros; rw [Spec.map_comp, Category.assoc]
    exact smc _ _ _
  ·
    exact key n U

end S_AlgebraicGeometry_exists_hom_glued_comp_toBase_eq_of_affHom_pushforwardUnit_of_coequifibered
end P2MW
export P2MW.S_AlgebraicGeometry_exists_hom_glued_comp_toBase_eq_of_affHom_pushforwardUnit_of_coequifibered (solution)
