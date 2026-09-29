-- Prove2me | solution 1 for AlgebraicGeometry.tilde.pullback_map_pullbackSpecIso_hom_comp_pullbackSpecIso_hom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/2f32f5c8-c5b4-5e29-83ab-e118609b89f8

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesTildePullback
import Theorems.Thm_AlgebraicGeometry_tilde_pullbackSpecIso_unit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_tilde_pullback_map_pullbackSpecIso_hom_comp_pullbackSpecIso_hom

set_option maxHeartbeats 1600000

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_tilde_pullback_map_pullbackSpecIso_hom_comp_pullbackSpecIso_hom.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Modules.pushforwardCongr Scheme.Modules.pullback tilde.adjunction moduleSpecΓFunctor Spec Spec.map Scheme pullbackSpecIso Scheme.Modules.pullbackCongr tilde.functor Scheme.Modules tilde Scheme.Modules.pushforwardCongr_hom_app_app Scheme.Modules.pullbackComp tilde.pullbackSpecIso tilde.pullbackSpecIso_unit"
namespace TildePullbackCompAux
p2m_open "AlgebraicGeometry"

open CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {X : Type u₄} {Y : Type u₅} {Z : Type u₆}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
  [Category.{v₄} X] [Category.{v₅} Y] [Category.{v₆} Z]
  {FR : A ⥤ X} {GR : X ⥤ A} {FS : B ⥤ Y} {GS : Y ⥤ B} {FT : C ⥤ Z} {GT : Z ⥤ C}
  (tR : FR ⊣ GR) (tS : FS ⊣ GS) (tT : FT ⊣ GT)
  {Eφ : A ⥤ B} {Rφ : B ⥤ A} {Eψ : B ⥤ C} {Rψ : C ⥤ B} {Eφψ : A ⥤ C} {Rφψ : C ⥤ A}
  (eφ : Eφ ⊣ Rφ) (eψ : Eψ ⊣ Rψ) (eφψ : Eφψ ⊣ Rφψ)
  {Pφ : X ⥤ Y} {Qφ : Y ⥤ X} {Pψ : Y ⥤ Z} {Qψ : Z ⥤ Y} {Pφψ : X ⥤ Z} {Qφψ : Z ⥤ X}
  (pφ : Pφ ⊣ Qφ) (pψ : Pψ ⊣ Qψ) (pφψ : Pφψ ⊣ Qφψ)
  (dφ : Qφ ⋙ GR ≅ GS ⋙ Rφ) (dψ : Qψ ⋙ GS ≅ GT ⋙ Rψ) (dφψ : Qφψ ⋙ GR ≅ GT ⋙ Rφψ)
  (q : Qφψ ⟶ Qψ ⋙ Qφ) (r : Rφψ ⟶ Rψ ⋙ Rφ)
  (M : A)
  (βφ : Pφ.obj (FR.obj M) ⟶ FS.obj (Eφ.obj M))
  (βψ : Pψ.obj (FS.obj (Eφ.obj M)) ⟶ FT.obj (Eψ.obj (Eφ.obj M)))
  (βφψ : Pφψ.obj (FR.obj M) ⟶ FT.obj (Eφψ.obj M))
  (κ : (Pφ ⋙ Pψ).obj (FR.obj M) ⟶ Pφψ.obj (FR.obj M))
  (ε : Eφψ.obj M ⟶ (Eφ ⋙ Eψ).obj M)

theorem main
    (hφ : (tR.comp pφ).unit.app M ≫ (Qφ ⋙ GR).map βφ ≫ dφ.hom.app _ =
      eφ.unit.app M ≫ Rφ.map (tS.unit.app _))
    (hψ : (tS.comp pψ).unit.app (Eφ.obj M) ≫ (Qψ ⋙ GS).map βψ ≫ dψ.hom.app _ =
      eψ.unit.app _ ≫ Rψ.map (tT.unit.app _))
    (hφψ : (tR.comp pφψ).unit.app M ≫ (Qφψ ⋙ GR).map βφψ ≫ dφψ.hom.app _ =
      eφψ.unit.app M ≫ Rφψ.map (tT.unit.app _))
    (hκ : (pφ.comp pψ).unit.app (FR.obj M) ≫ (Qψ ⋙ Qφ).map κ = pφψ.unit.app _ ≫ q.app _)
    (hε : eφψ.unit.app M ≫ Rφψ.map ε ≫ r.app _ = eφ.unit.app M ≫ Rφ.map (eψ.unit.app _))
    (hcoh : ∀ N : Z, GR.map (q.app N) ≫ dφ.hom.app (Qψ.obj N) ≫ Rφ.map (dψ.hom.app N) =
      dφψ.hom.app N ≫ r.app (GT.obj N)) :
    Pψ.map βφ ≫ βψ = κ ≫ βφψ ≫ FT.map ε := by

  simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Adjunction.comp_unit_app,
    Functor.map_comp, Category.assoc] at hφ hψ hφψ hκ hε hcoh

  have inj : Function.Injective (fun f : Pψ.obj (Pφ.obj (FR.obj M)) ⟶ FT.obj (Eψ.obj (Eφ.obj M)) =>
      tR.unit.app M ≫ GR.map (pφ.unit.app (FR.obj M)) ≫
        GR.map (Qφ.map (pψ.unit.app (Pφ.obj (FR.obj M)))) ≫ GR.map (Qφ.map (Qψ.map f)) ≫
        dφ.hom.app (Qψ.obj (FT.obj (Eψ.obj (Eφ.obj M)))) ≫
        Rφ.map (dψ.hom.app (FT.obj (Eψ.obj (Eφ.obj M))))) := by
    intro f g h
    dsimp only at h
    let N := FT.obj (Eψ.obj (Eφ.obj M))
    have h2 : (tR.unit.app M ≫ GR.map (pφ.unit.app (FR.obj M)) ≫
          GR.map (Qφ.map (pψ.unit.app (Pφ.obj (FR.obj M)))) ≫ GR.map (Qφ.map (Qψ.map f))) ≫
          (dφ.app (Qψ.obj N) ≪≫ Rφ.mapIso (dψ.app N)).hom =
        (tR.unit.app M ≫ GR.map (pφ.unit.app (FR.obj M)) ≫
          GR.map (Qφ.map (pψ.unit.app (Pφ.obj (FR.obj M)))) ≫ GR.map (Qφ.map (Qψ.map g))) ≫
          (dφ.app (Qψ.obj N) ≪≫ Rφ.mapIso (dψ.app N)).hom := by
      simpa only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc] using h
    rw [Iso.cancel_iso_hom_right] at h2
    apply (((tR.comp pφ).comp pψ).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    simp only [Adjunction.comp_unit_app, Functor.comp_map, Functor.map_comp,
      Functor.comp_obj, Functor.id_obj, Category.assoc]
    exact h2
  apply inj
  dsimp only

  have lhs : tR.unit.app M ≫ GR.map (pφ.unit.app (FR.obj M)) ≫
        GR.map (Qφ.map (pψ.unit.app (Pφ.obj (FR.obj M)))) ≫ GR.map (Qφ.map (Qψ.map (Pψ.map βφ ≫ βψ))) ≫
        dφ.hom.app (Qψ.obj (FT.obj (Eψ.obj (Eφ.obj M)))) ≫
        Rφ.map (dψ.hom.app (FT.obj (Eψ.obj (Eφ.obj M)))) =
      eφ.unit.app M ≫ Rφ.map (eψ.unit.app (Eφ.obj M)) ≫
        Rφ.map (Rψ.map (tT.unit.app (Eψ.obj (Eφ.obj M)))) := by
    have n1 := congr_arg (fun t => GR.map (Qφ.map t)) (pψ.unit_naturality βφ)
    simp only [Functor.comp_obj, Functor.id_obj, Functor.map_comp] at n1
    simp only [Functor.comp_obj, Functor.id_obj, Functor.map_comp, Category.assoc]
    rw [reassoc_of% n1]
    have n2 := dφ.hom.naturality (pψ.unit.app (FS.obj (Eφ.obj M)) ≫ Qψ.map βψ)
    simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.map_comp,
      Category.assoc] at n2
    rw [reassoc_of% n2, reassoc_of% hφ]
    simp only [← Functor.map_comp, Category.assoc, hψ]
  have rhs : tR.unit.app M ≫ GR.map (pφ.unit.app (FR.obj M)) ≫
        GR.map (Qφ.map (pψ.unit.app (Pφ.obj (FR.obj M)))) ≫
        GR.map (Qφ.map (Qψ.map (κ ≫ βφψ ≫ FT.map ε))) ≫
        dφ.hom.app (Qψ.obj (FT.obj (Eψ.obj (Eφ.obj M)))) ≫
        Rφ.map (dψ.hom.app (FT.obj (Eψ.obj (Eφ.obj M)))) =
      eφ.unit.app M ≫ Rφ.map (eψ.unit.app (Eφ.obj M)) ≫
        Rφ.map (Rψ.map (tT.unit.app (Eψ.obj (Eφ.obj M)))) := by
    have k1 := congr_arg (fun t => GR.map t) hκ
    simp only [Functor.comp_obj, Functor.id_obj, Functor.map_comp] at k1
    simp only [Functor.comp_obj, Functor.id_obj, Functor.map_comp, Category.assoc]
    rw [reassoc_of% k1]
    have k2 := congr_arg (fun t => GR.map t) (q.naturality (βφψ ≫ FT.map ε)).symm
    simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.map_comp, Category.assoc] at k2
    rw [reassoc_of% k2, hcoh]
    have k3 := dφψ.hom.naturality (FT.map ε)
    simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map] at k3
    rw [reassoc_of% k3, reassoc_of% hφψ]
    have k4 := congr_arg (fun t => Rφψ.map t) (tT.unit_naturality ε)
    simp only [Functor.comp_obj, Functor.id_obj, Functor.map_comp] at k4
    rw [reassoc_of% k4]
    have k5 := r.naturality (tT.unit.app (Eψ.obj (Eφ.obj M)))
    simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map] at k5
    rw [k5, reassoc_of% hε]
  exact lhs.trans rhs.symm

end AlgebraicGeometry.TildePullbackCompAux

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Modules.pushforwardCongr Scheme.Modules.pullback tilde.adjunction moduleSpecΓFunctor Spec Spec.map Scheme pullbackSpecIso Scheme.Modules.pullbackCongr tilde.functor Scheme.Modules tilde Scheme.Modules.pushforwardCongr_hom_app_app Scheme.Modules.pullbackComp tilde.pullbackSpecIso tilde.pullbackSpecIso_unit"
namespace TildePullbackCompAux
p2m_open "AlgebraicGeometry"

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_tilde_pullback_map_pullbackSpecIso_hom_comp_pullbackSpecIso_hom.AlgebraicGeometry Opposite AlgebraicGeometry.Scheme.Modules"

section Generic

variable {X Y Z : Scheme.{u}}

theorem pushforwardCongr_rfl (f : X ⟶ Y) :
    Scheme.Modules.pushforwardCongr (rfl : f = f) = Iso.refl _ := by
  ext N U x
  simp [Scheme.Modules.pushforwardCongr_hom_app_app]

theorem comp_unit_app_comp_map_pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) (A : Z.Modules) :
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f)).unit.app A ≫
        (pushforward f ⋙ pushforward g).map ((pullbackComp f g).hom.app A) =
      (pullbackPushforwardAdjunction (f ≫ g)).unit.app A ≫ (pushforwardComp f g).inv.app _ := by
  have h := unit_conjugateEquiv ((pullbackPushforwardAdjunction g).comp
    (pullbackPushforwardAdjunction f)) (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv A
  rw [conjugateEquiv_pullbackComp_inv] at h
  refine (Iso.eq_comp_inv ((pushforwardComp f g).app _)).mpr ?_
  rw [Iso.app_hom, Category.assoc]
  erw [(pushforwardComp f g).hom.naturality ((pullbackComp f g).hom.app A)]
  erw [reassoc_of% h]
  erw [← (pushforward (f ≫ g)).map_comp, Iso.inv_hom_id_app]
  simp

theorem comp_unit_app_comp_map_pullbackComp_pullbackCongr (f : X ⟶ Y) (g : Y ⟶ Z) {k : X ⟶ Z}
    (h : f ≫ g = k) (A : Z.Modules) :
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f)).unit.app A ≫
        (pushforward f ⋙ pushforward g).map ((pullbackComp f g).hom.app A ≫ (pullbackCongr h).hom.app A) =
      (pullbackPushforwardAdjunction k).unit.app A ≫
        ((pushforwardCongr h).inv ≫ (pushforwardComp f g).inv).app ((pullback k).obj A) := by
  subst h
  simp only [Functor.map_comp, NatTrans.comp_app, pushforwardCongr_rfl, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp]
  rw [← comp_unit_app_comp_map_pullbackComp]
  simp [Scheme.Modules.pullbackCongr]

variable {R : CommRingCat.{u}}

theorem moduleSpecΓFunctor_map_pushforwardCongr_inv_apply {f g : X ⟶ Spec R} (hf : f = g)
    (N : X.Modules) (y : (moduleSpecΓFunctor (R := R)).obj ((pushforward g).obj N)) :
    ((moduleSpecΓFunctor (R := R)).map ((pushforwardCongr hf).inv.app N)).hom y = y := by
  subst hf
  simp [pushforwardCongr_rfl]

theorem pushforwardSpecCompΓIso_hom_app_apply {S : CommRingCat.{u}} (φ : R ⟶ S) (N : (Spec S).Modules)
    (y : (moduleSpecΓFunctor (R := R)).obj ((pushforward (Spec.map φ)).obj N)) :
    ((pushforwardSpecCompΓIso φ).hom.app N :
      (moduleSpecΓFunctor (R := R)).obj ((pushforward (Spec.map φ)).obj N) ⟶
        (ModuleCat.restrictScalars φ.hom).obj ((moduleSpecΓFunctor (R := S)).obj N)).hom y = y := rfl

end Generic

section Concrete

variable {R S T : CommRingCat.{u}} (φ : R ⟶ S) (ψ : S ⟶ T)

theorem hε (M : ModuleCat.{u} R) :
    (ModuleCat.extendRestrictScalarsAdj (φ ≫ ψ).hom).unit.app M ≫
        (ModuleCat.restrictScalars (φ ≫ ψ).hom).map ((ModuleCat.extendScalarsComp φ.hom ψ.hom).hom.app M) ≫
        (ModuleCat.restrictScalarsComp φ.hom ψ.hom).hom.app
          ((ModuleCat.extendScalars ψ.hom).obj ((ModuleCat.extendScalars φ.hom).obj M)) =
      (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M ≫
        (ModuleCat.restrictScalars φ.hom).map ((ModuleCat.extendRestrictScalarsAdj ψ.hom).unit.app
          ((ModuleCat.extendScalars φ.hom).obj M)) := by
  have h := ModuleCat.homEquiv_extendScalarsComp φ.hom ψ.hom M
  rw [Adjunction.homEquiv_unit] at h
  exact (Iso.eq_comp_inv ((ModuleCat.restrictScalarsComp φ.hom ψ.hom).app _)
    (f := (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M ≫
      (ModuleCat.restrictScalars φ.hom).map ((ModuleCat.extendRestrictScalarsAdj ψ.hom).unit.app
        ((ModuleCat.extendScalars φ.hom).obj M)))
    (g := (ModuleCat.extendRestrictScalarsAdj (φ ≫ ψ).hom).unit.app M ≫
      (ModuleCat.restrictScalars (φ ≫ ψ).hom).map
        ((ModuleCat.extendScalarsComp φ.hom ψ.hom).hom.app M))).mp h

theorem tail3_apply (N : (Spec T).Modules)
    (z : (moduleSpecΓFunctor (R := R)).obj ((pushforward (Spec.map ψ ≫ Spec.map φ)).obj N)) :
    ((ModuleCat.restrictScalars φ.hom).map ((pushforwardSpecCompΓIso ψ).hom.app N)).hom
      (((pushforwardSpecCompΓIso φ).hom.app ((pushforward (Spec.map ψ)).obj N)).hom
        (((moduleSpecΓFunctor (R := R)).map ((pushforwardComp (Spec.map ψ) (Spec.map φ)).inv.app N)).hom z)) =
      z := rfl

theorem rhs_apply (N : (Spec T).Modules)
    (y : (moduleSpecΓFunctor (R := R)).obj ((pushforward (Spec.map (φ ≫ ψ))).obj N)) :
    ((pushforwardSpecCompΓIso (φ ≫ ψ)).hom.app N ≫
      (ModuleCat.restrictScalarsComp φ.hom ψ.hom).hom.app ((moduleSpecΓFunctor (R := T)).obj N)).hom y = y := rfl

theorem hcoh (N : (Spec T).Modules) :
    (moduleSpecΓFunctor (R := R)).map
        (((pushforwardCongr (Spec.map_comp φ ψ).symm).inv ≫
            (pushforwardComp (Spec.map ψ) (Spec.map φ)).inv).app N) ≫
      (pushforwardSpecCompΓIso φ).hom.app ((pushforward (Spec.map ψ)).obj N) ≫
      (ModuleCat.restrictScalars φ.hom).map ((pushforwardSpecCompΓIso ψ).hom.app N) =
    (pushforwardSpecCompΓIso (φ ≫ ψ)).hom.app N ≫
      (ModuleCat.restrictScalarsComp φ.hom ψ.hom).hom.app ((moduleSpecΓFunctor (R := T)).obj N) := by
  ext y
  refine Eq.trans ?_ (rhs_apply φ ψ N y).symm
  simp only [NatTrans.comp_app, Functor.map_comp, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply]
  refine (tail3_apply φ ψ N _).trans ?_
  exact moduleSpecΓFunctor_map_pushforwardCongr_inv_apply _ N y

end Concrete

end AlgebraicGeometry.TildePullbackCompAux

open AlgebraicGeometry.TildePullbackCompAux _root_.AlgebraicGeometry.Scheme.Modules in
theorem solution
    {R S T : CommRingCat.{u}} (φ : R ⟶ S) (ψ : S ⟶ T) (M : ModuleCat.{u} R) :
    (Scheme.Modules.pullback (Spec.map ψ)).map (tilde.pullbackSpecIso φ M).hom ≫
        (tilde.pullbackSpecIso ψ ((ModuleCat.extendScalars φ.hom).obj M)).hom =
      (Scheme.Modules.pullbackComp (Spec.map ψ) (Spec.map φ)).hom.app (tilde M) ≫
        (Scheme.Modules.pullbackCongr (Spec.map_comp φ ψ).symm).hom.app (tilde M) ≫
        (tilde.pullbackSpecIso (φ ≫ ψ) M).hom ≫
        (tilde.functor T).map ((ModuleCat.extendScalarsComp φ.hom ψ.hom).hom.app M) := by
  have := main (@id (@Adjunction (ModuleCat R) _ (Spec R).Modules (Scheme.Modules.instCategory : Category (Spec R).Modules)
      (tilde.functor R) moduleSpecΓFunctor) (tilde.adjunction (R := R)))
    (@id (@Adjunction (ModuleCat S) _ (Spec S).Modules (Scheme.Modules.instCategory : Category (Spec S).Modules)
      (tilde.functor S) moduleSpecΓFunctor) (tilde.adjunction (R := S)))
    (@id (@Adjunction (ModuleCat T) _ (Spec T).Modules (Scheme.Modules.instCategory : Category (Spec T).Modules)
      (tilde.functor T) moduleSpecΓFunctor) (tilde.adjunction (R := T)))
    (ModuleCat.extendRestrictScalarsAdj φ.hom) (ModuleCat.extendRestrictScalarsAdj ψ.hom)
    (ModuleCat.extendRestrictScalarsAdj (φ ≫ ψ).hom)
    (pullbackPushforwardAdjunction (Spec.map φ)) (pullbackPushforwardAdjunction (Spec.map ψ))
    (pullbackPushforwardAdjunction (Spec.map (φ ≫ ψ)))
    (pushforwardSpecCompΓIso φ) (pushforwardSpecCompΓIso ψ) (pushforwardSpecCompΓIso (φ ≫ ψ))
    ((pushforwardCongr (Spec.map_comp φ ψ).symm).inv ≫ (pushforwardComp (Spec.map ψ) (Spec.map φ)).inv)
    (ModuleCat.restrictScalarsComp φ.hom ψ.hom).hom
    M (tilde.pullbackSpecIso φ M).hom (tilde.pullbackSpecIso ψ ((ModuleCat.extendScalars φ.hom).obj M)).hom
    (tilde.pullbackSpecIso (φ ≫ ψ) M).hom
    _ ((ModuleCat.extendScalarsComp φ.hom ψ.hom).hom.app M)
    (tilde.pullbackSpecIso_unit φ M) (tilde.pullbackSpecIso_unit ψ _) (tilde.pullbackSpecIso_unit (φ ≫ ψ) M)
    (comp_unit_app_comp_map_pullbackComp_pullbackCongr (Spec.map ψ) (Spec.map φ) (Spec.map_comp φ ψ).symm (tilde M))
    (hε φ ψ M) (hcoh φ ψ)
  exact this.trans (@Category.assoc _ _
    ((Scheme.Modules.pullback (Spec.map φ) ⋙ Scheme.Modules.pullback (Spec.map ψ)).obj (tilde M)) _
    ((Scheme.Modules.pullback (Spec.map (φ ≫ ψ))).obj (tilde M)) _ _ _ _)

end S_AlgebraicGeometry_tilde_pullback_map_pullbackSpecIso_hom_comp_pullbackSpecIso_hom
end P2MW
export P2MW.S_AlgebraicGeometry_tilde_pullback_map_pullbackSpecIso_hom_comp_pullbackSpecIso_hom (solution)
