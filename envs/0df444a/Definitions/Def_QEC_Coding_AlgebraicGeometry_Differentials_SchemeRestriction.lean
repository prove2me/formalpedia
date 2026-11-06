-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestriction
-- name    : QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestriction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:02:18.619276+00:00
-- url     : https://prove2.me/theorems/b8abde93-8b0a-4184-9dec-d0c7cbafb62e
-- title:
--   Scheme Restriction
-- statement:
--   Definitions and structural lemmas for Scheme Restriction, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeRestriction.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_KaehlerRingIso
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeDifferentials
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_kaehlerRingIso_forward_bijective

set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
variable (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤))
def schemeRestrictionConstantMap : k ⟶ Γ(Y, ⊤) := c ≫ f.appTop
lemma schemeRestrictionConstantPresheafMap_image (U : Y.Opens) :
    (schemeConstantPresheafMap Y k (schemeRestrictionConstantMap f k c)).app (op U) ≫
      (f.appIso U).inv =
    (schemeConstantPresheafMap X k c).app (op (f ''ᵁ U)) := by
  have h := f.appLE_appIso_inv (U := ⊤) (V := U) (by simp)
  change (c ≫ f.appTop) ≫ Y.presheaf.map (homOfLE le_top).op ≫
    (f.appIso U).inv = c ≫ X.presheaf.map (homOfLE le_top).op
  exact (Category.assoc c f.appTop _).trans (congrArg (fun t => c ≫ t) h)
local notation "OmegaX" => schemeDifferentialSheaf X k c
def schemeRestrictedDifferentialSheaf : Y.Modules :=
  (Scheme.Modules.restrictFunctor f).obj (schemeDifferentialSheaf X k c)
local notation "R" => schemeRestrictedDifferentialSheaf f k c
local notation "deltaX" => schemeDifferentialSheafDerivation X k c
def schemeRestrictedDifferentialSheafDerivation :
    ((Scheme.Modules.toPresheafOfModules Y).obj R).Derivation'
      (schemeConstantPresheafMap Y k (schemeRestrictionConstantMap f k c)) where
  d := fun {U} => ((deltaX).d (X := f.opensFunctor.op.obj U)).comp
    (f.appIso U.unop).inv.hom.toAddMonoidHom
  d_mul := fun {U} a b => by
    have h := (deltaX).d_mul ((f.appIso U.unop).inv a) ((f.appIso U.unop).inv b)
    exact (congrArg (fun z => (deltaX).d z) ((f.appIso U.unop).inv.hom.map_mul a b)).trans h
  d_map := fun {U V} i a => by
    change (deltaX).d ((f.appIso V.unop).inv (Y.presheaf.map i a)) =
      ((OmegaX).val.map (f.opensFunctor.op.map i))
        ((deltaX).d ((f.appIso U.unop).inv a))
    have h := congrArg (fun t => t a) (f.appIso_inv_naturality i)
    exact (congrArg (fun b => (deltaX).d b) h).trans
      ((deltaX).d_map (f.opensFunctor.op.map i) ((f.appIso U.unop).inv a))
  d_app := fun {U} a => by
    change (deltaX).d ((f.appIso U.unop).inv
      ((schemeConstantPresheafMap Y k (schemeRestrictionConstantMap f k c)).app U a)) = 0
    have h := congrArg (fun t => t a)
      (schemeRestrictionConstantPresheafMap_image f k c U.unop)
    have h' : (f.appIso U.unop).inv
        ((schemeConstantPresheafMap Y k (schemeRestrictionConstantMap f k c)).app U a) =
        (schemeConstantPresheafMap X k c).app (f.opensFunctor.op.obj U) a := h
    exact (congrArg (fun z => (deltaX).d z) h').trans ((deltaX).d_app a)
def schemeDifferentialRestrictionComparison :
    schemeDifferentialSheaf Y k (schemeRestrictionConstantMap f k c) ⟶ R :=
  (schemeDifferentialSheafHomEquiv Y k (schemeRestrictionConstantMap f k c) R).symm
    (schemeRestrictedDifferentialSheafDerivation f k c)
end
end QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
variable (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤))
def schemeRestrictionRingPresheafMap : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf where
  app U := (f.appIso U.unop).inv
  naturality {_U _V} i := f.appIso_inv_naturality i
def schemeRestrictionPresheafFunctor : X.PresheafOfModules ⥤ Y.PresheafOfModules :=
  PresheafOfModules.pushforward (F := f.opensFunctor)
    (Functor.whiskerRight (schemeRestrictionRingPresheafMap f) (forget₂ CommRingCat RingCat))
local notation "phiY" => schemeConstantPresheafMap Y k (schemeRestrictionConstantMap f k c)
local notation "phiX" => schemeConstantPresheafMap X k c
local notation "OmegaYp" => schemeDifferentialPresheaf Y k (schemeRestrictionConstantMap f k c)
local notation "OmegaXp" => schemeDifferentialPresheaf X k c
def schemeDifferentialPresheafRestrictionApp (U : Y.Opensᵒᵖ) :
    (OmegaYp).obj U ⟶ ((schemeRestrictionPresheafFunctor f).obj OmegaXp).obj U :=
  kaehlerRingIso_forward ((phiY).app U) ((phiX).app (f.opensFunctor.op.obj U))
    (f.appIso U.unop).symm (schemeRestrictionConstantPresheafMap_image f k c U.unop)
lemma schemeDifferentialPresheafRestrictionApp_D (U : Y.Opensᵒᵖ) (a : Y.presheaf.obj U) :
    schemeDifferentialPresheafRestrictionApp f k c U (CommRingCat.KaehlerDifferential.d a) =
    CommRingCat.KaehlerDifferential.d ((f.appIso U.unop).inv a) := by
  dsimp only [schemeDifferentialPresheafRestrictionApp, kaehlerRingIso_forward]
  apply CommRingCat.KaehlerDifferential.map_d
def schemeDifferentialPresheafRestrictionComparison :
    OmegaYp ⟶ (schemeRestrictionPresheafFunctor f).obj OmegaXp where
  app U := schemeDifferentialPresheafRestrictionApp f k c U
  naturality {U V} i := by
    apply CommRingCat.KaehlerDifferential.ext
    intro a
    change schemeDifferentialPresheafRestrictionApp f k c V
        ((OmegaYp).map i (CommRingCat.KaehlerDifferential.d a)) =
      (OmegaXp).map (f.opensFunctor.op.map i)
        (schemeDifferentialPresheafRestrictionApp f k c U (CommRingCat.KaehlerDifferential.d a))
    have hY := PresheafOfModules.DifferentialsConstruction.relativeDifferentials'_map_d
      phiY i a
    have hX := PresheafOfModules.DifferentialsConstruction.relativeDifferentials'_map_d
      phiX (f.opensFunctor.op.map i) ((f.appIso U.unop).inv a)
    have hR : (f.appIso V.unop).inv (Y.presheaf.map i a) =
        X.presheaf.map (f.opensFunctor.op.map i) ((f.appIso U.unop).inv a) :=
      congrArg (fun t => t a) (f.appIso_inv_naturality i)
    exact (congrArg (fun z => schemeDifferentialPresheafRestrictionApp f k c V z) hY).trans
      ((schemeDifferentialPresheafRestrictionApp_D f k c V (Y.presheaf.map i a)).trans
        ((congrArg (CommRingCat.KaehlerDifferential.d
          (f := (phiX).app (f.opensFunctor.op.obj V))) hR).trans
          (hX.symm.trans (congrArg (fun z => (OmegaXp).map (f.opensFunctor.op.map i) z)
            (schemeDifferentialPresheafRestrictionApp_D f k c U a).symm))))
lemma schemeDifferentialPresheafRestrictionApp_bijective (U : Y.Opensᵒᵖ) :
    Function.Bijective (schemeDifferentialPresheafRestrictionApp f k c U) :=
  kaehlerRingIso_forward_bijective ((phiY).app U) ((phiX).app (f.opensFunctor.op.obj U))
    (f.appIso U.unop).symm (schemeRestrictionConstantPresheafMap_image f k c U.unop)
end
end QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
variable (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤))
local notation "OmegaXp" => schemeDifferentialPresheaf X k c
local notation "OmegaYp" => schemeDifferentialPresheaf Y k (schemeRestrictionConstantMap f k c)
local notation "OmegaX" => schemeDifferentialSheaf X k c
local notation "R" => schemeRestrictedDifferentialSheaf f k c
local notation "phiY" => schemeConstantPresheafMap Y k (schemeRestrictionConstantMap f k c)
def schemeDifferentialSheafificationUnit : OmegaXp ⟶
    (Scheme.Modules.toPresheafOfModules X).obj OmegaX :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app OmegaXp
lemma schemeDifferentialSheafDerivation_eq_unit (U : X.Opensᵒᵖ) (a : X.presheaf.obj U) :
    (schemeDifferentialSheafDerivation X k c).d a =
      (schemeDifferentialSheafificationUnit k c).app U (CommRingCat.KaehlerDifferential.d a) := by
  rfl
def schemeDifferentialRestrictionPresheafComparison :
    OmegaYp ⟶ (Scheme.Modules.toPresheafOfModules Y).obj R :=
  schemeDifferentialPresheafRestrictionComparison f k c ≫
    (schemeRestrictionPresheafFunctor f).map (schemeDifferentialSheafificationUnit k c)
lemma schemeDifferentialRestrictionPresheafComparison_D (U : Y.Opensᵒᵖ)
    (a : Y.presheaf.obj U) :
    (schemeDifferentialRestrictionPresheafComparison f k c).app U
      (CommRingCat.KaehlerDifferential.d a) =
    (schemeRestrictedDifferentialSheafDerivation f k c).d a := by
  change (schemeDifferentialSheafificationUnit k c).app (f.opensFunctor.op.obj U)
    (schemeDifferentialPresheafRestrictionApp f k c U (CommRingCat.KaehlerDifferential.d a)) =
      (schemeDifferentialSheafDerivation X k c).d ((f.appIso U.unop).inv a)
  exact (congrArg (fun z => (schemeDifferentialSheafificationUnit k c).app
    (f.opensFunctor.op.obj U) z) (schemeDifferentialPresheafRestrictionApp_D f k c U a)).trans
      (schemeDifferentialSheafDerivation_eq_unit k c _ _).symm
lemma schemeDifferentialRestrictionComparison_homEquiv :
    PresheafOfModules.sheafificationHomEquiv (𝟙 Y.ringCatSheaf.obj)
      (schemeDifferentialRestrictionComparison f k c) =
      schemeDifferentialRestrictionPresheafComparison f k c := by
  apply (PresheafOfModules.DifferentialsConstruction.isUniversal' phiY).postcomp_injective
  have h := (schemeDifferentialSheafHomEquiv Y k (schemeRestrictionConstantMap f k c) R).apply_symm_apply
    (schemeRestrictedDifferentialSheafDerivation f k c)
  refine h.trans ?_
  ext U a
  exact (schemeDifferentialRestrictionPresheafComparison_D f k c U a).symm
def schemeDifferentialRestrictionAbelianPresheafMap :=
  (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
    (schemeDifferentialPresheafRestrictionComparison f k c)
def schemeDifferentialRestrictionAbelianComparison :=
  (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
    (schemeDifferentialRestrictionPresheafComparison f k c)
lemma schemeDifferentialRestrictionAbelianComparison_fac :
    schemeDifferentialRestrictionAbelianComparison f k c =
      schemeDifferentialRestrictionAbelianPresheafMap f k c ≫
        Functor.whiskerLeft f.opensFunctor.op
          (CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology X) (OmegaXp).presheaf) := by
  rfl
lemma schemeDifferentialRestrictionAbelianPresheafMap_locallyInjective :
    CategoryTheory.Presheaf.IsLocallyInjective (_root_.Opens.grothendieckTopology Y)
      (schemeDifferentialRestrictionAbelianPresheafMap f k c) :=
  CategoryTheory.Presheaf.isLocallyInjective_of_injective _ _
    (fun U => (schemeDifferentialPresheafRestrictionApp_bijective f k c U).injective)
lemma schemeDifferentialRestrictionAbelianPresheafMap_locallySurjective :
    CategoryTheory.Presheaf.IsLocallySurjective (_root_.Opens.grothendieckTopology Y)
      (schemeDifferentialRestrictionAbelianPresheafMap f k c) :=
  CategoryTheory.Presheaf.isLocallySurjective_of_surjective _ _
    (fun U => (schemeDifferentialPresheafRestrictionApp_bijective f k c U).surjective)
lemma schemeDifferentialRestrictionAbelianComparison_locallyInjective :
    CategoryTheory.Presheaf.IsLocallyInjective (_root_.Opens.grothendieckTopology Y)
      (schemeDifferentialRestrictionAbelianComparison f k c) := by
  rw [schemeDifferentialRestrictionAbelianComparison_fac]
  have hinj : CategoryTheory.Presheaf.IsLocallyInjective (_root_.Opens.grothendieckTopology Y)
      (schemeDifferentialRestrictionAbelianPresheafMap f k c) :=
    schemeDifferentialRestrictionAbelianPresheafMap_locallyInjective f k c
  have hunit : CategoryTheory.Presheaf.IsLocallyInjective (_root_.Opens.grothendieckTopology Y)
      (Functor.whiskerLeft f.opensFunctor.op
        (CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology X) (OmegaXp).presheaf)) :=
    CategoryTheory.Presheaf.isLocallyInjective_whisker
    (_root_.Opens.grothendieckTopology Y) (_root_.Opens.grothendieckTopology X)
    f.opensFunctor (CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology X) (OmegaXp).presheaf)
  exact @CategoryTheory.Presheaf.isLocallyInjective_comp _ _ _ _ _ _ _ _
    (_root_.Opens.grothendieckTopology Y) _ _ _
    (schemeDifferentialRestrictionAbelianPresheafMap f k c)
    (Functor.whiskerLeft f.opensFunctor.op
      (CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology X) (OmegaXp).presheaf))
    hinj hunit
lemma schemeDifferentialRestrictionAbelianComparison_locallySurjective :
    CategoryTheory.Presheaf.IsLocallySurjective (_root_.Opens.grothendieckTopology Y)
      (schemeDifferentialRestrictionAbelianComparison f k c) := by
  rw [schemeDifferentialRestrictionAbelianComparison_fac]
  have hinj : CategoryTheory.Presheaf.IsLocallySurjective (_root_.Opens.grothendieckTopology Y)
      (schemeDifferentialRestrictionAbelianPresheafMap f k c) :=
    schemeDifferentialRestrictionAbelianPresheafMap_locallySurjective f k c
  have hunit : CategoryTheory.Presheaf.IsLocallySurjective (_root_.Opens.grothendieckTopology Y)
      (Functor.whiskerLeft f.opensFunctor.op
        (CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology X) (OmegaXp).presheaf)) :=
    CategoryTheory.Presheaf.isLocallySurjective_whisker
    (_root_.Opens.grothendieckTopology Y) (_root_.Opens.grothendieckTopology X)
    f.opensFunctor (CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology X) (OmegaXp).presheaf)
  exact @CategoryTheory.Presheaf.isLocallySurjective_comp _ _
    (_root_.Opens.grothendieckTopology Y) _ _ _ _ _ _ _ _ _
    (schemeDifferentialRestrictionAbelianPresheafMap f k c)
    (Functor.whiskerLeft f.opensFunctor.op
      (CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology X) (OmegaXp).presheaf))
    hinj hunit
end
end QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
variable (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤))
lemma schemeDifferentialRestrictionComparison_isIso :
    IsIso (schemeDifferentialRestrictionComparison f k c) := by
  let J := _root_.Opens.grothendieckTopology Y
  let OmegaYp := schemeDifferentialPresheaf Y k (schemeRestrictionConstantMap f k c)
  let unit := CategoryTheory.toSheafify J OmegaYp.presheaf
  let theta := (SheafOfModules.toSheaf Y.ringCatSheaf).map
    (schemeDifferentialRestrictionComparison f k c)
  have hfac : unit ≫ theta.hom = schemeDifferentialRestrictionAbelianComparison f k c := by
    have h := PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
      (𝟙 Y.ringCatSheaf.obj) (schemeDifferentialRestrictionComparison f k c)
    rw [schemeDifferentialRestrictionComparison_homEquiv f k c] at h
    exact h.symm
  have hinj : CategoryTheory.Presheaf.IsLocallyInjective J theta.hom :=
    (CategoryTheory.Presheaf.comp_isLocallyInjective_iff J unit theta.hom).mp (by
      rw [hfac]
      exact schemeDifferentialRestrictionAbelianComparison_locallyInjective f k c)
  have hsurj : CategoryTheory.Presheaf.IsLocallySurjective J theta.hom :=
    (CategoryTheory.Presheaf.comp_isLocallySurjective_iff J unit theta.hom).mp (by
      rw [hfac]
      exact schemeDifferentialRestrictionAbelianComparison_locallySurjective f k c)
  have hiso : IsIso theta :=
    (CategoryTheory.Sheaf.isLocallyBijective_iff_isIso theta).mp ⟨hinj, hsurj⟩
  have hpresheaf : IsIso theta.hom :=
    (CategoryTheory.sheafToPresheaf J AddCommGrpCat).map_isIso theta
  exact (isIso_iff_of_reflects_iso (schemeDifferentialRestrictionComparison f k c)
    (Scheme.Modules.toPresheaf Y)).mp hpresheaf
def schemeDifferentialRestrictionIso :
    schemeDifferentialSheaf Y k (schemeRestrictionConstantMap f k c) ≅
      (Scheme.Modules.restrictFunctor f).obj (schemeDifferentialSheaf X k c) :=
  @asIso _ _ _ _ (schemeDifferentialRestrictionComparison f k c)
    (schemeDifferentialRestrictionComparison_isIso f k c)
end
end QEC.Coding.AlgebraicGeometry


