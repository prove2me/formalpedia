-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:50.06078+00:00
-- url     : https://prove2.me/theorems/56e7b62f-20ee-4f98-83f7-58c72d9a4f88
-- title:
--   Map FOne Injective Of Sections Surjective
-- statement:
--   Definitions and structural lemmas for Map FOne Injective Of Sections Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe w' v u
open CategoryTheory Limits Abelian Opposite
noncomputable section
namespace GlobalTheory
namespace SheafLES
section Site
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]
variable (J) in

abbrev freeYoneda : C ⥤ Sheaf J AddCommGrpCat.{v} :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙ presheafToSheaf _ _
def freeYonedaHomEquiv (U : C) (F : Sheaf J AddCommGrpCat.{v}) :
    ((freeYoneda J).obj U ⟶ F) ≃ F.obj.obj (op U) :=
  (((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ F).trans
    ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj U) F.obj)).trans yonedaEquiv
def tautSection (U : C) : ((freeYoneda J).obj U).obj.obj (op U) :=
  freeYonedaHomEquiv U _ (𝟙 _)
lemma freeYonedaHomEquiv_comp (U : C) {F G : Sheaf J AddCommGrpCat.{v}}
    (φ : (freeYoneda J).obj U ⟶ F) (f : F ⟶ G) :
    freeYonedaHomEquiv U G (φ ≫ f) = f.hom.app (op U) (freeYonedaHomEquiv U F φ) := rfl
lemma freeYonedaHomEquiv_apply (U : C) {F : Sheaf J AddCommGrpCat.{v}}
    (φ : (freeYoneda J).obj U ⟶ F) :
    freeYonedaHomEquiv U F φ = φ.hom.app (op U) (tautSection U) := by
  rw [tautSection, ← freeYonedaHomEquiv_comp, Category.id_comp]
def freeYonedaHomAddEquiv (U : C) (F : Sheaf J AddCommGrpCat.{v}) :
    ((freeYoneda J).obj U ⟶ F) ≃+ F.obj.obj (op U) where
  toEquiv := freeYonedaHomEquiv U F
  map_add' φ ψ := by
    change freeYonedaHomEquiv U F (φ + ψ) = freeYonedaHomEquiv U F φ + freeYonedaHomEquiv U F ψ
    simp only [freeYonedaHomEquiv_apply]
    rfl
variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
section Basic
variable {F G K : Sheaf J AddCommGrpCat.{v}}
def map (f : F ⟶ G) (n : ℕ) (U : C) : Sheaf.H'.{w'} F n U →+ Sheaf.H'.{w'} G n U :=
  (((Sheaf.cohomologyPresheafFunctor.{w'} J n).map f).app (op U)).hom
def res (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {U V : C} (i : V ⟶ U) :
    Sheaf.H'.{w'} F n U →+ Sheaf.H'.{w'} F n V :=
  ((Sheaf.cohomologyPresheaf.{w'} F n).map i.op).hom
def equivZero (F : Sheaf J AddCommGrpCat.{v}) (U : C) :
    Sheaf.H'.{w'} F 0 U ≃+ F.obj.obj (op U) :=
  (Ext.addEquiv₀ (X := (freeYoneda J).obj U) (Y := F)).trans (freeYonedaHomAddEquiv U F)
end Basic
section Sequence
variable {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)
def δ (n : ℕ) (U : C) : Sheaf.H'.{w'} S.X₃ n U →+ Sheaf.H'.{w'} S.X₁ (n + 1) U :=
  hS.extClass.postcomp ((freeYoneda J).obj U) rfl
include hS
end Sequence
end Site
section Modules
universe v' u'
variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
theorem toSheaf_preservesColimitsOfShape (K : Type*) [Category K]
    [HasColimitsOfShape K AddCommGrpCat.{v}] :
    PreservesColimitsOfShape K (SheafOfModules.toSheaf.{v} R) where
  preservesColimit {F} := by
    let e : F ≅ (F ⋙ SheafOfModules.forget R) ⋙ PresheafOfModules.sheafification (𝟙 R.obj) :=
      Functor.isoWhiskerLeft F
        (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit).symm
    have h1 : PreservesColimitsOfShape K (PresheafOfModules.sheafification.{v} (𝟙 R.obj) ⋙
        SheafOfModules.toSheaf.{v} R) :=
      inferInstanceAs (PreservesColimitsOfShape K
        (PresheafOfModules.toPresheaf R.obj ⋙ presheafToSheaf J AddCommGrpCat.{v}))
    have h2 : PreservesColimit
        ((F ⋙ SheafOfModules.forget R) ⋙ PresheafOfModules.sheafification (𝟙 R.obj))
        (SheafOfModules.toSheaf.{v} R) :=
      preservesColimit_of_preserves_colimit_cocone
        (isColimitOfPreserves (PresheafOfModules.sheafification.{v} (𝟙 R.obj))
          (colimit.isColimit (F ⋙ SheafOfModules.forget R)))
        (isColimitOfPreserves (PresheafOfModules.sheafification.{v} (𝟙 R.obj) ⋙
          SheafOfModules.toSheaf.{v} R) (colimit.isColimit (F ⋙ SheafOfModules.forget R)))
    exact preservesColimit_of_iso_diagram _ e.symm
instance toSheaf_preservesFiniteColimits :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{v} R) where
  preservesFiniteColimits K _ _ := toSheaf_preservesColimitsOfShape R K
end Modules
section Top
open TopologicalSpace
variable {X : TopCat.{u}}
end Top
section Scheme
open AlgebraicGeometry
variable (X : Scheme.{u})
def toAbSheaf : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  SheafOfModules.toSheaf X.ringCatSheaf
instance : (toAbSheaf X).Additive :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Additive
instance : (toAbSheaf X).Faithful :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Faithful
instance : (toAbSheaf X).ReflectsIsomorphisms :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).ReflectsIsomorphisms
instance : PreservesFiniteLimits (toAbSheaf X) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf X.ringCatSheaf))
instance : PreservesFiniteColimits (toAbSheaf X) :=
  inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf X.ringCatSheaf))
variable {X}
end Scheme
end SheafLES
end GlobalTheory


