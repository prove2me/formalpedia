-- Prove2me | Definitions.Def_AlgebraicGeometry_PresheafPullbackCompositionComparison
-- name    : AlgebraicGeometry_PresheafPullbackCompositionComparison
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-19T14:53:02.57333+00:00
-- url     : https://prove2.me/theorems/5d7efa1a-7ca1-46b3-81c8-6abb349793d9
-- title:
--   Composition comparison for presheaf pullback
-- statement:
--   For two composable scheme morphisms, the comparison identifies successive pullbacks of presheaves of modules with pullback along the composite. Under the canonical comparison with sheafification, it transports to the usual comparison for sheaves of modules.
-- source:
--   Mathlib, SheafOfModules.sheafificationCompPullback and CategoryTheory.Adjunction.leftAdjointCompIso.

import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.Adjunction.Unique
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2

section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory

namespace PhilipponAdjointCompositionComparisons

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]

theorem mate_leftAdjointUniq {L K : A ⥤ B} {R : B ⥤ A} (a : L ⊣ R) (b : K ⊣ R) :
    conjugateEquiv b a (a.leftAdjointUniq b).hom = 𝟙 R := by
  simp [Adjunction.leftAdjointUniq]

theorem leftAdjointUniq_whiskerRight {L K : A ⥤ B} {R : B ⥤ A} (a : L ⊣ R) (b : K ⊣ R)
    {I : B ⥤ C} {J : C ⥤ B} (d : I ⊣ J) :
    ((a.comp d).leftAdjointUniq (b.comp d)).hom =
      Functor.whiskerRight (a.leftAdjointUniq b).hom I := by
  apply (conjugateEquiv (b.comp d) (a.comp d)).injective
  rw [mate_leftAdjointUniq, conjugateEquiv_whiskerRight, mate_leftAdjointUniq]
  ext
  simp

theorem leftAdjointUniq_whiskerLeft {L K : B ⥤ C} {R : C ⥤ B} (a : L ⊣ R) (b : K ⊣ R)
    {I : A ⥤ B} {J : B ⥤ A} (d : I ⊣ J) :
    ((d.comp a).leftAdjointUniq (d.comp b)).hom =
      Functor.whiskerLeft I (a.leftAdjointUniq b).hom := by
  apply (conjugateEquiv (d.comp b) (d.comp a)).injective
  rw [mate_leftAdjointUniq, conjugateEquiv_whiskerLeft, mate_leftAdjointUniq]
  ext
  simp

theorem leftAdjointUniq_associator {L : A ⥤ B} {R : B ⥤ A} (a : L ⊣ R)
    {K : B ⥤ C} {S : C ⥤ B} (b : K ⊣ S) {I : C ⥤ D} {J : D ⥤ C} (d : I ⊣ J) :
    (((a.comp b).comp d).leftAdjointUniq (a.comp (b.comp d))).hom =
      (Functor.associator L K I).hom := by
  apply (conjugateEquiv (a.comp (b.comp d)) ((a.comp b).comp d)).injective
  rw [mate_leftAdjointUniq, conjugateEquiv_associator_hom]
  rfl

theorem leftAdjointUniq_associator_inv {L : A ⥤ B} {R : B ⥤ A} (a : L ⊣ R)
    {K : B ⥤ C} {S : C ⥤ B} (b : K ⊣ S) {I : C ⥤ D} {J : D ⥤ C} (d : I ⊣ J) :
    ((a.comp (b.comp d)).leftAdjointUniq ((a.comp b).comp d)).hom =
      (Functor.associator L K I).inv := by
  have h := Iso.ext (leftAdjointUniq_associator a b d)
  ext X
  rw [← Adjunction.leftAdjointUniq_inv_app, h]

/-- A comparison whose right adjoint isomorphism is the identity agrees
with uniqueness of the left adjoints. -/
theorem leftAdjointCompIso_of_identity
    {L : A ⥤ B} {R : B ⥤ A} (a : L ⊣ R)
    {K : B ⥤ C} {S : C ⥤ B} (b : K ⊣ S)
    {I : A ⥤ C} (d : I ⊣ S ⋙ R) :
    (Adjunction.leftAdjointCompIso a b d (Iso.refl (S ⋙ R))).inv =
      (d.leftAdjointUniq (a.comp b)).hom := by
  apply (conjugateEquiv (a.comp b) d).injective
  rw [Adjunction.conjugateEquiv_leftAdjointCompIso_inv, mate_leftAdjointUniq, Iso.refl_hom]

theorem leftAdjointCompIso_hom_of_identity
    {L : A ⥤ B} {R : B ⥤ A} (a : L ⊣ R)
    {K : B ⥤ C} {S : C ⥤ B} (b : K ⊣ S)
    {I : A ⥤ C} (d : I ⊣ S ⋙ R) :
    (Adjunction.leftAdjointCompIso a b d (Iso.refl (S ⋙ R))).hom =
      ((a.comp b).leftAdjointUniq d).hom := by
  apply (conjugateEquiv d (a.comp b)).injective
  rw [Adjunction.leftAdjointCompIso_hom, Adjunction.leftAdjointCompNatTrans,
    Equiv.apply_symm_apply, mate_leftAdjointUniq, Iso.refl_inv]

end PhilipponAdjointCompositionComparisons
end

section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PhilipponAdjointCompositionComparisons

namespace PhilipponSchemePullbackSheafificationComposition
universe u

abbrev L (X : Scheme.{u}) := Scheme.Modules.sheafify X
abbrev F {X Y : Scheme.{u}} (f : X ⟶ Y) := Scheme.Modules.pullback f
abbrev P {X Y : Scheme.{u}} (f : X ⟶ Y) := Scheme.Modules.pullback₀ f

private abbrev a (X : Scheme.{u}) := SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property
private abbrev d {X Y : Scheme.{u}} (f : X ⟶ Y) := Scheme.Modules.pullbackPushforwardAdjunction f
abbrev b {X Y : Scheme.{u}} (f : X ⟶ Y) := PresheafOfModules.PullbackMonoidal.adj (Opens.map f.base) f.c

abbrev lifted {X Y : Scheme.{u}} (f : X ⟶ Y) : L Y ⋙ F f ≅ P f ⋙ L X :=
  SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

abbrev presheafComp : P g ⋙ P f ≅ P (f ≫ g) :=
  ((b g).comp (b f)).leftAdjointUniq (b (f ≫ g))

theorem sheafComp_hom :
    (Scheme.Modules.pullbackComp f g).hom =
      (((d g).comp (d f)).leftAdjointUniq (d (f ≫ g))).hom :=
  leftAdjointCompIso_hom_of_identity (d g) (d f) (d (f ≫ g))

/-- Sheafification takes the presheaf pullback comparison for composition
to the actual pullback comparison for sheaves of modules. -/
theorem commuting_comparisons :
    Functor.whiskerLeft (L Z) (Scheme.Modules.pullbackComp f g).hom ≫ (lifted (f ≫ g)).hom =
      (Functor.associator (L Z) (F g) (F f)).inv ≫
        Functor.whiskerRight (lifted g).hom (F f) ≫
        (Functor.associator (P g) (L Y) (F f)).hom ≫
        Functor.whiskerLeft (P g) (lifted f).hom ≫
        (Functor.associator (P g) (P f) (L X)).inv ≫
        Functor.whiskerRight (presheafComp f g).hom (L X) := by
  change
    Functor.whiskerLeft (L Z) (Scheme.Modules.pullbackComp f g).hom ≫
        (((a Z).comp (d (f ≫ g))).leftAdjointUniq ((b (f ≫ g)).comp (a X))).hom =
      (Functor.associator (L Z) (F g) (F f)).inv ≫
        Functor.whiskerRight (((a Z).comp (d g)).leftAdjointUniq ((b g).comp (a Y))).hom (F f) ≫
        (Functor.associator (P g) (L Y) (F f)).hom ≫
        Functor.whiskerLeft (P g) (((a Y).comp (d f)).leftAdjointUniq ((b f).comp (a X))).hom ≫
        (Functor.associator (P g) (P f) (L X)).inv ≫
        Functor.whiskerRight (((b g).comp (b f)).leftAdjointUniq (b (f ≫ g))).hom (L X)
  rw [sheafComp_hom f g]
  rw [← leftAdjointUniq_whiskerLeft ((d g).comp (d f)) (d (f ≫ g)) (a Z),
    ← leftAdjointUniq_whiskerRight ((a Z).comp (d g)) ((b g).comp (a Y)) (d f),
    ← leftAdjointUniq_whiskerLeft ((a Y).comp (d f)) ((b f).comp (a X)) (b g),
    ← leftAdjointUniq_whiskerRight ((b g).comp (b f)) (b (f ≫ g)) (a X),
    ← leftAdjointUniq_associator_inv (a Z) (d g) (d f),
    ← leftAdjointUniq_associator (b g) (a Y) (d f),
    ← leftAdjointUniq_associator_inv (b g) (b f) (a X)]
  simp only [Adjunction.leftAdjointUniq_trans]

end PhilipponSchemePullbackSheafificationComposition
end
end


