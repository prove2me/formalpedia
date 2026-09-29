-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection_monoidalV2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/ee21e2d5-b855-5f94-9a86-7cff94155b0a

import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_PresheafOfModules_PullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection_monoidalV2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection_monoidalV2.AlgebraicGeometry Opposite TensorProduct"
p2m_open "CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme Scheme.Modules.Hom.app Scheme.Modules Scheme.Modules.pullbackTensorUnitObjIso Scheme.Modules.unitSection Scheme.Modules.pullbackLocalSection"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf Modules.pullback Hom Γ Modules.Hom.comp_app Hom.app Modules.Hom Modules.Hom.app Hom.comp_app Modules Opens grothendieckTopology PresheafOfModules Modules.sheafify Modules.pullbackTensorUnitObjIso Modules.unitSection Modules.pullbackLocalSection"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback presheaf Hom.comp_app Hom Hom.app pullbackPushforwardAdjunction sheafify pullback₀ pullbackTensorUnitObjIso unitSection pullbackLocalSection pullbackLocalSection_app"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace PullbackUnitSection

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

private abbrev _root_.AlgebraicGeometry.Scheme.Modules.PullbackUnitSection.adj (Z : Scheme.{u}) := SheafOfModules.sheafifyAdj Z.sheaf.obj Z.ringCatSheaf.property
p2m_export "AlgebraicGeometry.Scheme.Modules.PullbackUnitSection" "adj"

abbrev ι (Z : Scheme.{u}) := SheafOfModules.toPMod Z.sheaf.obj Z.ringCatSheaf.property

private abbrev _root_.AlgebraicGeometry.Scheme.Modules.PullbackUnitSection.pf := PresheafOfModules.PullbackMonoidal.pf (TopologicalSpace.Opens.map f.base)
  (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c
p2m_export "AlgebraicGeometry.Scheme.Modules.PullbackUnitSection" "pf"

abbrev adj₀ := PresheafOfModules.PullbackMonoidal.adj (TopologicalSpace.Opens.map f.base)
  (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c

abbrev e : Modules.sheafify Y ⋙ Modules.pullback f ≅ pullback₀ f ⋙ Modules.sheafify X :=
  SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom

def pb₀Section (P : Y.PresheafOfModules) (V : Y.Opens) (s : P.obj (op V)) :
    ((pullback₀ f).obj P).obj (op (f ⁻¹ᵁ V)) :=
  ((adj₀ f).unit.app P).app (op V) s

def shUnit {Z : Scheme.{u}} (A : Z.PresheafOfModules) (W : Z.Opens) (a : A.obj (op W)) :
    Γ((Modules.sheafify Z).obj A, W) :=
  ((adj Z).unit.app A).app (op W) a

example : pullback₀ f = PresheafOfModules.pullback f.toRingCatSheafHom.hom := rfl
example : adj₀ f = PresheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom.hom := rfl
example : e f =
    Localization.Lifting.iso (Modules.sheafify Y)
      (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj)
      (pullback₀ f ⋙ Modules.sheafify X) (Modules.pullback f) := rfl

lemma sheafify_map_app_shUnit {Z : Scheme.{u}} {A A' : Z.PresheafOfModules} (g : A ⟶ A') (W : Z.Opens)
    (z : A.obj (op W)) :
    Scheme.Modules.Hom.app ((Modules.sheafify Z).map g) W (shUnit A W z) = shUnit A' W (g.app (op W) z) := by
  have h := (adj Z).unit.naturality g
  exact (congr($(h.symm).app (op W) z) :)

lemma counit_app_shUnit {Z : Scheme.{u}} (L : Z.Modules) (V : Z.Opens) (s : Γ(L, V)) :
    Scheme.Modules.Hom.app ((adj Z).counit.app L) V (shUnit ((ι Z).obj L) V s) = s := by
  have h := (adj Z).right_triangle_components L
  exact (congr($(h).app (op V) s) :)

lemma homEquiv_symm_app_pb₀Section {A : Y.PresheafOfModules} {B : X.PresheafOfModules}
    (k : A ⟶ (pf f).obj B) (V : Y.Opens) (z : A.obj (op V)) :
    (((adj₀ f).homEquiv A B).symm k).app (op (f ⁻¹ᵁ V)) (pb₀Section f A V z) =
      (k.app (op V) z : B.obj (op (f ⁻¹ᵁ V))) := by
  have h1 := (adj₀ f).homEquiv_unit (X := A) (Y := B) (f := ((adj₀ f).homEquiv A B).symm k)
  rw [Equiv.apply_symm_apply] at h1
  exact (congr($(h1.symm).app (op V) z) :)

lemma e_hom_app_pullbackLocalSection (P : Y.PresheafOfModules) (V : Y.Opens) (s : P.obj (op V)) :
    Scheme.Modules.Hom.app ((e f).hom.app P) (f ⁻¹ᵁ V) (pullbackLocalSection f (shUnit P V s)) =
      shUnit ((pullback₀ f).obj P) (f ⁻¹ᵁ V) (pb₀Section f P V s) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).comp
      (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom))
    ((PresheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom.hom).comp
      (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj))) P
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app] at h
  exact (congr($(h).app (op V) s) :)

lemma η_sheafify_eq (Z : Scheme.{u}) : η (Modules.sheafify Z) = (adj Z).counit.app (𝟙_ Z.Modules) := rfl

lemma unitSection_eq {Z : Scheme.{u}} (V : Z.Opens) :
    Modules.unitSection V = Scheme.Modules.Hom.app (η (Modules.sheafify Z)) V
      (shUnit (𝟙_ Z.PresheafOfModules) V (1 : Γ(Z, V))) :=
  (counit_app_shUnit (𝟙_ Z.Modules) V (Modules.unitSection V)).symm

lemma η_pullback_eq : η (Modules.pullback f) =
    (Modules.pullback f).map (ε (Modules.sheafify Y)) ≫ (e f).hom.app (𝟙_ Y.PresheafOfModules) ≫
      η (pullback₀ f ⋙ Modules.sheafify X) := by
  letI := SheafOfModules.presheafW_isMonoidal Y.sheaf.obj Y.ringCatSheaf.property
  have hε : ε (Modules.pullback f) = ε (pullback₀ f ⋙ Modules.sheafify X) ≫
      (e f).inv.app (𝟙_ Y.PresheafOfModules) ≫ (Modules.pullback f).map (η (Modules.sheafify Y)) :=
    Localization.Monoidal.functorMonoidalOfComp_ε (Modules.sheafify Y)
      (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj)
      (Modules.pullback f) (pullback₀ f ⋙ Modules.sheafify X)
  rw [← cancel_epi (ε (Modules.pullback f)), Functor.Monoidal.ε_η, hε]
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, Functor.Monoidal.η_ε, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.inv_hom_id_app_assoc, Functor.Monoidal.ε_η]

lemma map_η_sheafify_comp_η_pullback :
    (Modules.pullback f).map (η (Modules.sheafify Y)) ≫ η (Modules.pullback f) =
      (e f).hom.app (𝟙_ Y.PresheafOfModules) ≫
        (Modules.sheafify X).map (η (pullback₀ f)) ≫ η (Modules.sheafify X) := by
  rw [η_pullback_eq, ← Category.assoc, ← CategoryTheory.Functor.map_comp, Functor.Monoidal.η_ε,
    CategoryTheory.Functor.map_id, Category.id_comp, Functor.OplaxMonoidal.comp_η]

lemma pf_ε_app_one (V : Y.Opens) :
    (ε (pf f)).app (op V) (1 : Γ(Y, V)) = (1 : Γ(X, f ⁻¹ᵁ V)) := by
  change (ε (_root_.PresheafOfModules.restrictScalars (_root_.PresheafOfModules.ringCatHom
      (R := (TopologicalSpace.Opens.map f.base).op ⋙ X.sheaf.obj) f.c)) ≫
      (_root_.PresheafOfModules.restrictScalars (_root_.PresheafOfModules.ringCatHom
        (R := (TopologicalSpace.Opens.map f.base).op ⋙ X.sheaf.obj) f.c)).map
        (ε (_root_.PresheafOfModules.pushforward₀OfCommRingCat (TopologicalSpace.Opens.map f.base)
          X.sheaf.obj))).app (op V) (1 : Γ(Y, V)) = (1 : Γ(X, f ⁻¹ᵁ V))
  rw [show ε (_root_.PresheafOfModules.pushforward₀OfCommRingCat (TopologicalSpace.Opens.map f.base) X.sheaf.obj)
      = 𝟙 _ from rfl, CategoryTheory.Functor.map_id, Category.comp_id]
  erw [ModuleCat.restrictScalars_η]
  exact (f.c.app (op V)).hom.map_one

lemma pb₀_η_app_pb₀Section_one (V : Y.Opens) :
    (η (pullback₀ f)).app (op (f ⁻¹ᵁ V)) (pb₀Section f (𝟙_ Y.PresheafOfModules) V (1 : Γ(Y, V))) =
      (1 : Γ(X, f ⁻¹ᵁ V)) := by
  rw [show η (pullback₀ f) = ((adj₀ f).homEquiv _ _).symm (ε (pf f)) from
    Adjunction.leftAdjointOplaxMonoidal_η (adj₀ f)]
  refine (homEquiv_symm_app_pb₀Section f (ε (pf f)) V (1 : Γ(Y, V))).trans ?_
  exact pf_ε_app_one f V

theorem pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection (V : Y.Opens) :
    (pullbackTensorUnitObjIso f).hom.app (f ⁻¹ᵁ V) (pullbackLocalSection f (Modules.unitSection V)) =
      Modules.unitSection (f ⁻¹ᵁ V) := by
  change Scheme.Modules.Hom.app (η (Modules.pullback f)) (f ⁻¹ᵁ V)
    (pullbackLocalSection f (Modules.unitSection V)) = _
  rw [unitSection_eq V, pullbackLocalSection_app]
  have h := congr(Scheme.Modules.Hom.app $(map_η_sheafify_comp_η_pullback f) (f ⁻¹ᵁ V)
    (pullbackLocalSection f (shUnit (𝟙_ Y.PresheafOfModules) V (1 : Γ(Y, V)))))
  simp only [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply] at h
  refine h.trans ?_
  rw [e_hom_app_pullbackLocalSection]

  have step₁ := congrArg (fun w => Scheme.Modules.Hom.app (η (Modules.sheafify X)) (f ⁻¹ᵁ V) w)
    (sheafify_map_app_shUnit (η (pullback₀ f)) (f ⁻¹ᵁ V)
      (pb₀Section f (𝟙_ Y.PresheafOfModules) V (1 : Γ(Y, V))))
  refine step₁.trans ?_
  have step₂ : shUnit (𝟙_ X.PresheafOfModules) (f ⁻¹ᵁ V) ((η (pullback₀ f)).app (op (f ⁻¹ᵁ V))
      (pb₀Section f (𝟙_ Y.PresheafOfModules) V (1 : Γ(Y, V)))) =
        shUnit (𝟙_ X.PresheafOfModules) (f ⁻¹ᵁ V) (1 : Γ(X, f ⁻¹ᵁ V)) :=
    congrArg (shUnit (𝟙_ X.PresheafOfModules) (f ⁻¹ᵁ V)) (pb₀_η_app_pb₀Section_one f V)
  have step₃ := congrArg (fun w => Scheme.Modules.Hom.app (η (Modules.sheafify X)) (f ⁻¹ᵁ V) w) step₂
  refine step₃.trans ?_
  rw [η_sheafify_eq]
  exact counit_app_shUnit (𝟙_ X.Modules) (f ⁻¹ᵁ V) (Modules.unitSection (f ⁻¹ᵁ V))

end PullbackUnitSection

end AlgebraicGeometry.Scheme.Modules

end

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection_monoidalV2.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection_monoidalV2.AlgebraicGeometry.Scheme.Modules in

theorem solution
    {X Y : AlgebraicGeometry.Scheme.{u}} (φ : X ⟶ Y) (U : Y.Opens) :
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorUnitObjIso φ).hom.app (φ ⁻¹ᵁ U)
      (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection φ
        (AlgebraicGeometry.Scheme.Modules.unitSection U)) =
    AlgebraicGeometry.Scheme.Modules.unitSection (φ ⁻¹ᵁ U) :=
  PullbackUnitSection.pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection φ U

end S_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection_monoidalV2
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection_monoidalV2 (solution)
