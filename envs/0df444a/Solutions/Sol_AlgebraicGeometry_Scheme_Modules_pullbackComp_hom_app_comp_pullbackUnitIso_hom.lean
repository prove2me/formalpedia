-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/f665d94a-324d-5257-89bd-dbcb4bdeffe8

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_comp_pullbackUnitIso_hom

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_comp_pullbackUnitIso_hom.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.hom_ext Scheme.Modules.pullback Scheme.Hom Scheme Scheme.Hom.comp_app Scheme.Modules Scheme.Modules.pullbackComp Scheme.Modules.pullbackUnitIso"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.hom_ext ringCatSheaf Modules.pullback Hom Γ Hom.comp_app Modules Opens Modules.pullbackComp Modules.pullbackUnitIso"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext pushforward pushforwardComp pullback Hom.comp_app Hom pushforward_map_app pullbackPushforwardAdjunction conjugateEquiv_pullbackComp_inv pullbackComp pullbackUnitIso"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

noncomputable def unitHom : @Quiver.Hom Y.Modules _ (SheafOfModules.unit Y.ringCatSheaf)
    ((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

theorem unitHom_app (U : Y.Opens) (x : Γ(SheafOfModules.unit Y.ringCatSheaf, U)) :
    (unitHom f).app U x = f.app U x := rfl

theorem homEquiv_pullbackUnitIso_hom :
    (pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackUnitIso f).hom = unitHom f := by
  have h := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit (φ := f.toRingCatSheafHom)
  exact h

theorem unitHom_comp :
    unitHom (f ≫ g) = unitHom g ≫ (pushforward g).map (unitHom f) ≫
      (pushforwardComp f g).hom.app (SheafOfModules.unit X.ringCatSheaf) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  simp only [Hom.comp_app, pushforward_map_app, CategoryTheory.comp_apply, unitHom_app, Scheme.Hom.comp_app]
  rfl

theorem homEquiv_comp_map_pullbackUnitIso :
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f)).homEquiv _ _
        ((pullback f).map (pullbackUnitIso g).hom ≫ (pullbackUnitIso f).hom) =
      unitHom g ≫ (pushforward g).map (unitHom f) := by
  rw [Adjunction.comp_homEquiv]
  change (pullbackPushforwardAdjunction g).homEquiv _ _ ((pullbackPushforwardAdjunction f).homEquiv _ _
    ((pullback f).map (pullbackUnitIso g).hom ≫ (pullbackUnitIso f).hom)) = _
  have h₁ : (pullbackPushforwardAdjunction f).homEquiv _ _
      ((pullback f).map (pullbackUnitIso g).hom ≫ (pullbackUnitIso f).hom) = (pullbackUnitIso g).hom ≫ unitHom f := by
    rw [← homEquiv_pullbackUnitIso_hom f]
    exact (pullbackPushforwardAdjunction f).homEquiv_naturality_left _ _
  rw [h₁, ← homEquiv_pullbackUnitIso_hom g]
  exact (pullbackPushforwardAdjunction g).homEquiv_naturality_right _ _

set_option maxHeartbeats 3200000 in

theorem pullbackUnitIso_comp :
    (pullbackComp f g).hom.app (SheafOfModules.unit Z.ringCatSheaf) ≫ (pullbackUnitIso (f ≫ g)).hom =
      (pullback f).map (pullbackUnitIso g).hom ≫ (pullbackUnitIso f).hom := by
  rw [← cancel_epi ((pullbackComp f g).inv.app (SheafOfModules.unit Z.ringCatSheaf)), Iso.inv_hom_id_app_assoc]
  apply ((pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
  rw [homEquiv_pullbackUnitIso_hom, unitHom_comp]
  have key := unit_conjugateEquiv ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv (SheafOfModules.unit Z.ringCatSheaf)
  rw [conjugateEquiv_pullbackComp_inv] at key
  have e₂ := homEquiv_comp_map_pullbackUnitIso f g
  rw [Adjunction.homEquiv_unit] at e₂
  rw [Adjunction.homEquiv_unit]
  erw [Functor.map_comp, ← reassoc_of% key, ← (pushforwardComp f g).hom.naturality, reassoc_of% e₂]

end AlgebraicGeometry.Scheme.Modules

theorem solution {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.pullbackComp f g).hom.app (SheafOfModules.unit Z.ringCatSheaf) ≫
        (Scheme.Modules.pullbackUnitIso (f ≫ g)).hom =
      (Scheme.Modules.pullback f).map (Scheme.Modules.pullbackUnitIso g).hom ≫
        (Scheme.Modules.pullbackUnitIso f).hom :=
  AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_comp f g

end S_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_comp_pullbackUnitIso_hom
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_comp_pullbackUnitIso_hom (solution)
