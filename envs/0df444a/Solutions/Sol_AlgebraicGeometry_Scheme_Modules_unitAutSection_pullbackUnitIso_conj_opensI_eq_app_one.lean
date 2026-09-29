-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.unitAutSection_pullbackUnitIso_conj_opensI_eq_app_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/e73f6053-2010-5f25-a7d7-38bc22499e27

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_conj_app_top_one_eq_appTop
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_unitAutSection_pullbackUnitIso_conj_opensI_eq_app_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace UASRestrict

theorem unit_app_one_res {Y : Scheme.{u}}
    (ψ : SheafOfModules.unit Y.ringCatSheaf ≅ SheafOfModules.unit Y.ringCatSheaf)
    {U V : Y.Opens} (i : V ⟶ U) :
    (Y.presheaf.map i.op).hom ((ψ.hom.val.app (op U)).hom (1 : Y.presheaf.obj (op U))) =
      (ψ.hom.val.app (op V)).hom (1 : Y.presheaf.obj (op V)) := by
  have h := PresheafOfModules.naturality_apply ψ.hom.val i.op (1 : Y.presheaf.obj (op U))
  erw [PresheafOfModules.unit_map_one] at h
  exact h.symm

end UASRestrict

open UASRestrict in
theorem solution
    {Y : Scheme.{u}} (W : Y.Opens)
    (ψ : SheafOfModules.unit Y.ringCatSheaf ≅ SheafOfModules.unit Y.ringCatSheaf) :
    Scheme.Modules.unitAutSection W
        ((Scheme.Modules.pullbackUnitIso W.ι).symm ≪≫ (Scheme.Modules.pullback W.ι).mapIso ψ ≪≫
          Scheme.Modules.pullbackUnitIso W.ι) =
      (ψ.hom.val.app (op W)).hom (1 : Y.presheaf.obj (op W)) := by
  unfold Scheme.Modules.unitAutSection
  erw [Scheme.Modules.pullbackUnitIso_conj_app_top_one_eq_appTop]
  rw [← unit_app_one_res ψ (homOfLE (le_top : W ≤ ⊤))]
  simp only [Scheme.Opens.topIso_hom, Scheme.Opens.ι_appTop]
  rw [← CommRingCat.comp_apply]
  erw [← Functor.map_comp]
  rfl

end S_AlgebraicGeometry_Scheme_Modules_unitAutSection_pullbackUnitIso_conj_opensI_eq_app_one
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_unitAutSection_pullbackUnitIso_conj_opensI_eq_app_one (solution)
