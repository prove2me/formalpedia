-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.app_pullbackTensorPowIso_tensorPowMapIso_unitSection
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/fb81e86a-4608-5882-baea-f5f63a178094

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection_monoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_app_pullbackTensorPowIso_tensorPowMapIso_unitSection

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules"

theorem solution
    {X X' : Scheme.{u}} (c : X' ⟶ X) (L : X.Modules) (L' : X'.Modules) (e : (Scheme.Modules.pullback c).obj L ≅ L') :
    ((Scheme.Modules.pullbackTensorPowIso c L 0 ≪≫ Scheme.Modules.tensorPowMapIso e 0).hom.app ⊤) ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow 0)).app ⊤) (Scheme.Modules.unitSection ⊤))
      = Scheme.Modules.unitSection ⊤ := by
  have h := AlgebraicGeometry.Scheme.Modules.pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection_monoidalV2 c (⊤ : X.Opens)
  rw [Scheme.Modules.pullbackLocalSection_def] at h
  simp only [Iso.trans_hom, Scheme.Modules.pullbackTensorPowIso, Scheme.Modules.tensorPowMapIso, Iso.refl_hom, Category.comp_id]
  exact h

end S_AlgebraicGeometry_Scheme_Modules_app_pullbackTensorPowIso_tensorPowMapIso_unitSection
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_app_pullbackTensorPowIso_tensorPowMapIso_unitSection (solution)
