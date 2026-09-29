-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/8c079ece-40fd-53f8-9706-5024c22e045c

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X Y : Scheme.{u}} (φ : X ⟶ Y) (U : Y.Opens) (g : Γ(Y, U)) :
    (Scheme.Modules.pullbackUnitIso φ).hom.app (φ ⁻¹ᵁ U)
        (Scheme.Modules.pullbackLocalSection φ (Scheme.Modules.toUnitSection U g)) =
      Scheme.Modules.toUnitSection (φ ⁻¹ᵁ U) (φ.app U g) := by

  have h1 : (Scheme.Modules.pullbackUnitIso φ).hom =
      ((Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv _ _).symm
        (SheafOfModules.unitToPushforwardObjUnit φ.toRingCatSheafHom) := rfl
  rw [h1, Scheme.Modules.homEquiv_symm_app_pullbackLocalSection]
  rfl

end S_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection (solution)
