-- Prove2me | solution 1 for AutomorphicForm.ideleNorm_det_globalPoints
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/bc85d3c9-0e01-5961-b16f-0c32002c3821

import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_ideleNorm_det_globalPoints

set_option autoImplicit false

open scoped NumberField

theorem solution
    {F : Type} [Field F] [NumberField F] (γ : Matrix.GeneralLinearGroup (Fin 2) F) :
    NumberField.TateGlobal.ideleNorm F
        (Matrix.GeneralLinearGroup.det (AutomorphicForm.globalPoints (𝓞 F) F γ)) = 1 := by
  have hdet : Matrix.GeneralLinearGroup.det (AutomorphicForm.globalPoints (𝓞 F) F γ)
      = Units.map (algebraMap F (NumberField.AdeleRing (𝓞 F) F)).toMonoidHom
          (Matrix.GeneralLinearGroup.det γ) := by
    refine Units.ext ?_
    rw [Units.coe_map, Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.GeneralLinearGroup.val_det_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      RingHom.map_det]
    rfl
  letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
  haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 F) F
  unfold NumberField.TateGlobal.ideleNorm
  rw [hdet, NumberField.AdeleRing.distribHaarChar_algebraMap F (Matrix.GeneralLinearGroup.det γ)]
  rfl

end S_AutomorphicForm_ideleNorm_det_globalPoints
end P2MW
export P2MW.S_AutomorphicForm_ideleNorm_det_globalPoints (solution)
