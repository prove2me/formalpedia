-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_FrHformSumLeft
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_FrHformSumLeft
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T17:23:18.610965+00:00
-- url     : https://prove2.me/theorems/47e9f26c-aaac-4394-9504-69af1dd27b9b
-- title:
--   Fr Hform Sum Left
-- statement:
--   Definitions and structural lemmas for Fr Hform Sum Left, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/FrHformSumLeft.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_HformSumRight
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_hform_add_right
import Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_hform_smul_right
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
open NumberField Matrix Formalism.UG PI.InHHClassFin Module
namespace PI.UnitaryGroupMassFormula.InHHClassFin
section FrameEx
variable {I : Formalism.MainNotions.S.AutInst} {S : Set (Fin I.n → I.E)}
variable (I S) in

def frW : Submodule I.E (Fin I.n → I.E) where
  carrier := {y | ∀ s ∈ S, hform (starRingEnd I.E) I.J s y = 0}
  add_mem' := fun {x y} hx hy s hs => by rw [hform_add_right, hx s hs, hy s hs, add_zero]
  zero_mem' := fun s _ => by simp [hform]
  smul_mem' := fun c x hx s hs => by rw [hform_smul_right, hx s hs, mul_zero]
end FrameEx
end PI.UnitaryGroupMassFormula.InHHClassFin


