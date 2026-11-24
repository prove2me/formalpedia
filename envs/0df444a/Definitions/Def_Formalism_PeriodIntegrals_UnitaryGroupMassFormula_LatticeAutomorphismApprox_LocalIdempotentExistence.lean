-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocalIdempotentExistence
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocalIdempotentExistence
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T14:51:40.2778+00:00
-- url     : https://prove2.me/theorems/045439f5-9bb4-4a08-a55c-c372037d2db6
-- title:
--   Local Idempotent Existence
-- statement:
--   Definitions and structural lemmas for Local Idempotent Existence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/LocalIdempotentExistence.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_NatCastTmul
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_FinKW_LocTo_ov_smul_vec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.ScXuExists
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists
def smulLin (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (c : RV I v) :
    (Fin I.n → RV I v) →ₗ[OV I v] (Fin I.n → RV I v) where
  toFun x := c • x
  map_add' x y := smul_add c x y
  map_smul' o x := by
    simp only [RingHom.id_apply]
    rw [PI.FinKW.LocTo.ov_smul_vec, PI.FinKW.LocTo.ov_smul_vec, smul_comm]
end PI.UnitaryGroupMassFormula.ScXuExists


