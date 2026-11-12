-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhaseInjection
-- name    : QEC_Distillation_LowOverheadProtocol_Core_PhaseInjection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T15:30:38.363292+00:00
-- url     : https://prove2.me/theorems/96a0a7e0-d98c-4ae5-b557-af25dba73a72
-- title:
--   Phase Injection
-- statement:
--   Definitions and structural lemmas for Phase Injection, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhaseInjection.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18PhaseInjection
open Semantics Semantics.Qubit
def tInvIdealAngle : Real :=
  -Real.pi / 4
def tInvErrorAngle : Real :=
  tInvIdealAngle + Real.pi
def tInvOutcomeCorrection : Bool -> Operator QubitSpace
  | true => 1
  | false => OneQubitMagic.phaseShiftOperator (-Real.pi / 2)
noncomputable def correctedIdealTInvAttempt (psi : QubitSpace)
    (hpsi : ‖psi‖ = 1) (coin : Bool) : QubitSpace :=
  tInvOutcomeCorrection coin
    (PhaseInjection.oneShotAttempt psi tInvIdealAngle hpsi coin)
noncomputable def correctedErroredTInvAttempt (psi : QubitSpace)
    (hpsi : ‖psi‖ = 1) (coin : Bool) : QubitSpace :=
  tInvOutcomeCorrection coin
    (PhaseInjection.oneShotAttempt psi tInvErrorAngle hpsi coin)
end HH18PhaseInjection
end Distillation
end QEC


