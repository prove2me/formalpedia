-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SitewisePhaseInjection
-- name    : QEC_Distillation_LowOverheadProtocol_Core_SitewisePhaseInjection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T15:33:45.713457+00:00
-- url     : https://prove2.me/theorems/1517f8d8-b588-4121-a4c6-943569052c8d
-- title:
--   Sitewise Phase Injection
-- statement:
--   Definitions and structural lemmas for Sitewise Phase Injection, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SitewisePhaseInjection.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhaseInjection
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18SitewisePhaseInjection
open Coding Semantics
open Semantics.Qubit
open scoped BigOperators
abbrev PhysicalSite := HH18PuncturedReedMuller.PhysicalSite 4 0
abbrev PhysicalErrorWord := HH18NoisyInput.PhysicalErrorWord 4 0
abbrev InjectionOutcomeWord := PhysicalSite -> Bool
def tInvResourceAngle (error : ZMod 2) : Real :=
  if error = 0 then HH18PhaseInjection.tInvIdealAngle
  else HH18PhaseInjection.tInvErrorAngle
noncomputable def correctedTInvAttempt (error : ZMod 2) (psi : QubitSpace)
    (hpsi : ‖psi‖ = 1) (coin : Bool) : QubitSpace :=
  if error = 0 then
    HH18PhaseInjection.correctedIdealTInvAttempt psi hpsi coin
  else
    HH18PhaseInjection.correctedErroredTInvAttempt psi hpsi coin
noncomputable def correctedTInvBasisAmplitude
    (error : ZMod 2) (coin : Bool) (bit : Fin 2) : Complex :=
  correctedTInvAttempt error
    (EuclideanSpace.basisFun (Fin 2) Complex bit)
    ((EuclideanSpace.basisFun (Fin 2) Complex).norm_eq_one bit)
    coin bit
noncomputable def sitewiseTInvGlobalPhase
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord) : Complex :=
  ∏ i, PhaseInjection.oneShotAttemptGlobalPhase
    (tInvResourceAngle (error i)) (outcomes i)
noncomputable def sitewiseCorrectedTInvAttempt
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord)
    (psi : QubitRegister PhysicalSite) : QubitRegister PhysicalSite :=
  WithLp.toLp 2 fun bits =>
    (∏ i, correctedTInvBasisAmplitude (error i) (outcomes i) (bits i)) *
      psi bits
end HH18SitewisePhaseInjection
end Distillation
end QEC


