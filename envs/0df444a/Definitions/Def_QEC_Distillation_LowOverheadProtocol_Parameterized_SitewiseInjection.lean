-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SitewiseInjection
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_SitewiseInjection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T15:34:34.187637+00:00
-- url     : https://prove2.me/theorems/18c58f16-30e7-45a3-bb40-c184a04f6756
-- title:
--   Sitewise Injection
-- statement:
--   Definitions and structural lemmas for Sitewise Injection, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SitewiseInjection.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Preparation
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhaseInjection
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
abbrev InjectionOutcomeWord (m w : Nat) := PhysicalSite m w → Bool
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
noncomputable def sitewiseTInvGlobalPhase {m w : Nat}
    (error : PhysicalErrorWord m w) (outcomes : InjectionOutcomeWord m w) : Complex :=
  ∏ i, PhaseInjection.oneShotAttemptGlobalPhase
    (tInvResourceAngle (error i)) (outcomes i)
noncomputable def sitewiseCorrectedTInvAttempt {m w : Nat}
    (error : PhysicalErrorWord m w) (outcomes : InjectionOutcomeWord m w)
    (psi : PhysicalRegister m w) : PhysicalRegister m w :=
  WithLp.toLp 2 fun bits =>
    (∏ i, correctedTInvBasisAmplitude (error i) (outcomes i) (bits i)) *
      psi bits
end HH18Parameterized
end Distillation
end QEC


