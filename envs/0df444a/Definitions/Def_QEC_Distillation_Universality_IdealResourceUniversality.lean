-- Prove2me | Definitions.Def_QEC_Distillation_Universality_IdealResourceUniversality
-- name    : QEC_Distillation_Universality_IdealResourceUniversality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T15:06:49.128807+00:00
-- url     : https://prove2.me/theorems/d1621bba-b181-4b49-9432-dabf37f3b395
-- title:
--   Ideal Resource Universality
-- statement:
--   Definitions and structural lemmas for Ideal Resource Universality, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/IdealResourceUniversality.lean

import Definitions.Def_QEC_Distillation_Universality_FiniteRegisterUniversality
import Definitions.Def_QEC_Distillation_Universality_HAngleUniversality
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Definitions.Def_QEC_Distillation_Universality_TPhaseGeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_TResourcePhase
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace IdealResourceUniversality
open QEC.Semantics
open QEC.Semantics.Qubit
open GeneratedUniversality
open OneQubitMagic
open PhaseInjection
open FiniteRegisterUniversality
open FiniteRegisterUniversality.FiniteRegisterCircuit
open scoped BigOperators
def hResourceGenerators : Set (UnitaryGate (Fin 2)) :=
  cliffordPhaseGenerators (-Real.pi / 4)
def tResourceGenerators : Set (UnitaryGate (Fin 2)) :=
  cliffordPhaseGenerators (-Real.pi / 6)
structure SourceTPreparationAcceptedTrace where
  rejectedAttempts : Nat
namespace SourceTPreparationAcceptedTrace
def attemptCount (trace : SourceTPreparationAcceptedTrace) : Nat :=
  trace.rejectedAttempts + 1
noncomputable def weight (trace : SourceTPreparationAcceptedTrace) : Real :=
  sourceTAttempt.rejectedWeight ^ trace.rejectedAttempts *
    sourceTAttempt.acceptedWeight
noncomputable def ledger (trace : SourceTPreparationAcceptedTrace) :
    AdaptiveIdealClifford.ResourceLedger (DensityOperator QubitSpace) :=
  Multiset.replicate (trace.attemptCount * sourceTAttempt.resourceCount)
    sourceTDensity
end SourceTPreparationAcceptedTrace
noncomputable def sourceTPreparationLedger (attemptCount : Nat) :
    AdaptiveIdealClifford.ResourceLedger (DensityOperator QubitSpace) :=
  Multiset.replicate (attemptCount * sourceTAttempt.resourceCount) sourceTDensity
noncomputable def sourceTPreparationHitMass (attemptBudget : Nat) : Real :=
  ∑ rejectedAttempts ∈ Finset.range attemptBudget,
    (SourceTPreparationAcceptedTrace.mk rejectedAttempts).weight
noncomputable def sourceTPreparationMissMass (attemptBudget : Nat) : Real :=
  sourceTAttempt.rejectedWeight ^ attemptBudget
def IdealHResourceRoute : Prop :=
  hResourceTransport.conjDensity hMagicState =
      phaseStateDensity (-Real.pi / 4) ∧
  (phaseStateResourceUse (-Real.pi / 4)).ledger = {(-Real.pi / 4)} ∧
  (∀ (psi : QubitSpace) (hpsi : ‖psi‖ = 1),
    (phaseStateResourceUse (-Real.pi / 4)).run (sourceInputDensity psi hpsi) =
      injectionInputDensity psi (-Real.pi / 4) hpsi) ∧
  (∀ (psi : QubitSpace) (hpsi : ‖psi‖ = 1) (coin : Bool),
    oneShotMeasurementWeight psi (-Real.pi / 4) hpsi coin = (1 / 2 : Real)) ∧
  (∀ (psi : QubitSpace) (hpsi : ‖psi‖ = 1) (coin : Bool),
    oneShotAttempt psi (-Real.pi / 4) hpsi coin =
      oneShotAttemptGlobalPhase (-Real.pi / 4) coin •
        phaseShiftOperator (oneShotAttemptAngle (-Real.pi / 4) coin) psi) ∧
  (∀ (psi : QubitSpace) (hpsi : ‖psi‖ = 1),
    Filter.Tendsto (fun blocks =>
      phaseInjectionStoppingHitMass (blocks := blocks)
        (0 : ZMod 8) (1 : ZMod 8) psi hpsi)
      Filter.atTop (nhds 1)) ∧
  (∀ (blocks : Nat) (trace : PhaseRetry.BlockTrace 8 blocks)
      (psi : QubitSpace) (hpsi : ‖psi‖ = 1),
    ∃ attempts ≤ 8 * blocks,
      phaseInjectionStoppingLedger
          (0 : ZMod 8) (1 : ZMod 8) trace psi hpsi =
        Multiset.replicate attempts (-Real.pi / 4)) ∧
  (∀ {blocks : Nat} (trace : PhaseRetry.BlockTrace 8 blocks)
      (psi : QubitSpace) (hpsi : ‖psi‖ = 1),
    PhaseRetry.traceVisitsTarget (0 : ZMod 8) (1 : ZMod 8) blocks trace →
      phaseInjectionStoppingOutputDensity
          (0 : ZMod 8) (1 : ZMod 8) trace psi hpsi =
        phaseCycleTargetOutputDensity 8 (1 : ZMod 8) psi hpsi) ∧
  phaseCycleTargetAction 8 (1 : ZMod 8) =
      phaseShiftOperator (-Real.pi / 4) ∧
  ProjectivelyGeneratedDense hResourceGenerators ∧
  ∀ {Wire : Type} [Fintype Wire] [DecidableEq Wire]
      (circuit : FiniteRegisterCircuit Wire)
      (precision : Real), 0 < precision →
    ApproximatesModuloPhase
      (finiteRegisterGenerators (Wire := Wire) hResourceGenerators)
      circuit.unitary precision
def IdealTResourceRoute : Prop :=
  sourceTAttempt.resourceCount = 2 ∧
  sourceTDensity = tMagicState ∧
  sourceTAttempt.acceptedWeight = 2 / 3 ∧
  sourceTAttempt.rejectedWeight = 1 / 3 ∧
  sourceTOutcomeAction .accepted = .emitAccepted ∧
  sourceTOutcomeAction .rejected = .retryWithFreshPair ∧
  (∀ attemptBudget,
    sourceTPreparationHitMass attemptBudget +
      sourceTPreparationMissMass attemptBudget = 1) ∧
  (∀ attemptBudget,
    sourceTPreparationMissMass attemptBudget = (1 / 3 : Real) ^ attemptBudget) ∧
  Filter.Tendsto sourceTPreparationMissMass Filter.atTop (nhds 0) ∧
  Filter.Tendsto sourceTPreparationHitMass Filter.atTop (nhds 1) ∧
  (∀ attemptCount,
    sourceTPreparationLedger attemptCount =
      Multiset.replicate (2 * attemptCount) sourceTDensity) ∧
  (∀ trace : SourceTPreparationAcceptedTrace,
    trace.weight = (1 / 3 : Real) ^ trace.rejectedAttempts * (2 / 3)) ∧
  (∀ trace : SourceTPreparationAcceptedTrace,
    trace.ledger = Multiset.replicate (2 * trace.attemptCount) sourceTDensity) ∧
  (QuantumChannel.unitaryConj hadamardTransport).mapDensity
        ((QuantumChannel.comp TwoQubit.secondQubitDiscard
          (QuantumChannel.unitaryConj TwoQubit.xorTransport)).mapDensity
            sourceTEvenBranch) =
      phaseStateDensity (-Real.pi / 6) ∧
  hadamardOperator sourceTEvenFirstQubit =
      sourceTGlobalPhase • phaseState (-Real.pi / 6) ∧
  ‖sourceTGlobalPhase‖ = 1 ∧
  (phaseStateResourceUse (-Real.pi / 6)).ledger = {(-Real.pi / 6)} ∧
  (∀ (psi : QubitSpace) (hpsi : ‖psi‖ = 1),
    (phaseStateResourceUse (-Real.pi / 6)).run (sourceInputDensity psi hpsi) =
      injectionInputDensity psi (-Real.pi / 6) hpsi) ∧
  (∀ (psi : QubitSpace) (hpsi : ‖psi‖ = 1) (coin : Bool),
    oneShotMeasurementWeight psi (-Real.pi / 6) hpsi coin = (1 / 2 : Real)) ∧
  (∀ (psi : QubitSpace) (hpsi : ‖psi‖ = 1) (coin : Bool),
    oneShotAttempt psi (-Real.pi / 6) hpsi coin =
      oneShotAttemptGlobalPhase (-Real.pi / 6) coin •
        phaseShiftOperator (oneShotAttemptAngle (-Real.pi / 6) coin) psi) ∧
  (∀ (psi : QubitSpace) (hpsi : ‖psi‖ = 1),
    Filter.Tendsto (fun blocks =>
      phaseInjectionStoppingHitMass (blocks := blocks)
        (0 : ZMod 12) (1 : ZMod 12) psi hpsi)
      Filter.atTop (nhds 1)) ∧
  (∀ (blocks : Nat) (trace : PhaseRetry.BlockTrace 12 blocks)
      (psi : QubitSpace) (hpsi : ‖psi‖ = 1),
    ∃ attempts ≤ 12 * blocks,
      phaseInjectionStoppingLedger
          (0 : ZMod 12) (1 : ZMod 12) trace psi hpsi =
        Multiset.replicate attempts (-Real.pi / 6)) ∧
  (∀ {blocks : Nat} (trace : PhaseRetry.BlockTrace 12 blocks)
      (psi : QubitSpace) (hpsi : ‖psi‖ = 1),
    PhaseRetry.traceVisitsTarget (0 : ZMod 12) (1 : ZMod 12) blocks trace →
      phaseInjectionStoppingOutputDensity
          (0 : ZMod 12) (1 : ZMod 12) trace psi hpsi =
        phaseCycleTargetOutputDensity 12 (1 : ZMod 12) psi hpsi) ∧
  phaseCycleTargetAction 12 (1 : ZMod 12) =
      phaseShiftOperator (-Real.pi / 6) ∧
  ProjectivelyGeneratedDense tResourceGenerators ∧
  ∀ {Wire : Type} [Fintype Wire] [DecidableEq Wire]
      (circuit : FiniteRegisterCircuit Wire)
      (precision : Real), 0 < precision →
    ApproximatesModuloPhase
      (finiteRegisterGenerators (Wire := Wire) tResourceGenerators)
      circuit.unitary precision
inductive IdealMagicResource
  | h
  | t
deriving DecidableEq
def idealMagicResourceGenerators :
    IdealMagicResource → Set (UnitaryGate (Fin 2))
  | .h => hResourceGenerators
  | .t => tResourceGenerators
def IdealMagicResourceRoute : IdealMagicResource → Prop
  | .h => IdealHResourceRoute
  | .t => IdealTResourceRoute
end IdealResourceUniversality
end Distillation
end QEC


