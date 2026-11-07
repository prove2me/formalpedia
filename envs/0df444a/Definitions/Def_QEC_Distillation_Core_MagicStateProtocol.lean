-- Prove2me | Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
-- name    : QEC_Distillation_Core_MagicStateProtocol
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:14:10.993494+00:00
-- url     : https://prove2.me/theorems/5a13912e-3d41-44d1-99f3-9f88588c81aa
-- title:
--   Magic State Protocol
-- statement:
--   Definitions and structural lemmas for Magic State Protocol, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/MagicStateProtocol.lean

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.convexCombination_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
universe u
namespace QEC
namespace Distillation
open Semantics
open scoped BigOperators
theorem densityOperator_ext {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
    {rho sigma : DensityOperator H}
    (h : rho.toOperator = sigma.toOperator) :
    rho = sigma := by
  cases rho with
  | mk rho hpos htrace =>
      cases sigma with
      | mk sigma hpos' htrace' =>
          dsimp at h
          cases h
          rfl
abbrev ResourceInput (count : Nat) (Resource : Type u)
    [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
    [FiniteQuantumSystem Resource] :=
  Fin count → DensityOperator Resource
structure IndependentInputErrorModel (count : Nat) (Resource : Type u)
    [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
    [FiniteQuantumSystem Resource] where
  rate : Fin count → ℝ
  rate_nonneg : ∀ i, 0 ≤ rate i
  rate_le_one : ∀ i, rate i ≤ 1
  admissible : (Fin count → ℝ) → ResourceInput count Resource → Prop
structure AdversarialWeightInputErrorModel (count : Nat) (Resource : Type u)
    [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
    [FiniteQuantumSystem Resource] where
  weight : ResourceInput count Resource → Nat
  maxWeight : Nat
structure LocalStochasticInputErrorModel (count : Nat) (Resource : Type u)
    [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
    [FiniteQuantumSystem Resource] where
  rate : ℝ
  rate_nonneg : 0 ≤ rate
  rate_le_one : rate ≤ 1
  admissible : ℝ → ResourceInput count Resource → Prop
inductive InputErrorModel (count : Nat) (Resource : Type u)
    [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
    [FiniteQuantumSystem Resource] where
  | independent (model : IndependentInputErrorModel count Resource)
  | adversarialWeight (model : AdversarialWeightInputErrorModel count Resource)
  | localStochastic (model : LocalStochasticInputErrorModel count Resource)
namespace InputErrorModel
variable {count : Nat} {Resource : Type u}
variable [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
variable [FiniteQuantumSystem Resource]
def Permits (model : InputErrorModel count Resource)
    (inputs : ResourceInput count Resource) : Prop :=
  match model with
  | .independent model => model.admissible model.rate inputs
  | .adversarialWeight model => model.weight inputs ≤ model.maxWeight
  | .localStochastic model => model.admissible model.rate inputs
@[simp]
theorem permits_independent
    (model : IndependentInputErrorModel count Resource)
    (inputs : ResourceInput count Resource) :
    Permits (.independent model) inputs ↔ model.admissible model.rate inputs :=
  Iff.rfl
@[simp]
theorem permits_adversarialWeight
    (model : AdversarialWeightInputErrorModel count Resource)
    (inputs : ResourceInput count Resource) :
    Permits (.adversarialWeight model) inputs ↔
      model.weight inputs ≤ model.maxWeight :=
  Iff.rfl
@[simp]
theorem permits_localStochastic
    (model : LocalStochasticInputErrorModel count Resource)
    (inputs : ResourceInput count Resource) :
    Permits (.localStochastic model) inputs ↔
      model.admissible model.rate inputs :=
  Iff.rfl
end InputErrorModel
inductive DistillationOutcome
  | accepted
  | rejected
deriving DecidableEq
instance : Fintype DistillationOutcome where
  elems := {.accepted, .rejected}
  complete := by intro outcome; cases outcome <;> simp
def outcomeWeight (successProbability : ℝ) : DistillationOutcome → ℝ
  | .accepted => successProbability
  | .rejected => 1 - successProbability
theorem outcomeWeight_nonneg {successProbability : ℝ}
    (h0 : 0 ≤ successProbability) (h1 : successProbability ≤ 1)
    (outcome : DistillationOutcome) :
    0 ≤ outcomeWeight successProbability outcome := by
  cases outcome with
  | accepted => exact h0
  | rejected =>
      simpa [outcomeWeight] using sub_nonneg.mpr h1
theorem outcomeWeight_sum (successProbability : ℝ) :
    ∑ outcome : DistillationOutcome, outcomeWeight successProbability outcome = 1 := by
  rw [show (Finset.univ : Finset DistillationOutcome) =
      {DistillationOutcome.accepted, DistillationOutcome.rejected} by decide]
  simp [outcomeWeight]
def branchState {Output : Type u}
    [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
    [FiniteQuantumSystem Output]
    (acceptedOutput rejectedOutput : DensityOperator Output) :
    DistillationOutcome → DensityOperator Output
  | .accepted => acceptedOutput
  | .rejected => rejectedOutput
noncomputable def outcomeMixture {Output : Type u}
    [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
    [FiniteQuantumSystem Output]
    (successProbability : ℝ) (h0 : 0 ≤ successProbability)
    (h1 : successProbability ≤ 1)
    (acceptedOutput rejectedOutput : DensityOperator Output) :
    DensityOperator Output :=
  DensityOperator.convexCombination Finset.univ
    (outcomeWeight successProbability)
    (branchState acceptedOutput rejectedOutput)
    (by
      intro outcome _houtcome
      exact outcomeWeight_nonneg h0 h1 outcome)
    (by
      simpa using outcomeWeight_sum successProbability)
structure DistillationRun (Resource Input Output : Type u)
    [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
    [FiniteQuantumSystem Resource]
    [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
    [FiniteQuantumSystem Input]
    [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
    [FiniteQuantumSystem Output] where
  resourceCount : Nat
  noisyInput : Fin resourceCount → DensityOperator Resource
  prepareInput :
    (Fin resourceCount → DensityOperator Resource) → DensityOperator Input
  operation : QuantumChannel Input Output
  successProbability : ℝ
  success_nonneg : 0 ≤ successProbability
  success_le_one : successProbability ≤ 1
  acceptedOutput : DensityOperator Output
  rejectedOutput : DensityOperator Output
  output_decomposition :
    operation.mapDensity (prepareInput noisyInput) =
      outcomeMixture successProbability success_nonneg success_le_one
        acceptedOutput rejectedOutput
namespace DistillationRun
variable {Resource Input Output : Type u}
variable [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
variable [FiniteQuantumSystem Resource]
variable [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
variable [FiniteQuantumSystem Input]
variable [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
variable [FiniteQuantumSystem Output]
noncomputable def rawOutput (run : DistillationRun Resource Input Output) :
    DensityOperator Output :=
  run.operation.mapDensity (run.prepareInput run.noisyInput)
def rejectionProbability (run : DistillationRun Resource Input Output) : ℝ :=
  1 - run.successProbability
def outcomeProbability (run : DistillationRun Resource Input Output) :
    DistillationOutcome → ℝ :=
  outcomeWeight run.successProbability
def conditionalOutput (run : DistillationRun Resource Input Output) :
    DistillationOutcome → DensityOperator Output :=
  branchState run.acceptedOutput run.rejectedOutput
@[simp]
theorem accepted_probability (run : DistillationRun Resource Input Output) :
    run.outcomeProbability .accepted = run.successProbability :=
  rfl
@[simp]
theorem rejected_probability (run : DistillationRun Resource Input Output) :
    run.outcomeProbability .rejected = run.rejectionProbability :=
  rfl
@[simp]
theorem accepted_conditionalOutput
    (run : DistillationRun Resource Input Output) :
    run.conditionalOutput .accepted = run.acceptedOutput :=
  rfl
@[simp]
theorem rejected_conditionalOutput
    (run : DistillationRun Resource Input Output) :
    run.conditionalOutput .rejected = run.rejectedOutput :=
  rfl
end DistillationRun
inductive ProtocolBehavior (Output : Type u)
    [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
    [FiniteQuantumSystem Output] where
  | postselected
  | activeCorrection (decoder : QuantumChannel Output Output)
namespace DistillationRun
variable {Resource Input Output : Type u}
variable [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
variable [FiniteQuantumSystem Resource]
variable [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
variable [FiniteQuantumSystem Input]
variable [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
variable [FiniteQuantumSystem Output]
noncomputable def reportedOutput
    (run : DistillationRun Resource Input Output) :
    ProtocolBehavior Output → DensityOperator Output
  | .postselected => run.acceptedOutput
  | .activeCorrection decoder => decoder.mapDensity run.rawOutput
@[simp]
theorem reportedOutput_postselected
    (run : DistillationRun Resource Input Output) :
    run.reportedOutput .postselected = run.acceptedOutput :=
  rfl
@[simp]
theorem reportedOutput_activeCorrection
    (run : DistillationRun Resource Input Output)
    (decoder : QuantumChannel Output Output) :
    run.reportedOutput (.activeCorrection decoder) =
      decoder.mapDensity run.rawOutput :=
  rfl
end DistillationRun
structure MagicStateDistillationProtocol (Resource Input Output : Type u)
    [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
    [FiniteQuantumSystem Resource]
    [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
    [FiniteQuantumSystem Input]
    [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
    [FiniteQuantumSystem Output] where
  run : DistillationRun Resource Input Output
  inputErrorModel : InputErrorModel run.resourceCount Resource
  inputPermitted : inputErrorModel.Permits run.noisyInput
  behavior : ProtocolBehavior Output
  idealOutput : DensityOperator Output
  outputError : DensityOperator Output → DensityOperator Output → ℝ
  outputError_nonneg : ∀ rho sigma, 0 ≤ outputError rho sigma
namespace MagicStateDistillationProtocol
variable {Resource Input Output : Type u}
variable [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
variable [FiniteQuantumSystem Resource]
variable [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
variable [FiniteQuantumSystem Input]
variable [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
variable [FiniteQuantumSystem Output]
def successfulOutputError
    (protocol : MagicStateDistillationProtocol Resource Input Output) : ℝ :=
  protocol.outputError protocol.run.acceptedOutput protocol.idealOutput
noncomputable def reportedOutputError
    (protocol : MagicStateDistillationProtocol Resource Input Output) : ℝ :=
  protocol.outputError
    (protocol.run.reportedOutput protocol.behavior) protocol.idealOutput
end MagicStateDistillationProtocol
end Distillation
namespace Semantics
namespace QuantumChannel
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
variable [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
variable [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L]
variable [FiniteQuantumSystem L]
theorem comp_mapDensity (Psi : QuantumChannel K L) (Phi : QuantumChannel H K)
    (rho : DensityOperator H) :
    (QuantumChannel.comp Psi Phi).mapDensity rho =
      Psi.mapDensity (Phi.mapDensity rho) := by
  rfl
end QuantumChannel
end Semantics
namespace Distillation
open Semantics
theorem mapDensity_outcomeMixture {Output Output' : Type u}
    [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
    [FiniteQuantumSystem Output]
    [NormedAddCommGroup Output'] [InnerProductSpace Complex Output']
    [FiniteQuantumSystem Output']
    (channel : QuantumChannel Output Output')
    (successProbability : ℝ) (h0 : 0 ≤ successProbability)
    (h1 : successProbability ≤ 1)
    (acceptedOutput rejectedOutput : DensityOperator Output) :
    channel.mapDensity
        (outcomeMixture successProbability h0 h1
          acceptedOutput rejectedOutput) =
      outcomeMixture successProbability h0 h1
        (channel.mapDensity acceptedOutput)
        (channel.mapDensity rejectedOutput) := by
  apply densityOperator_ext
  simp [outcomeMixture, DensityOperator.convexCombinationOperator,
    branchState, outcomeWeight,
    show (Finset.univ : Finset DistillationOutcome) =
      {DistillationOutcome.accepted, DistillationOutcome.rejected} by decide]
namespace DistillationRun
variable {Resource Input Output : Type u}
variable [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
variable [FiniteQuantumSystem Resource]
variable [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
variable [FiniteQuantumSystem Input]
variable [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
variable [FiniteQuantumSystem Output]
noncomputable def postprocess {Output' : Type u}
    [NormedAddCommGroup Output'] [InnerProductSpace Complex Output']
    [FiniteQuantumSystem Output']
    (run : DistillationRun Resource Input Output)
    (channel : QuantumChannel Output Output') :
    DistillationRun Resource Input Output' where
  resourceCount := run.resourceCount
  noisyInput := run.noisyInput
  prepareInput := run.prepareInput
  operation := QuantumChannel.comp channel run.operation
  successProbability := run.successProbability
  success_nonneg := run.success_nonneg
  success_le_one := run.success_le_one
  acceptedOutput := channel.mapDensity run.acceptedOutput
  rejectedOutput := channel.mapDensity run.rejectedOutput
  output_decomposition := by
    rw [Semantics.QuantumChannel.comp_mapDensity]
    rw [run.output_decomposition]
    exact mapDensity_outcomeMixture channel run.successProbability
      run.success_nonneg run.success_le_one run.acceptedOutput run.rejectedOutput
end DistillationRun
end Distillation
end QEC


