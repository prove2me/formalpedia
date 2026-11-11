-- Prove2me | Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
-- name    : QEC_Distillation_Universality_AdaptiveIdealClifford
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T11:50:20.720374+00:00
-- url     : https://prove2.me/theorems/1eaf6c83-e21c-45db-9045-f709c876e85b
-- title:
--   Adaptive Ideal Clifford
-- statement:
--   Definitions and structural lemmas for Adaptive Ideal Clifford, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/AdaptiveIdealClifford.lean

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_apply_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_involutive
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_symm_apply
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_tensor_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenBranchDensity_toOperator
import Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenProjector_apply_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenProjector_branchState
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOddBranchDensity_toOperator
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOddProjector_apply_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOddProjector_branchState
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOperator_apply
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOperator_apply_basis
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_apply_basis
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_involutive
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_symm_apply
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_tensor_basis
attribute [local simp] QEC.Distillation.TwoQubit.zzEvenBranchDensity_toOperator
attribute [local simp] QEC.Distillation.TwoQubit.zzEvenProjector_apply_basis
attribute [local simp] QEC.Distillation.TwoQubit.zzEvenProjector_branchState
attribute [local simp] QEC.Distillation.TwoQubit.zzOddBranchDensity_toOperator
attribute [local simp] QEC.Distillation.TwoQubit.zzOddProjector_apply_basis
attribute [local simp] QEC.Distillation.TwoQubit.zzOddProjector_branchState
attribute [local simp] QEC.Distillation.TwoQubit.zzOperator_apply
attribute [local simp] QEC.Distillation.TwoQubit.zzOperator_apply_basis
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace AdaptiveIdealClifford
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open scoped TensorProduct
universe u v w
variable {H K R E : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
  [FiniteQuantumSystem K]
variable [NormedAddCommGroup R] [InnerProductSpace Complex R]
  [FiniteQuantumSystem R]
variable [NormedAddCommGroup E] [InnerProductSpace Complex E]
  [FiniteQuantumSystem E]
noncomputable def unitaryIdentity (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H] :
    UnitaryTransport H H where
  toLinearEquiv := LinearEquiv.refl Complex H
  map_inner := by
    intro x y
    rfl
noncomputable def unitaryCompose {L : Type u}
    [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
    (V : UnitaryTransport K L) (U : UnitaryTransport H K) :
    UnitaryTransport H L where
  toLinearEquiv := U.toLinearEquiv.trans V.toLinearEquiv
  map_inner := by
    intro x y
    change inner Complex (V (U x)) (V (U y)) = inner Complex x y
    simpa using (V.map_inner (U x) (U y)).trans (U.map_inner x y)
structure CliffordPresentation (Wire : Type v) [Fintype Wire] where
  hadamard : Wire → UnitaryTransport H H
  phase : Wire → UnitaryTransport H H
  controlledX : Wire → Wire → UnitaryTransport H H
  relabel : Equiv.Perm Wire → UnitaryTransport H H
inductive CliffordSyntax {Wire : Type v} [Fintype Wire]
    (presentation : CliffordPresentation (H := H) Wire) where
  | identity : CliffordSyntax presentation
  | hadamard (wire : Wire) : CliffordSyntax presentation
  | phase (wire : Wire) : CliffordSyntax presentation
  | controlledX (control target : Wire) : CliffordSyntax presentation
  | relabel (permutation : Equiv.Perm Wire) (gate : CliffordSyntax presentation) :
      CliffordSyntax presentation
  | tensor (left right : CliffordSyntax presentation) : CliffordSyntax presentation
  | compose (first second : CliffordSyntax presentation) : CliffordSyntax presentation
namespace CliffordSyntax
variable {Wire : Type v} [Fintype Wire]
variable {presentation : CliffordPresentation (H := H) Wire}
noncomputable def unitary : CliffordSyntax presentation → UnitaryTransport H H
  | .identity => unitaryIdentity H
  | .hadamard wire => presentation.hadamard wire
  | .phase wire => presentation.phase wire
  | .controlledX control target => presentation.controlledX control target
  | .relabel permutation gate =>
      unitaryCompose (presentation.relabel permutation) gate.unitary
  | .tensor left right => unitaryCompose right.unitary left.unitary
  | .compose first second => unitaryCompose second.unitary first.unitary
noncomputable def channel (gate : CliffordSyntax presentation) : QuantumChannel H H :=
  QuantumChannel.unitaryConj gate.unitary
@[simp] theorem unitary_identity : (identity : CliffordSyntax presentation).unitary =
    unitaryIdentity H :=
  rfl
@[simp] theorem unitary_hadamard (wire : Wire) :
    (CliffordSyntax.hadamard (presentation := presentation) wire).unitary =
    presentation.hadamard wire :=
  rfl
@[simp] theorem unitary_phase (wire : Wire) :
    (CliffordSyntax.phase (presentation := presentation) wire).unitary =
    presentation.phase wire :=
  rfl
@[simp] theorem unitary_controlledX (control target : Wire) :
    (CliffordSyntax.controlledX (presentation := presentation) control target).unitary =
    presentation.controlledX control target :=
  rfl
@[simp] theorem channel_apply (gate : CliffordSyntax presentation) (A : Operator H) :
    gate.channel A = gate.unitary.conjOperator A :=
  rfl
end CliffordSyntax
abbrev ResourceLedger (Token : Type v) := Multiset Token
def ResourceLedger.empty (Token : Type v) : ResourceLedger Token :=
  0
def ResourceLedger.debit {Token : Type v} (token : Token) : ResourceLedger Token :=
  {token}
structure ResourceUse (Token : Type v) where
  token : Token
  resource : DensityOperator R
  consumer : QuantumChannel (CompositeSystem H R) K
namespace ResourceUse
variable {Token : Type v}
noncomputable def run (use : ResourceUse (H := H) (K := K) (R := R) Token)
    (rho : DensityOperator H) : DensityOperator K :=
  use.consumer.mapDensity (DensityOperator.tensorDensity rho use.resource)
def ledger (use : ResourceUse (H := H) (K := K) (R := R) Token) :
    ResourceLedger Token :=
  ResourceLedger.debit use.token
@[simp] theorem run_toOperator
    (use : ResourceUse (H := H) (K := K) (R := R) Token)
    (rho : DensityOperator H) :
    (use.run rho).toOperator =
      use.consumer (DensityOperator.tensorDensity rho use.resource).toOperator :=
  rfl
@[simp] theorem ledger_eq_debit
    (use : ResourceUse (H := H) (K := K) (R := R) Token) :
    use.ledger = {use.token} :=
  rfl
end ResourceUse
structure HonestDiscard where
  factorization : UnitaryTransport H (CompositeSystem K E)
namespace HonestDiscard
noncomputable def channel (discard : HonestDiscard (H := H) (K := K) (E := E)) :
    QuantumChannel H K :=
  QuantumChannel.comp (partialTraceRightRaw_cptp K E)
    (QuantumChannel.unitaryConj discard.factorization)
noncomputable def run (discard : HonestDiscard (H := H) (K := K) (E := E))
    (rho : DensityOperator H) : DensityOperator K :=
  discard.channel.mapDensity rho
@[simp] theorem channel_apply (discard : HonestDiscard (H := H) (K := K) (E := E))
    (A : Operator H) :
    discard.channel A = partialTraceRightRaw K E (discard.factorization.conjOperator A) :=
  rfl
@[simp] theorem run_toOperator (discard : HonestDiscard (H := H) (K := K) (E := E))
    (rho : DensityOperator H) :
    (discard.run rho).toOperator =
      partialTraceRightRaw K E (discard.factorization.conjOperator rho.toOperator) :=
  rfl
end HonestDiscard
noncomputable def zeroQubitDensity : DensityOperator QubitSpace :=
  DensityOperator.pureOfNonzero
    (EuclideanSpace.basisFun (Fin 2) Complex 0)
    (by
      intro hzero
      have hcoordinate := congrArg (fun state : QubitSpace => state 0) hzero
      simpa using hcoordinate)
structure ZeroPreparationAdapter (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] where
  consumer : QuantumChannel (CompositeSystem H QubitSpace) K
namespace ZeroPreparationAdapter
variable {H K : Type}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
noncomputable def run (adapter : ZeroPreparationAdapter (H := H) (K := K))
    (rho : DensityOperator H) : DensityOperator K :=
  adapter.consumer.mapDensity (DensityOperator.tensorDensity rho zeroQubitDensity)
end ZeroPreparationAdapter
structure RawOutcomeBranch (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H] where
  operator : Operator H
  weight : ℝ
structure JointMeasurement (ι : Type u) [Fintype ι] [DecidableEq ι]
    (κ : Type v) [Fintype κ] [DecidableEq κ] where
  checks : κ → Binary ι
  commute : ∀ left right, Commutes (checks left) (checks right)
namespace JointMeasurement
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ] [DecidableEq κ]
noncomputable def instrument (measurement : JointMeasurement ι κ) :
    FiniteInstrument (JointSyndrome κ) (JointSyndrome κ)
      (QubitRegister ι) (QubitRegister ι) :=
  jointStabilizerInstrument measurement.checks measurement.commute
noncomputable def branch (measurement : JointMeasurement ι κ)
    (syndrome : JointSyndrome κ) (rho : DensityOperator (QubitRegister ι)) :
    RawOutcomeBranch (QubitRegister ι) where
  operator := (measurement.instrument.branchOperator syndrome rho.toOperator)
  weight := measurement.instrument.bornWeight syndrome rho
noncomputable def conditionalDensity (measurement : JointMeasurement ι κ)
    (syndrome : JointSyndrome κ) (rho : DensityOperator (QubitRegister ι))
    (hpositive : 0 < (measurement.branch syndrome rho).weight) :
    DensityOperator (QubitRegister ι) :=
  measurement.instrument.conditionalDensity syndrome rho hpositive
end JointMeasurement
abbrev AdaptiveHistory (κ : Type v) := List (JointSyndrome κ ⊕ Bool)
inductive DeterministicStep {ι : Type} [Fintype ι] [DecidableEq ι]
    {Wire : Type} [Fintype Wire] (Token : Type)
    (presentation : CliffordPresentation (H := QubitRegister ι) Wire) where
  | clifford (gate : CliffordSyntax presentation) :
      DeterministicStep Token presentation
  | resource (use : ResourceUse (H := QubitRegister ι) (K := QubitRegister ι)
      (R := QubitSpace) Token) : DeterministicStep Token presentation
  | discard (E : Type) [NormedAddCommGroup E] [InnerProductSpace Complex E]
      [FiniteQuantumSystem E]
      (discard : HonestDiscard (H := QubitRegister ι) (K := QubitRegister ι)
        (E := E)) : DeterministicStep Token presentation
  | zeroPreparation (adapter : ZeroPreparationAdapter
      (H := QubitRegister ι) (K := QubitRegister ι)) :
      DeterministicStep Token presentation
namespace DeterministicStep
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {Wire : Type} [Fintype Wire] {Token : Type}
variable {presentation : CliffordPresentation (H := QubitRegister ι) Wire}
noncomputable def run : DeterministicStep Token presentation →
    DensityOperator (QubitRegister ι) → DensityOperator (QubitRegister ι)
  | .clifford gate => fun rho => gate.channel.mapDensity rho
  | .resource use => fun rho => use.run rho
  | @discard _ _ _ _ _ _ _ E instNormed instInner instFinite honestDiscard => fun rho =>
      letI : NormedAddCommGroup E := instNormed
      letI : InnerProductSpace Complex E := instInner
      letI : FiniteQuantumSystem E := instFinite
      honestDiscard.run rho
  | .zeroPreparation adapter => fun rho => adapter.run rho
def ledger : DeterministicStep Token presentation → ResourceLedger Token
  | .clifford _ => ResourceLedger.empty Token
  | .resource use => use.ledger
  | @discard _ _ _ _ _ _ _ _ _ _ _ _ => ResourceLedger.empty Token
  | .zeroPreparation _ => ResourceLedger.empty Token
end DeterministicStep
inductive AdaptiveProgram {ι : Type} [Fintype ι] [DecidableEq ι]
    (κ : Type) [Fintype κ] [DecidableEq κ]
    {Wire : Type} [Fintype Wire] (Token : Type)
    (presentation : CliffordPresentation (H := QubitRegister ι) Wire) where
  | terminal (deferred : CliffordSyntax presentation) :
      AdaptiveProgram κ Token presentation
  | deterministic (step : DeterministicStep Token presentation)
      (next : AdaptiveProgram κ Token presentation) :
      AdaptiveProgram κ Token presentation
  | coin (next : Bool → AdaptiveProgram κ Token presentation) :
      AdaptiveProgram κ Token presentation
  | measure (measurement : JointMeasurement ι κ)
      (next : JointSyndrome κ → AdaptiveProgram κ Token presentation) :
      AdaptiveProgram κ Token presentation
namespace AdaptiveProgram
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable {Wire : Type} [Fintype Wire] {Token : Type}
variable {presentation : CliffordPresentation (H := QubitRegister ι) Wire}
structure TerminalBranch (ι : Type) [Fintype ι] [DecidableEq ι]
    (κ : Type) [Fintype κ] [DecidableEq κ] (Token : Type) where
  history : AdaptiveHistory κ
  weight : ℝ
  positive : 0 < weight
  ledger : ResourceLedger Token
  output : DensityOperator (QubitRegister ι)
noncomputable def TerminalBranch.rawOperator (branch : TerminalBranch
    (ι := ι) (κ := κ) (Token := Token)) : Operator (QubitRegister ι) :=
  (branch.weight : Complex) • branch.output.toOperator
def TerminalBranch.prependDeterministic (debit : ResourceLedger Token)
    (branch : TerminalBranch (ι := ι) (κ := κ) (Token := Token)) :
    TerminalBranch (ι := ι) (κ := κ) (Token := Token) where
  history := branch.history
  weight := branch.weight
  positive := branch.positive
  ledger := debit + branch.ledger
  output := branch.output
noncomputable def TerminalBranch.prependCoin (coin : Bool)
    (branch : TerminalBranch (ι := ι) (κ := κ) (Token := Token)) :
    TerminalBranch (ι := ι) (κ := κ) (Token := Token) where
  history := Sum.inr coin :: branch.history
  weight := (1 / 2 : ℝ) * branch.weight
  positive := mul_pos (by norm_num) branch.positive
  ledger := branch.ledger
  output := branch.output
noncomputable def TerminalBranch.prependSyndrome (measurement : JointMeasurement ι κ)
    (syndrome : JointSyndrome κ) (rho : DensityOperator (QubitRegister ι))
    (hpositive : 0 < (measurement.branch syndrome rho).weight)
    (branch : TerminalBranch (ι := ι) (κ := κ) (Token := Token)) :
    TerminalBranch (ι := ι) (κ := κ) (Token := Token) where
  history := Sum.inl syndrome :: branch.history
  weight := (measurement.branch syndrome rho).weight * branch.weight
  positive := mul_pos hpositive branch.positive
  ledger := branch.ledger
  output := branch.output
noncomputable def eval : AdaptiveProgram κ Token presentation →
    DensityOperator (QubitRegister ι) →
      Multiset (TerminalBranch (ι := ι) (κ := κ) (Token := Token))
  | .terminal deferred, rho =>
      { { history := []
          weight := 1
          positive := by norm_num
          ledger := ResourceLedger.empty Token
          output := deferred.channel.mapDensity rho } }
  | .deterministic step next, rho =>
      (next.eval (step.run rho)).map (TerminalBranch.prependDeterministic step.ledger)
  | .coin next, rho =>
      ((next false).eval rho).map (TerminalBranch.prependCoin false) +
        ((next true).eval rho).map (TerminalBranch.prependCoin true)
  | .measure measurement next, rho =>
      Finset.univ.1.bind fun syndrome =>
        if hpositive : 0 < (measurement.branch syndrome rho).weight then
          ((next syndrome).eval (measurement.conditionalDensity syndrome rho hpositive)).map
            (TerminalBranch.prependSyndrome measurement syndrome rho hpositive)
        else 0
def totalWeight
    (branches : Multiset (TerminalBranch (ι := ι) (κ := κ) (Token := Token))) : ℝ :=
  (branches.map TerminalBranch.weight).sum
def MeasurementFamiliesCommute (left right : κ → Binary ι) : Prop :=
  ∀ first second, Commutes (left first) (right second)
def branchLocalCommutation : AdaptiveProgram κ Token presentation →
    List (κ → Binary ι) → Prop
  | .terminal _, _ => True
  | .deterministic _ next, history => branchLocalCommutation next history
  | .coin next, history => ∀ coin, branchLocalCommutation (next coin) history
  | .measure measurement next, history =>
      (∀ previous ∈ history, MeasurementFamiliesCommute measurement.checks previous) ∧
        ∀ syndrome, branchLocalCommutation (next syndrome) (measurement.checks :: history)
def Valid (program : AdaptiveProgram κ Token presentation) : Prop :=
  branchLocalCommutation program []
noncomputable def TerminalBranch.bind
    (first second : TerminalBranch (ι := ι) (κ := κ) (Token := Token)) :
    TerminalBranch (ι := ι) (κ := κ) (Token := Token) where
  history := first.history ++ second.history
  weight := first.weight * second.weight
  positive := mul_pos first.positive second.positive
  ledger := first.ledger + second.ledger
  output := second.output
noncomputable def bindEval
    (branches : Multiset (TerminalBranch (ι := ι) (κ := κ) (Token := Token)))
    (next : TerminalBranch (ι := ι) (κ := κ) (Token := Token) →
      AdaptiveProgram κ Token presentation) :
    Multiset (TerminalBranch (ι := ι) (κ := κ) (Token := Token)) :=
  branches.bind fun first =>
    ((next first).eval first.output).map (TerminalBranch.bind first)
noncomputable def aggregateRaw
    (branches : Multiset (TerminalBranch (ι := ι) (κ := κ) (Token := Token))) :
    Operator (QubitRegister ι) :=
  (branches.map TerminalBranch.rawOperator).sum
noncomputable def outputOperator
    (program : AdaptiveProgram κ Token presentation)
    (rho : DensityOperator (QubitRegister ι)) : Operator (QubitRegister ι) :=
  aggregateRaw (program.eval rho)
def ImplementsChannel (program : AdaptiveProgram κ Token presentation)
    (target : QuantumChannel (QubitRegister ι) (QubitRegister ι)) : Prop :=
  ∀ rho : DensityOperator (QubitRegister ι), program.outputOperator rho = target rho.toOperator
def ImplementsObserved
    (program : AdaptiveProgram κ Token presentation)
    (target : AdaptiveHistory κ → DensityOperator (QubitRegister ι) →
      Operator (QubitRegister ι)) : Prop :=
  ∀ (rho : DensityOperator (QubitRegister ι)) branch,
    branch ∈ program.eval rho → branch.rawOperator = target branch.history rho
def selectEvent (event : TerminalBranch (ι := ι) (κ := κ) (Token := Token) → Prop)
    [DecidablePred event]
    (branches : Multiset (TerminalBranch (ι := ι) (κ := κ) (Token := Token))) :
    Multiset (TerminalBranch (ι := ι) (κ := κ) (Token := Token)) :=
  branches.filter event
def eventWeight (event : TerminalBranch (ι := ι) (κ := κ) (Token := Token) → Prop)
    [DecidablePred event]
    (branches : Multiset (TerminalBranch (ι := ι) (κ := κ) (Token := Token))) : ℝ :=
  totalWeight (selectEvent event branches)
noncomputable def TerminalBranch.condition
    (eventMass : ℝ) (hpositive : 0 < eventMass)
    (branch : TerminalBranch (ι := ι) (κ := κ) (Token := Token)) :
    TerminalBranch (ι := ι) (κ := κ) (Token := Token) where
  history := branch.history
  weight := eventMass⁻¹ * branch.weight
  positive := mul_pos (inv_pos.mpr hpositive) branch.positive
  ledger := branch.ledger
  output := branch.output
noncomputable def conditionEvent
    (event : TerminalBranch (ι := ι) (κ := κ) (Token := Token) → Prop)
    [DecidablePred event]
    (branches : Multiset (TerminalBranch (ι := ι) (κ := κ) (Token := Token)))
    (hpositive : 0 < eventWeight event branches) :
    Multiset (TerminalBranch (ι := ι) (κ := κ) (Token := Token)) :=
  (selectEvent event branches).map
    (TerminalBranch.condition (eventWeight event branches) hpositive)
def ImplementsPostselected
    (program : AdaptiveProgram κ Token presentation)
    (event : TerminalBranch (ι := ι) (κ := κ) (Token := Token) → Prop)
    [DecidablePred event]
    (target : DensityOperator (QubitRegister ι) → Operator (QubitRegister ι)) : Prop :=
  ∀ (rho : DensityOperator (QubitRegister ι))
    (hpositive : 0 < eventWeight event (program.eval rho)),
    aggregateRaw (conditionEvent event (program.eval rho) hpositive) = target rho
noncomputable def TerminalBranch.postprocess
    (channel : QuantumChannel (QubitRegister ι) (QubitRegister ι))
    (branch : TerminalBranch (ι := ι) (κ := κ) (Token := Token)) :
    TerminalBranch (ι := ι) (κ := κ) (Token := Token) where
  history := branch.history
  weight := branch.weight
  positive := branch.positive
  ledger := branch.ledger
  output := channel.mapDensity branch.output
end AdaptiveProgram
end AdaptiveIdealClifford
end Distillation
end QEC


