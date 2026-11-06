-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystem
-- name    : QEC_Semantics_Instruments_Selection_SelectedSubsystem
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:06:37.460338+00:00
-- url     : https://prove2.me/theorems/1ef9ff91-0152-4607-9921-56b06f604f4d
-- title:
--   Selected Subsystem
-- statement:
--   Definitions and structural lemmas for Selected Subsystem, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedSubsystem.lean

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_Basis
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerObservedAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBasis_succ_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBasis_zero_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitBitstringEquiv_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitRegisterTransport_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.mem_tensorPowerAcceptedIndices
attribute [local simp] QEC.Semantics.FiniteInstrument.mem_tensorPowerObservedAcceptedIndices
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerBasis_succ_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerBasis_zero_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitBitstringEquiv_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitRegisterTransport_apply_basis
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
attribute [local simp] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
universe u v
namespace QEC
namespace Semantics
noncomputable section
namespace FiniteInstrument
noncomputable def tensorPowerSelectedCoordinateEmbedding
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    (Fin required × ι) ↪ (Fin attempts × ι) := by
  refine
    { toFun := fun coordinate =>
        (tensorPowerAcceptedSelector accepts attempts history required hrequired coordinate.1,
          coordinate.2)
      inj' := ?_ }
  rintro ⟨first, firstPort⟩ ⟨second, secondPort⟩ heq
  have htrials :
      tensorPowerAcceptedSelector accepts attempts history required hrequired first =
        tensorPowerAcceptedSelector accepts attempts history required hrequired second :=
    congrArg Prod.fst heq
  have hports : firstPort = secondPort :=
    congrArg Prod.snd heq
  have hslots : first = second :=
    (tensorPowerAcceptedSelector accepts attempts history required hrequired).injective htrials
  exact Prod.ext hslots hports
noncomputable def tensorPowerSelectedSubsystem
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    FiniteSubsystem (Fin attempts × ι) where
  selected :=
    (Finset.univ : Finset (Fin required × ι)).map
      (tensorPowerSelectedCoordinateEmbedding accepts attempts history required hrequired ι)
theorem mem_tensorPowerSelectedSubsystem_iff
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (coordinate : Fin attempts × ι) :
    coordinate ∈
      (tensorPowerSelectedSubsystem accepts attempts history required hrequired ι).selected ↔
      ∃ selected : Fin required × ι,
        tensorPowerSelectedCoordinateEmbedding accepts attempts history required hrequired ι
          selected = coordinate := by
  change coordinate ∈ (Finset.univ : Finset (Fin required × ι)).map
      (tensorPowerSelectedCoordinateEmbedding accepts attempts history required hrequired ι) ↔ _
  constructor
  · intro hcoordinate
    rcases Finset.mem_map.mp hcoordinate with ⟨selected, -, hselected⟩
    exact ⟨selected, hselected⟩
  · rintro ⟨selected, hselected⟩
    exact Finset.mem_map.mpr ⟨selected, Finset.mem_univ _, hselected⟩
theorem tensorPowerSelectedCoordinateEmbedding_mem
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (selected : Fin required × ι) :
    tensorPowerSelectedCoordinateEmbedding accepts attempts history required hrequired ι
      selected ∈
      (tensorPowerSelectedSubsystem accepts attempts history required hrequired ι).selected :=
  (mem_tensorPowerSelectedSubsystem_iff accepts attempts history required hrequired ι
    (tensorPowerSelectedCoordinateEmbedding accepts attempts history required hrequired ι
      selected)).mpr ⟨selected, rfl⟩
noncomputable def tensorPowerSelectedCoordinateEquiv
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    (Fin required × ι) ≃
      (tensorPowerSelectedSubsystem accepts attempts history required hrequired ι).SelectedCoordinates := by
  apply Equiv.ofBijective
    (fun selected =>
      ⟨tensorPowerSelectedCoordinateEmbedding accepts attempts history required hrequired ι
          selected,
        tensorPowerSelectedCoordinateEmbedding_mem accepts attempts history required hrequired ι
          selected⟩)
  constructor
  · intro first second heq
    apply (tensorPowerSelectedCoordinateEmbedding accepts attempts history required hrequired ι).injective
    exact Subtype.ext_iff.mp heq
  · intro coordinate
    rcases (mem_tensorPowerSelectedSubsystem_iff accepts attempts history required hrequired ι
      coordinate.1).mp coordinate.2 with ⟨selected, hselected⟩
    refine ⟨selected, ?_⟩
    apply Subtype.ext
    exact hselected
@[simp] theorem tensorPowerSelectedCoordinateEquiv_apply_val
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (selected : Fin required × ι) :
    ((tensorPowerSelectedCoordinateEquiv accepts attempts history required hrequired ι selected :
      (tensorPowerSelectedSubsystem accepts attempts history required hrequired ι).SelectedCoordinates) :
      Fin attempts × ι) =
      tensorPowerSelectedCoordinateEmbedding accepts attempts history required hrequired ι selected :=
  rfl
@[simp] theorem tensorPowerSelectedCoordinateEmbedding_fst
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (selected : Fin required × ι) :
    (tensorPowerSelectedCoordinateEmbedding accepts attempts history required hrequired ι selected).1 =
      tensorPowerAcceptedSelector accepts attempts history required hrequired selected.1 :=
  rfl
noncomputable def tensorPowerSelectedBitstringEquiv
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    Qubit.Bitstring
      (tensorPowerSelectedSubsystem accepts attempts history required hrequired ι).SelectedCoordinates ≃
      Qubit.Bitstring (Fin required × ι) where
  toFun := fun bits selected =>
    bits (tensorPowerSelectedCoordinateEquiv accepts attempts history required hrequired ι selected)
  invFun := fun bits coordinate =>
    bits ((tensorPowerSelectedCoordinateEquiv accepts attempts history required hrequired ι).symm
      coordinate)
  left_inv := by
    intro bits
    funext coordinate
    simp
  right_inv := by
    intro bits
    funext selected
    simp
noncomputable def tensorPowerSelectedRegisterReindex
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    UnitaryTransport
      (Qubit.QubitRegister
        (tensorPowerSelectedSubsystem accepts attempts history required hrequired ι).SelectedCoordinates)
      (Qubit.QubitRegister (Fin required × ι)) := by
  let sourceBasis :=
    EuclideanSpace.basisFun
      (Qubit.Bitstring
        (tensorPowerSelectedSubsystem accepts attempts history required hrequired ι).SelectedCoordinates)
      Complex
  let targetBasis := EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex
  let U := sourceBasis.equiv targetBasis
    (tensorPowerSelectedBitstringEquiv accepts attempts history required hrequired ι)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }
noncomputable def tensorPowerSelectedPartialTraceChannel
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    QuantumChannel (tensorPowerCarrier (Qubit.QubitRegister ι) attempts)
      (Qubit.QubitRegister (Fin required × ι)) :=
  QuantumChannel.comp
    (QuantumChannel.unitaryConj
      (tensorPowerSelectedRegisterReindex accepts attempts history required hrequired ι))
    (QuantumChannel.comp
      (tensorPowerSelectedSubsystem accepts attempts history required hrequired ι).selectedPartialTraceFromRegister
      (QuantumChannel.unitaryConj (tensorPowerQubitRegisterTransport ι attempts)))
end FiniteInstrument
end
end Semantics
end QEC


