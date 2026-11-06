-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedTrialComplement
-- name    : QEC_Semantics_Instruments_Selection_SelectedTrialComplement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:26:29.977372+00:00
-- url     : https://prove2.me/theorems/a49f3118-315b-43d9-b610-980512f00a09
-- title:
--   Selected Trial Complement
-- statement:
--   Definitions and structural lemmas for Selected Trial Complement, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedTrialComplement.lean

import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystemOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerObservedAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBasis_succ_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBasis_zero_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitBitstringEquiv_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitRegisterTransport_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedComplementBitstring_equiv_symm
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedHistoryBitstringEquiv_apply_fst
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedHistoryBitstringEquiv_apply_snd
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedOutputBitstring_equiv_symm
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedPartialTraceChannel_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedRegisterReindex_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
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
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedComplementBitstring_equiv_symm
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedHistoryBitstringEquiv_apply_fst
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedHistoryBitstringEquiv_apply_snd
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedOutputBitstring_equiv_symm
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedPartialTraceChannel_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedRegisterReindex_apply_basis
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
attribute [local simp] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
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
universe u v
namespace QEC
namespace Semantics
open Classical
open scoped BigOperators
noncomputable section
namespace FiniteInstrument
noncomputable def tensorPowerSelectedTrials
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card) :
    Finset (Fin attempts) :=
  Finset.univ.map
    (tensorPowerAcceptedSelector accepts attempts history required hrequired).toEmbedding
theorem mem_tensorPowerSelectedTrials_iff
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card)
    (trial : Fin attempts) :
    trial ∈ tensorPowerSelectedTrials accepts attempts history required hrequired ↔
      ∃ slot : Fin required,
        tensorPowerAcceptedSelector accepts attempts history required hrequired slot =
          trial := by
  simp [tensorPowerSelectedTrials]
theorem tensorPowerSelectedSubsystem_coordinate_mem_iff_trial_mem
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (coordinate : Fin attempts × ι) :
    coordinate ∈
        (tensorPowerSelectedSubsystem accepts attempts history required hrequired
          ι).selected ↔
      coordinate.1 ∈
        tensorPowerSelectedTrials accepts attempts history required hrequired := by
  rw [mem_tensorPowerSelectedSubsystem_iff,
    mem_tensorPowerSelectedTrials_iff]
  constructor
  · rintro ⟨⟨slot, port⟩, heq⟩
    exact ⟨slot, congrArg Prod.fst heq⟩
  · rintro ⟨slot, htrial⟩
    refine ⟨(slot, coordinate.2), ?_⟩
    exact Prod.ext htrial rfl
abbrev tensorPowerUnselectedTrial
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card) : Type :=
  {trial : Fin attempts //
    trial ∉ tensorPowerSelectedTrials accepts attempts history required hrequired}
noncomputable def tensorPowerSelectedComplementCoordinateEquiv
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    (tensorPowerUnselectedTrial accepts attempts history required hrequired × ι) ≃
      (tensorPowerSelectedSubsystem accepts attempts history required hrequired
        ι).ComplementCoordinates := by
  apply Equiv.ofBijective
    (fun coordinate =>
      ⟨(coordinate.1.1, coordinate.2), by
        intro hmem
        exact coordinate.1.2
          ((tensorPowerSelectedSubsystem_coordinate_mem_iff_trial_mem accepts
            attempts history required hrequired ι _).mp hmem)⟩)
  constructor
  · rintro ⟨firstTrial, firstPort⟩ ⟨secondTrial, secondPort⟩ heq
    have hpairs : (firstTrial.1, firstPort) = (secondTrial.1, secondPort) :=
      congrArg Subtype.val heq
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst hpairs)
    · exact congrArg (fun pair : Fin attempts × ι => pair.2) hpairs
  · intro coordinate
    have hunselected : coordinate.1.1 ∉
        tensorPowerSelectedTrials accepts attempts history required hrequired := by
      intro htrial
      exact coordinate.2
        ((tensorPowerSelectedSubsystem_coordinate_mem_iff_trial_mem accepts
          attempts history required hrequired ι coordinate.1).mpr htrial)
    refine ⟨(⟨coordinate.1.1, hunselected⟩, coordinate.1.2), ?_⟩
    apply Subtype.ext
    rfl
@[simp] theorem tensorPowerSelectedComplementCoordinateEquiv_apply_val
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (trial : tensorPowerUnselectedTrial accepts attempts history required hrequired)
    (port : ι) :
    ((tensorPowerSelectedComplementCoordinateEquiv accepts attempts history required
      hrequired ι (trial, port) :
        (tensorPowerSelectedSubsystem accepts attempts history required hrequired
          ι).ComplementCoordinates) : Fin attempts × ι) =
      (trial.1, port) :=
  rfl
noncomputable def tensorPowerSelectedComplementTrialBitstringEquiv
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    Qubit.Bitstring
        (tensorPowerSelectedSubsystem accepts attempts history required hrequired
          ι).ComplementCoordinates ≃
      (tensorPowerUnselectedTrial accepts attempts history required hrequired →
        Qubit.Bitstring ι) where
  toFun := fun bits trial port =>
    bits (tensorPowerSelectedComplementCoordinateEquiv accepts attempts history
      required hrequired ι (trial, port))
  invFun := fun bits coordinate =>
    bits ((tensorPowerSelectedComplementCoordinateEquiv accepts attempts history
      required hrequired ι).symm coordinate).1
      ((tensorPowerSelectedComplementCoordinateEquiv accepts attempts history
        required hrequired ι).symm coordinate).2
  left_inv := by
    intro bits
    funext coordinate
    simp
  right_inv := by
    intro bits
    funext trial port
    simp
noncomputable def tensorPowerSelectedAndUnselectedTrialEquiv
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card) :
    (Fin required ⊕
      tensorPowerUnselectedTrial accepts attempts history required hrequired) ≃
        Fin attempts := by
  apply Equiv.ofBijective
    (Sum.elim
      (tensorPowerAcceptedSelector accepts attempts history required hrequired)
      Subtype.val)
  constructor
  · intro first second heq
    cases first with
    | inl firstSlot =>
        cases second with
        | inl secondSlot =>
            exact congrArg Sum.inl
              ((tensorPowerAcceptedSelector accepts attempts history required
                hrequired).injective heq)
        | inr secondTrial =>
            exact (secondTrial.2
              ((mem_tensorPowerSelectedTrials_iff accepts attempts history required
                hrequired secondTrial.1).mpr ⟨firstSlot, heq⟩)).elim
    | inr firstTrial =>
        cases second with
        | inl secondSlot =>
            exact (firstTrial.2
              ((mem_tensorPowerSelectedTrials_iff accepts attempts history required
                hrequired firstTrial.1).mpr ⟨secondSlot, heq.symm⟩)).elim
        | inr secondTrial =>
            exact congrArg Sum.inr (Subtype.ext heq)
  · intro trial
    by_cases htrial : trial ∈
        tensorPowerSelectedTrials accepts attempts history required hrequired
    · rcases (mem_tensorPowerSelectedTrials_iff accepts attempts history required
        hrequired trial).mp htrial with ⟨slot, hslot⟩
      exact ⟨Sum.inl slot, hslot⟩
    · exact ⟨Sum.inr ⟨trial, htrial⟩, rfl⟩
end FiniteInstrument
end
end Semantics
end QEC


