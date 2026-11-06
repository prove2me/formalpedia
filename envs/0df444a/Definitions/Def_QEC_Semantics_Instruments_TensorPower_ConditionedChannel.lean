-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_TensorPower_ConditionedChannel
-- name    : QEC_Semantics_Instruments_TensorPower_ConditionedChannel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:49:35.721235+00:00
-- url     : https://prove2.me/theorems/a820d127-a123-42b3-b93a-c587dfb420dd
-- title:
--   Conditioned Channel
-- statement:
--   Definitions and structural lemmas for Conditioned Channel, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ConditionedChannel.lean

import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystem
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
set_option autoImplicit false
universe v w
namespace QEC
namespace Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
namespace FiniteInstrument
noncomputable def fixedDensityReplacementSwap (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] :
    UnitaryTransport (CompositeSystem H K) (CompositeSystem K H) := by
  let U := TensorProduct.commIsometry Complex H K
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }
noncomputable def fixedDensityReplacementChannel (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (sigma : DensityOperator K) : QuantumChannel H K :=
  QuantumChannel.comp (partialTraceRightRaw_cptp K H)
    (QuantumChannel.comp
      (QuantumChannel.unitaryConj (fixedDensityReplacementSwap H K))
      (ThermalEncoding.prepareRight H K sigma))
noncomputable def tensorPowerHistoryConditionedChannel
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts) (required : Nat)
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (shortageState : DensityOperator (Qubit.QubitRegister (Fin required × ι))) :
    QuantumChannel (tensorPowerCarrier (Qubit.QubitRegister ι) attempts)
      (Qubit.QubitRegister (Fin required × ι)) :=
  if hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card then
    tensorPowerSelectedPartialTraceChannel accepts attempts history required hrequired ι
  else
    fixedDensityReplacementChannel
      (tensorPowerCarrier (Qubit.QubitRegister ι) attempts)
      (Qubit.QubitRegister (Fin required × ι)) shortageState
noncomputable def tensorPowerHistoryConditionedInstrument
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω]
    (I : FiniteInstrument κ Ω H (Qubit.QubitRegister ι))
    (accepts : Ω → Prop) [DecidablePred accepts]
    (attempts required : Nat)
    (shortageState : DensityOperator (Qubit.QubitRegister (Fin required × ι))) :
    FiniteInstrument
      (Sigma fun firstIndex : tensorPowerHistory κ attempts =>
        Fin ((tensorPowerHistoryConditionedChannel accepts attempts
          ((I.tensorPower attempts).observe firstIndex) required ι shortageState).chosenKrausCount))
      (Sigma fun _ : tensorPowerHistory Ω attempts => PUnit)
      (tensorPowerCarrier H attempts)
      (Qubit.QubitRegister (Fin required × ι)) :=
  (I.tensorPower attempts).bindDependent
    (fun history =>
      QuantumChannel.toFiniteInstrument
        (tensorPowerHistoryConditionedChannel accepts attempts history required ι shortageState))
end FiniteInstrument
end
end Semantics
end QEC


