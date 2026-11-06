-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystemOperator
-- name    : QEC_Semantics_Instruments_Selection_SelectedSubsystemOperator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:11:40.651757+00:00
-- url     : https://prove2.me/theorems/29c75450-105a-4e77-9989-a3259c78935a
-- title:
--   Selected Subsystem Operator
-- statement:
--   Definitions and structural lemmas for Selected Subsystem Operator, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedSubsystemOperator.lean

import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystem
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
set_option autoImplicit false
universe u v
namespace QEC
namespace Semantics
open Classical
open scoped TensorProduct
noncomputable section
namespace FiniteInstrument
noncomputable def tensorPowerSelectedOutputBitstring
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (observedHistory : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts observedHistory).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (basisHistory : tensorPowerHistory (Qubit.Bitstring ι) attempts) :
    Qubit.Bitstring (Fin required × ι) :=
  tensorPowerSelectedBitstringEquiv accepts attempts observedHistory required
    hrequired ι
      ((tensorPowerSelectedSubsystem accepts attempts observedHistory required
        hrequired ι).splitBitstring
          (tensorPowerQubitBitstringEquiv ι attempts basisHistory)).1
noncomputable def tensorPowerSelectedComplementBitstring
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (observedHistory : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts observedHistory).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (basisHistory : tensorPowerHistory (Qubit.Bitstring ι) attempts) :
    Qubit.Bitstring
      (tensorPowerSelectedSubsystem accepts attempts observedHistory required
        hrequired ι).ComplementCoordinates :=
  ((tensorPowerSelectedSubsystem accepts attempts observedHistory required
      hrequired ι).splitBitstring
        (tensorPowerQubitBitstringEquiv ι attempts basisHistory)).2
noncomputable def tensorPowerSelectedHistoryBitstringEquiv
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (observedHistory : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts observedHistory).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    tensorPowerHistory (Qubit.Bitstring ι) attempts ≃
      Qubit.Bitstring (Fin required × ι) ×
        Qubit.Bitstring
          (tensorPowerSelectedSubsystem accepts attempts observedHistory required
            hrequired ι).ComplementCoordinates :=
  (tensorPowerQubitBitstringEquiv ι attempts).trans
    ((tensorPowerSelectedSubsystem accepts attempts observedHistory required
        hrequired ι).bitstringFactorization.trans
      (Equiv.prodCongr
        (tensorPowerSelectedBitstringEquiv accepts attempts observedHistory required
          hrequired ι)
        (Equiv.refl _)))
end FiniteInstrument
end
end Semantics
end QEC


