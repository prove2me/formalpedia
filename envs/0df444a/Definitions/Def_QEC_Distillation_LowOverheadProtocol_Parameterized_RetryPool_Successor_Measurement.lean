-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Measurement
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Measurement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T19:23:45.524201+00:00
-- url     : https://prove2.me/theorems/4b59ff54-60ac-4526-89b3-9a3e9482c48a
-- title:
--   Measurement
-- statement:
--   Definitions and structural lemmas for Measurement, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Measurement.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Preparation
import Definitions.Def_QEC_Semantics_Instruments_Registers_ChannelProduct
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm

set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite
noncomputable def decodedRetryPoolOneQubitRecordDensity
    (parameter : ErrorParameter) : DensityOperator QubitSpace :=
  aBasisTransport.symm.conjDensity (diagonalAResource parameter)
noncomputable def decodedRetryPoolSuccessorOneQubitRecordChannel :
    QuantumChannel QubitSpace QubitSpace :=
  QuantumChannel.comp
    (QuantumChannel.unitaryConj aBasisTransport.symm)
    (QuantumChannel.comp
      (QuantumChannel.unitaryConj
        (OneQubitMagic.phaseShiftTransport (Real.pi / 2)))
      decodedRetryPoolSuccessorOneQubitPreparation)
noncomputable def decodedRetryPoolSuccessorRecordPreparationChannel
    (m w z q : Nat) (stage : Fin z) :
    QuantumChannel
      (QubitRegister (decodedRetryPoolSuccessorSourceSlots m w z q stage))
      (QubitRegister (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :=
  tensorPowerRegisterSitewiseChannel
    (decodedRetryPoolQubitRegisterSitewiseChannel
      decodedRetryPoolSuccessorOneQubitRecordChannel
      (LogicalSite m w))
    (decodedRetryPoolBackwardSchedule m w z q stage)
end HH18Parameterized
end Distillation
end QEC


