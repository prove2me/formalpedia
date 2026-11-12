-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_AcceptedPortRecordProduct
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_AcceptedPortRecordProduct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T19:26:23.124589+00:00
-- url     : https://prove2.me/theorems/900e6b62-17b5-4bab-987f-6f8f149d9f77
-- title:
--   Accepted Port Record Product
-- statement:
--   Definitions and structural lemmas for Accepted Port Record Product, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/AcceptedPortRecordProduct.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_AcceptedProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Measurement
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProduct
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_complete
import Theorems.Thm_QEC_Semantics_QuantumChannel_toFiniteInstrument_complete

set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite
noncomputable def decodedRetryPoolSelectedPortChannel
    (m w : Nat) (port : LogicalSite m w) :
    QuantumChannel (LogicalRegister m w) QubitSpace :=
  QuantumChannel.comp
    (QuantumChannel.unitaryConj (selectedLogicalPortTransport m w port))
    (selectedLogicalPortSubsystem m w port).selectedPartialTraceFromRegister
noncomputable def decodedRetryPoolSelectedPortRecordChannel
    (m w : Nat) (port : LogicalSite m w) :
    QuantumChannel (LogicalRegister m w) QubitSpace :=
  QuantumChannel.comp
    decodedRetryPoolSuccessorOneQubitRecordChannel
    (decodedRetryPoolSelectedPortChannel m w port)
noncomputable def decodedRetryPoolSelectedPortRecordChannelTensorPower
    (m w : Nat) (port : LogicalSite m w) (required : Nat) :
    QuantumChannel
      (tensorPowerCarrier (LogicalRegister m w) required)
      (tensorPowerCarrier QubitSpace required) :=
  let channel := decodedRetryPoolSelectedPortRecordChannel m w port
  ((channel.toFiniteInstrument).tensorPower required).kraus.toQuantumChannel
    ((channel.toFiniteInstrument).tensorPower_complete
      channel.toFiniteInstrument_complete required)
noncomputable def decodedRetryPoolAcceptedPortRecordProductChannel
    (m w : Nat) (port : LogicalSite m w) (required : Nat) :
    QuantumChannel
      (QubitRegister (Fin required × LogicalSite m w))
      (tensorPowerCarrier QubitSpace required) :=
  QuantumChannel.comp
    (decodedRetryPoolSelectedPortRecordChannelTensorPower m w port required)
    (QuantumChannel.unitaryConj
      (tensorPowerQubitRegisterTransport (LogicalSite m w) required).symm)
end HH18Parameterized
end Distillation
end QEC


