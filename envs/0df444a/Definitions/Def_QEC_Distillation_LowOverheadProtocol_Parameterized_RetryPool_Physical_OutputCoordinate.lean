-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_OutputCoordinate
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_OutputCoordinate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T20:59:24.567303+00:00
-- url     : https://prove2.me/theorems/758eb917-76d4-4b3e-ba4a-ba39ee6f2aaf
-- title:
--   Output Coordinate
-- statement:
--   Definitions and structural lemmas for Output Coordinate, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/OutputCoordinate.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Run
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Accounting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_AcceptedPortRecordProduct
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
abbrev decodedRetryPoolPhysicalProtocolOutputCoordinate
    (m w z q : Nat) (hz : 0 < z) :=
  routedDepthOutputSlots m w (z - 1) ×
    (Fin (decodedRetryPoolBackwardSchedule m w z q
      (decodedRetryPoolProtocolTerminalStage z hz)) × LogicalSite m w)
noncomputable def decodedRetryPoolAcceptedProductCoordinateChannel
    (m w required : Nat) (block : Fin required) (port : LogicalSite m w) :
    QuantumChannel
      (QubitRegister (Fin required × LogicalSite m w)) QubitSpace :=
  QuantumChannel.comp
    (decodedRetryPoolQubitRegisterCoordinateChannel (LogicalSite m w) port)
    (tensorPowerRegisterTrialChannel (LogicalSite m w) required block)
noncomputable def decodedRetryPoolPhysicalProtocolTerminalCoordinateChannel
    (m w z q : Nat) (hz : 0 < z)
    (coordinate :
      decodedRetryPoolPhysicalProtocolOutputCoordinate m w z q hz) :
    QuantumChannel
      (decodedRetryPoolPhysicalProtocolOutputCarrier m w z q hz) QubitSpace :=
  QuantumChannel.comp
    (decodedRetryPoolAcceptedProductCoordinateChannel m w
      (decodedRetryPoolBackwardSchedule m w z q
        (decodedRetryPoolProtocolTerminalStage z hz))
      coordinate.2.1 coordinate.2.2)
    (nestedTensorCoordinateOperator
      (QubitRegister
        (Fin (decodedRetryPoolBackwardSchedule m w z q
          (decodedRetryPoolProtocolTerminalStage z hz)) × LogicalSite m w))
      (logicalOutputCount m w) (z - 1)
      ((decodedRetryPoolNestedPathEquiv m w (z - 1)).symm coordinate.1))
noncomputable def decodedRetryPoolPhysicalProtocolCoordinateRawError
    (m w z q : Nat) (hz : 0 < z)
    (coordinate :
      decodedRetryPoolPhysicalProtocolOutputCoordinate m w z q hz)
    (rho : DensityOperator
      (decodedRetryPoolPhysicalProtocolOutputCarrier m w z q hz)) : Real :=
  aBasisInstrument.bornWeight .negative
    ((decodedRetryPoolPhysicalProtocolTerminalCoordinateChannel
      m w z q hz coordinate).mapDensity rho)
end HH18Parameterized
end Distillation
end QEC


