-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_GlobalBridge
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_GlobalBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T20:12:15.691207+00:00
-- url     : https://prove2.me/theorems/dd6123e1-3864-4b6c-a280-0ca7168abb46
-- title:
--   Global Bridge
-- statement:
--   Definitions and structural lemmas for Global Bridge, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/GlobalBridge.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_BranchOperator
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
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
noncomputable def decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalOuterAux
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (previous : Fin z)
    (hstage : previous.1 + 1 < z)
    (path : routedDepthOutputSlots m w (previous.1 + 1))
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) :
    Operator (tensorPowerCarrier
      (QubitRegister
        (Fin (decodedRetryPoolBackwardSchedule m w z q
          ⟨previous.1 + 1, hstage⟩) × LogicalSite m w))
      (logicalOutputCount m w)) :=
  bindNestedFilteredCoordinateOperator
    (logicalOutputCount m w) previous.1
    (decodedRetryPoolProtocolInstrumentAux
      h hdegree z q hz previous.1 previous.2)
    (decodedRetryPoolSuccessorStageInstrument
      h hdegree z q previous hstage)
    (fun priorOutcome =>
      decodedRetryPoolProtocolPathSuccessfulRoutingAux
        m w z q previous.1 previous.2
          (routedDepthOutputPathInit m w previous.1 path) priorOutcome = true)
    (fun successorOutcome =>
      decodedRetryPoolSuccessorStageSelectedPoolEnough
        m w z q previous hstage
          (routedDepthOutputPathLast m w previous.1 path) successorOutcome = true)
    ((decodedRetryPoolNestedPathEquiv m w previous.1).symm
      (routedDepthOutputPathInit m w previous.1 path))
    rho.toOperator
noncomputable def decodedRetryPoolProtocolPathSuccessorEnoughGlobalOperator
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (previous : Fin z) (hstage : previous.1 + 1 < z)
    (port : LogicalSite m w)
    (A : Operator (QubitRegister
      (Fin (decodedRetryPoolBackwardSchedule m w z q
        previous) × LogicalSite m w))) :
    Operator (tensorPowerCarrier
      (QubitRegister
        (Fin (decodedRetryPoolBackwardSchedule m w z q
          ⟨previous.1 + 1, hstage⟩) × LogicalSite m w))
      (logicalOutputCount m w)) :=
  filteredBranchOperatorSum
    (decodedRetryPoolSuccessorStageInstrument
      h hdegree z q previous hstage)
    (fun successorOutcome =>
      decodedRetryPoolSuccessorStageSelectedPoolEnough
        m w z q previous hstage port successorOutcome = true)
    A
noncomputable def decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalPriorAux
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (previous : Fin z)
    (priorPath : routedDepthOutputSlots m w previous.1)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) :
    Operator (QubitRegister
      (Fin (decodedRetryPoolBackwardSchedule m w z q
        previous) × LogicalSite m w)) :=
  nestedFilteredPredecessorCoordinateOperator
    (logicalOutputCount m w) previous.1
    (decodedRetryPoolProtocolInstrumentAux
      h hdegree z q hz previous.1 previous.2)
    (fun priorOutcome =>
      decodedRetryPoolProtocolPathSuccessfulRoutingAux
        m w z q previous.1 previous.2 priorPath priorOutcome = true)
    ((decodedRetryPoolNestedPathEquiv m w previous.1).symm priorPath)
    rho.toOperator
end HH18Parameterized
end Distillation
end QEC


