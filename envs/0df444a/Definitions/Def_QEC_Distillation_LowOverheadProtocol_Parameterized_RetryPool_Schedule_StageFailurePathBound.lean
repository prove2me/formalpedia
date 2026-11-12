-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_StageFailurePathBound
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_StageFailurePathBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T20:14:35.792746+00:00
-- url     : https://prove2.me/theorems/8d46a4d6-b4a3-4474-bdc1-b021bea26eb7
-- title:
--   Stage Failure Path Bound
-- statement:
--   Definitions and structural lemmas for Stage Failure Path Bound, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/StageFailurePathBound.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_GlobalBridge
import Definitions.Def_QEC_Semantics_Instruments_Sequential_NestedFilteredMarginalBranchOperator
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
local instance instStageFailurePathBoundClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
attribute [local instance] QEC.Distillation.HH18Parameterized.instStageFailurePathBoundClassicalDecidable
abbrev decodedRetryPoolSuccessorStageOutputCarrier
    (m w z q stage : Nat) (hstage : stage + 1 < z) :=
  tensorPowerCarrier
    (QubitRegister
      (Fin (decodedRetryPoolBackwardSchedule m w z q
        ⟨stage + 1, hstage⟩) × LogicalSite m w))
    (logicalOutputCount m w)
noncomputable def decodedRetryPoolProtocolPathFailureTraceAux
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage + 1 < z)
    (path : nestedTensorPath (logicalOutputCount m w) stage)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) : Real :=
  Complex.re (LinearMap.trace Complex
    (decodedRetryPoolSuccessorStageOutputCarrier m w z q stage hstage)
    (filteredBranchOperatorSum
      (decodedRetryPoolSuccessorStageInstrument
        h hdegree z q ⟨stage, by omega⟩ hstage)
      (fun successorOutcome =>
        decodedRetryPoolSuccessorStageRoutingGood
          m w z q ⟨stage, by omega⟩ hstage successorOutcome ≠ true)
      (decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
        h hdegree z q hz stage (by omega)
          (decodedRetryPoolNestedPathEquiv m w stage path) rho)))
end HH18Parameterized
end Distillation
end QEC


