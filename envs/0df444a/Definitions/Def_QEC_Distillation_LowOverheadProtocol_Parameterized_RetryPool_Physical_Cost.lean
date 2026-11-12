-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Cost
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Cost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T21:03:34.204519+00:00
-- url     : https://prove2.me/theorems/643e63b8-4b74-4044-9c31-cf47894a1b9e
-- title:
--   Cost
-- statement:
--   Definitions and structural lemmas for Cost, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Cost.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_ExactBatching
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_AcceptedError
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite
abbrev decodedRetryPoolPhysicalExactBatchInputSlots
    (m w depth : Nat) :=
  decodedRetryPoolPhysicalProtocolRootInputSlots m w (depth + 1)
    (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
    (Nat.succ_pos depth)
abbrev decodedRetryPoolPhysicalExactBatchOutputSlots
    (m w depth : Nat) :=
  decodedRetryPoolPhysicalProtocolOutputCoordinate m w (depth + 1)
    (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
    (Nat.succ_pos depth)
noncomputable abbrev decodedRetryPoolPhysicalExactBatchRun
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :=
  decodedRetryPoolPhysicalProtocolRun h hdegree epsilon (depth + 1)
    (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
    (Nat.succ_pos depth) rhoUnit
noncomputable def decodedRetryPoolPhysicalExactBatchYield
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) : NNReal :=
  ⟨(decodedRetryPoolPhysicalExactBatchRun
      h hdegree epsilon depth rhoUnit).successProbability,
    (decodedRetryPoolPhysicalExactBatchRun
      h hdegree epsilon depth rhoUnit).success_nonneg⟩
noncomputable def decodedRetryPoolPhysicalExactBatchTypedSuccessfulOutputCost
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) : Real :=
  DependentBatch.typedSuccessfulOutputCost
    (decodedRetryPoolPhysicalExactBatchInputSlots m w depth)
    (decodedRetryPoolPhysicalExactBatchOutputSlots m w depth)
    (decodedRetryPoolPhysicalExactBatchYield
      h hdegree epsilon depth rhoUnit)
end HH18Parameterized
end Distillation
end QEC


