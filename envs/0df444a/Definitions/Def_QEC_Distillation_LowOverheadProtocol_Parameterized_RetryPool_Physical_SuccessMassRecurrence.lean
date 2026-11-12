-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessMassRecurrence
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessMassRecurrence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T20:00:53.921415+00:00
-- url     : https://prove2.me/theorems/ed73d4ad-e9d8-44c1-8aac-1fc1899c04ec
-- title:
--   Success Mass Recurrence
-- statement:
--   Definitions and structural lemmas for Success Mass Recurrence, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/SuccessMassRecurrence.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_BornMass
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_BranchProduct
import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalBornMass
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
local instance instPhysicalSuccessMassRecurrenceClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
attribute [local instance] QEC.Distillation.HH18Parameterized.instPhysicalSuccessMassRecurrenceClassicalDecidable
noncomputable def decodedRetryPoolProtocolSuccessfulRoutingMassAux
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier m w z q hz)) : Real :=
  ∑ outcome ∈ Finset.univ.filter
      (fun outcome : decodedRetryPoolProtocolOutcomeAux m w z q stage hstage =>
        decodedRetryPoolProtocolSuccessfulRoutingAux
          m w z q stage hstage outcome = true),
    (decodedRetryPoolProtocolInstrumentAux
      h hdegree z q hz stage hstage).bornWeight outcome rho
noncomputable def decodedRetryPoolProtocolStageRoutingFailureMass
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage + 1 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier m w z q hz)) : Real :=
  ∑ nextOutcome ∈ Finset.univ.filter
      (fun nextOutcome : decodedRetryPoolProtocolOutcomeAux
          m w z q (stage + 1) hstage =>
        decodedRetryPoolProtocolSuccessfulRoutingAux
            m w z q stage (by omega) nextOutcome.1 = true ∧
          nestedTensorHistoryAll
              (decodedRetryPoolSuccessorStageRoutingGood
                m w z q ⟨stage, by omega⟩ hstage)
              (logicalOutputCount m w) stage nextOutcome.2 ≠ true),
    (decodedRetryPoolProtocolInstrumentAux
      h hdegree z q hz (stage + 1) hstage).bornWeight nextOutcome rho
noncomputable def decodedRetryPoolPhysicalProtocolNoisyRootInput
    (m w z q : Nat) (hz : 0 < z)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    DensityOperator (decodedRetryPoolProtocolRootInputCarrier m w z q hz) :=
  tensorPowerProductInput
    (prepareMeasuredResources m w (noisyResources m w epsilon)) rhoUnit
    (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩)
end HH18Parameterized
end Distillation
end QEC


