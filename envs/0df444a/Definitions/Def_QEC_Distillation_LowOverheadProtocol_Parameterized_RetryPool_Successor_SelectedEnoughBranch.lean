-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_SelectedEnoughBranch
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_SelectedEnoughBranch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T20:00:28.833285+00:00
-- url     : https://prove2.me/theorems/4619646f-e679-48cc-8a9c-3d485d3c066f
-- title:
--   Selected Enough Branch
-- statement:
--   Definitions and structural lemmas for Selected Enough Branch, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/SelectedEnoughBranch.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_EnoughBranchSum
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_BranchProduct
import Definitions.Def_QEC_Semantics_Instruments_Branches_ChannelFirstFilteredBranchOperator
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_FilteredMarginalBranchOperator
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
def decodedRetryPoolSuccessorStageSelectedPoolEnough
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (outcome : decodedRetryPoolSuccessorStageOutcome m w z q stage hstage) : Bool :=
  decodedRetryPoolOutcomeEnough
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
      (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩)
      (tensorPowerHistoryAt _ (logicalOutputCount m w) outcome.2
        (decodedRetryPoolLogicalSiteFinEquiv m w port))
noncomputable def decodedRetryPoolSuccessorStageJointInput
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    DensityOperator (decodedRetryPoolSuccessorNestedInputCarrier
      m w z q stage hstage) :=
  (decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage).mapDensity
    (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
      (decodedRetryPoolBackwardSchedule m w z q stage))
noncomputable def decodedRetryPoolSuccessorStageSelectedNextInput
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    DensityOperator (tensorPowerCarrier (PhysicalRegister m w)
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)) :=
  tensorPowerProductInput
    (prepareMeasuredResources m w
      (noisyResources m w
        (selectedLogicalPortNextInputRate h hdegree epsilon port hhalf)))
    rhoUnit
    (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
noncomputable def decodedRetryPoolSuccessorStageSelectedEnoughGlobalOperator
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    Operator (tensorPowerCarrier
      (QubitRegister (Fin (decodedRetryPoolBackwardSchedule m w z q
        ⟨stage.1 + 1, hstage⟩) × LogicalSite m w))
      (logicalOutputCount m w)) :=
  ∑ outcome : decodedRetryPoolSuccessorStageOutcome m w z q stage hstage,
    if decodedRetryPoolSuccessorStageSelectedPoolEnough
        m w z q stage hstage port outcome = true then
      (decodedRetryPoolSuccessorStageInstrument
        h hdegree z q stage hstage).branchOperator outcome
          (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
            (decodedRetryPoolBackwardSchedule m w z q stage)).toOperator
    else 0
noncomputable def decodedRetryPoolSuccessorStageSelectedEnoughRoutedOperator
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    Operator (tensorPowerCarrier
      (QubitRegister (Fin (decodedRetryPoolBackwardSchedule m w z q
        ⟨stage.1 + 1, hstage⟩) × LogicalSite m w))
      (logicalOutputCount m w)) :=
  ∑ history : tensorPowerHistory
      (Sigma fun _ : tensorPowerHistory DistillationOutcome
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩) => PUnit)
      (logicalOutputCount m w),
    if decodedRetryPoolOutcomeEnough
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩)
        (tensorPowerHistoryAt _ (logicalOutputCount m w) history
          (decodedRetryPoolLogicalSiteFinEquiv m w port)) = true then
      ((decodedRetryPoolInstrument h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q
          ⟨stage.1 + 1, hstage⟩)).tensorPower
            (logicalOutputCount m w)).branchOperator history
              (decodedRetryPoolSuccessorStageJointInput
                h hdegree epsilon z q stage hstage rhoUnit).toOperator
    else 0
noncomputable def decodedRetryPoolSuccessorStageSelectedEnoughBranchOperator
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    Operator (QubitRegister
      (Fin (decodedRetryPoolBackwardSchedule m w z q
        ⟨stage.1 + 1, hstage⟩) × LogicalSite m w)) :=
  tensorPowerCoordinateOperator (logicalOutputCount m w)
    (decodedRetryPoolLogicalSiteFinEquiv m w port)
    (decodedRetryPoolSuccessorStageSelectedEnoughGlobalOperator
      h hdegree epsilon z q stage hstage port rhoUnit)
noncomputable def decodedRetryPoolSuccessorStageLocalEnoughOperator
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (A : Operator (tensorPowerCarrier (PhysicalRegister m w)
      (decodedRetryPoolBackwardAttempts m w z q
        ⟨stage.1 + 1, hstage⟩))) :
    Operator (QubitRegister
      (Fin (decodedRetryPoolBackwardSchedule m w z q
        ⟨stage.1 + 1, hstage⟩) × LogicalSite m w)) :=
  ∑ outcome : Sigma fun _ : tensorPowerHistory DistillationOutcome
      (decodedRetryPoolBackwardAttempts m w z q
        ⟨stage.1 + 1, hstage⟩) => PUnit,
    if decodedRetryPoolOutcomeEnough
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩)
        outcome = true then
      (decodedRetryPoolInstrument h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q
          ⟨stage.1 + 1, hstage⟩)).branchOperator outcome A
    else 0
end HH18Parameterized
end Distillation
end QEC


