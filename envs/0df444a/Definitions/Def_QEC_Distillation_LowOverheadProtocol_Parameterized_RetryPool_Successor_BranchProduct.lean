-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_BranchProduct
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_BranchProduct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T19:39:38.708752+00:00
-- url     : https://prove2.me/theorems/7de0f7e5-8527-47ab-865f-c886e5f44869
-- title:
--   Branch Product
-- statement:
--   Definitions and structural lemmas for Branch Product, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/BranchProduct.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Regrouping
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_RecordRouting
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProductFunctorial
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
attribute [local instance 100] Fintype.ofFinite
local instance instSuccessorBranchClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
attribute [local instance] QEC.Distillation.HH18Parameterized.instSuccessorBranchClassicalDecidable
noncomputable def decodedRetryPoolSuccessorCoordinateTensorChannel
    (m w z q : Nat) (stage : Fin z) (port : LogicalSite m w) :
    QuantumChannel
      (QubitRegister (decodedRetryPoolSuccessorSourceSlots m w z q stage))
      (tensorPowerCarrier QubitSpace
        (decodedRetryPoolBackwardSchedule m w z q stage)) :=
  QuantumChannel.comp
    (quantumChannelTensorPower
      (decodedRetryPoolQubitRegisterCoordinateChannel (LogicalSite m w) port)
      (decodedRetryPoolBackwardSchedule m w z q stage))
    (QuantumChannel.unitaryConj
      (tensorPowerQubitRegisterTransport (LogicalSite m w)
        (decodedRetryPoolBackwardSchedule m w z q stage)).symm)
noncomputable def decodedRetryPoolSuccessorCoordinateBranchRouteTransport
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    UnitaryTransport
      (tensorPowerCarrier QubitSpace
        (decodedRetryPoolBackwardSchedule m w z q stage))
      (tensorPowerCarrier (PhysicalRegister m w)
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩)) := by
  let flatten := decodedRetryPoolQubitTensorPowerFinRegisterTransport
    (decodedRetryPoolBackwardSchedule m w z q stage)
  let route := decodedRetryPoolSuccessorPortRecordTransport
    m w z q stage hstage
  let restore := (tensorPowerQubitRegisterTransport (PhysicalSite m w)
    (decodedRetryPoolBackwardAttempts m w z q
      ⟨stage.1 + 1, hstage⟩)).symm
  exact
    { toLinearEquiv :=
        (flatten.toLinearEquiv.trans route.toLinearEquiv).trans
          restore.toLinearEquiv
      map_inner := by
        intro x y
        exact (restore.map_inner (route (flatten x)) (route (flatten y))).trans
          ((route.map_inner (flatten x) (flatten y)).trans
            (flatten.map_inner x y)) }
noncomputable def decodedRetryPoolSuccessorCoordinateBranchRouteChannel
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    QuantumChannel
      (tensorPowerCarrier QubitSpace
        (decodedRetryPoolBackwardSchedule m w z q stage))
      (tensorPowerCarrier (PhysicalRegister m w)
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩)) :=
  QuantumChannel.unitaryConj
    (decodedRetryPoolSuccessorCoordinateBranchRouteTransport
      m w z q stage hstage)
noncomputable def decodedRetryPoolSuccessorCoordinateBranchChannel
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w) :
    QuantumChannel
      (QubitRegister (decodedRetryPoolSuccessorSourceSlots m w z q stage))
      (tensorPowerCarrier (PhysicalRegister m w)
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩)) :=
  QuantumChannel.comp
    (decodedRetryPoolSuccessorCoordinateBranchRouteChannel
      m w z q stage hstage)
    (decodedRetryPoolSuccessorCoordinateTensorChannel
      m w z q stage port)
noncomputable def decodedRetryPoolSuccessorCoordinateBranchHistory
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (bits : Bitstring (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    tensorPowerHistory (Bitstring (PhysicalSite m w))
      (decodedRetryPoolBackwardAttempts m w z q
        ⟨stage.1 + 1, hstage⟩) :=
  (tensorPowerQubitBitstringEquiv (PhysicalSite m w)
    (decodedRetryPoolBackwardAttempts m w z q
      ⟨stage.1 + 1, hstage⟩)).symm
    (fun target => bits
      ((decodedRetryPoolSuccessorAttemptSlotsEquiv
        m w z q stage hstage).symm target, port))
noncomputable def decodedRetryPoolSuccessorCoordinateBranchCoefficient
    (m w z q : Nat) (stage : Fin z) (port : LogicalSite m w)
    (left right : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) : Complex :=
  ∏ trial : Fin (decodedRetryPoolBackwardSchedule m w z q stage),
    ∏ coordinate : Fin (Fintype.card (LogicalSite m w)),
      if coordinate = Fintype.equivFin (LogicalSite m w) port then 1
      else inner Complex
        (EuclideanSpace.basisFun (Fin 2) Complex
          (right (trial,
            (Fintype.equivFin (LogicalSite m w)).symm coordinate)))
        (EuclideanSpace.basisFun (Fin 2) Complex
          (left (trial,
            (Fintype.equivFin (LogicalSite m w)).symm coordinate)))
noncomputable def decodedRetryPoolSuccessorSourceMatrixUnit
    (m w z q : Nat) (stage : Fin z)
    (left right : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    Operator (QubitRegister
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :=
  (InnerProductSpace.rankOne Complex
    (EuclideanSpace.basisFun
      (Bitstring (decodedRetryPoolSuccessorSourceSlots m w z q stage))
      Complex left)
    (EuclideanSpace.basisFun
      (Bitstring (decodedRetryPoolSuccessorSourceSlots m w z q stage))
      Complex right)).toLinearMap
noncomputable def decodedRetryPoolSuccessorCoordinateTensorBasisVector
    (m w z q : Nat) (stage : Fin z) (port : LogicalSite m w)
    (bits : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    tensorPowerCarrier QubitSpace
      (decodedRetryPoolBackwardSchedule m w z q stage) :=
  tensorPowerBasis (EuclideanSpace.basisFun (Fin 2) Complex)
    (decodedRetryPoolBackwardSchedule m w z q stage)
    (tensorPowerHistoryMap (fun localBits => localBits port)
      (decodedRetryPoolBackwardSchedule m w z q stage)
      ((tensorPowerQubitBitstringEquiv (LogicalSite m w)
        (decodedRetryPoolBackwardSchedule m w z q stage)).symm bits))
noncomputable def decodedRetryPoolSuccessorCoordinateTensorMatrixUnit
    (m w z q : Nat) (stage : Fin z) (port : LogicalSite m w)
    (left right : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    Operator (tensorPowerCarrier QubitSpace
      (decodedRetryPoolBackwardSchedule m w z q stage)) :=
  (InnerProductSpace.rankOne Complex
    (decodedRetryPoolSuccessorCoordinateTensorBasisVector
      m w z q stage port left)
    (decodedRetryPoolSuccessorCoordinateTensorBasisVector
      m w z q stage port right)).toLinearMap
noncomputable def decodedRetryPoolSuccessorCoordinateBranchBasisVector
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (bits : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    tensorPowerCarrier (PhysicalRegister m w)
      (decodedRetryPoolBackwardAttempts m w z q
        ⟨stage.1 + 1, hstage⟩) :=
  tensorPowerBasis
    (EuclideanSpace.basisFun (Bitstring (PhysicalSite m w)) Complex)
    (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
    (decodedRetryPoolSuccessorCoordinateBranchHistory
      m w z q stage hstage port bits)
noncomputable def decodedRetryPoolSuccessorCoordinateBranchMatrixUnit
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (left right : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    Operator (tensorPowerCarrier (PhysicalRegister m w)
      (decodedRetryPoolBackwardAttempts m w z q
        ⟨stage.1 + 1, hstage⟩)) :=
  (InnerProductSpace.rankOne Complex
    (decodedRetryPoolSuccessorCoordinateBranchBasisVector
      m w z q stage hstage port left)
    (decodedRetryPoolSuccessorCoordinateBranchBasisVector
      m w z q stage hstage port right)).toLinearMap
def decodedRetryPoolSuccessorSiblingAgreement
    (m w z q : Nat) (stage : Fin z) (port : LogicalSite m w)
    (left right : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) : Prop :=
  ∀ trial : Fin (decodedRetryPoolBackwardSchedule m w z q stage),
    ∀ site : LogicalSite m w, site ≠ port →
      right (trial, site) = left (trial, site)
noncomputable def decodedRetryPoolSuccessorRoutedBranchCoefficient
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (branch : Fin (logicalOutputCount m w))
    (left right : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) : Complex :=
  ∏ coordinate : Fin (logicalOutputCount m w),
    if coordinate = branch then 1
    else inner Complex
      (tensorPowerBasis
        (EuclideanSpace.basisFun (Bitstring (PhysicalSite m w)) Complex)
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩)
        ((tensorPowerQubitBitstringEquiv (PhysicalSite m w)
          (decodedRetryPoolBackwardAttempts m w z q
            ⟨stage.1 + 1, hstage⟩)).symm
          (fun target => right
            ((decodedRetryPoolSuccessorAttemptSlotsEquiv
              m w z q stage hstage).symm target,
              (decodedRetryPoolLogicalSiteFinEquiv m w).symm coordinate))))
      (tensorPowerBasis
        (EuclideanSpace.basisFun (Bitstring (PhysicalSite m w)) Complex)
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩)
        ((tensorPowerQubitBitstringEquiv (PhysicalSite m w)
          (decodedRetryPoolBackwardAttempts m w z q
            ⟨stage.1 + 1, hstage⟩)).symm
          (fun target => left
            ((decodedRetryPoolSuccessorAttemptSlotsEquiv
              m w z q stage hstage).symm target,
              (decodedRetryPoolLogicalSiteFinEquiv m w).symm coordinate))))
end HH18Parameterized
end Distillation
end QEC


