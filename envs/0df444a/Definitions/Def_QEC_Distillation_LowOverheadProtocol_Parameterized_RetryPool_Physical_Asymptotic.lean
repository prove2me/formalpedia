-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Asymptotic
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Asymptotic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T22:55:24.449866+00:00
-- url     : https://prove2.me/theorems/b754dc48-56cd-4222-b062-79e677efa3cd
-- title:
--   Asymptotic
-- statement:
--   Definitions and structural lemmas for Asymptotic, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Asymptotic.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Cost
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolExactBatchTerminalRequest_pos
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalExactBatchOutputSlots_card
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolCoordinateRawError_nonneg
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolRun_coordinateError_le_four_thirds_envelope
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthLogicalOutputCount_pos
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPhysicalInputCount_pos
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleErrorEnvelope_nonneg
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleTargetError_eq_scale_mul_errorEnvelope
import Theorems.Thm_QEC_Distillation_HH18Parameterized_two_mul_routedDepthPhysicalInputCount_le_iterationScale
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalMagicState_inner_self

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
theorem decodedRetryPoolPhysicalExactBatchOutputSlots_nonempty
    (m w depth : Nat) :
    Nonempty (decodedRetryPoolPhysicalExactBatchOutputSlots m w depth) := by
  apply Fintype.card_pos_iff.mp
  rw [decodedRetryPoolPhysicalExactBatchOutputSlots_card]
  exact mul_pos
    (decodedRetryPoolExactBatchTerminalRequest_pos (depth + 1))
    (pow_pos (routedDepthLogicalOutputCount_pos m w) _)
noncomputable def decodedRetryPoolPhysicalExactBatchActualOutputError
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) : Real := by
  classical
  exact Finset.univ.sup'
    ⟨(decodedRetryPoolPhysicalExactBatchOutputSlots_nonempty
      m w depth).some, Finset.mem_univ _⟩
    fun coordinate =>
      decodedRetryPoolPhysicalProtocolCoordinateRawError m w (depth + 1)
        (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
        (Nat.succ_pos depth) coordinate
        (decodedRetryPoolPhysicalExactBatchRun
          h hdegree epsilon depth rhoUnit).acceptedOutput
theorem four_thirds_mul_routedDepthErrorEnvelope_le_scheduleTargetError
    {w r m : Nat} (h : Admissible w r m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat) :
    (4 / 3 : Real) * routedDepthErrorEnvelope w r m epsilon depth <=
      routedDepthScheduleTargetError w r m epsilon depth := by
  rw [routedDepthScheduleTargetError_eq_scale_mul_errorEnvelope h epsilon depth]
  have hn : 0 < physicalInputCount m w := routedDepthPhysicalInputCount_pos h
  have hscale : (4 / 3 : Real) <= routedDepthIterationScale w r m := by
    have htwo := two_mul_routedDepthPhysicalInputCount_le_iterationScale w r m
    have hcount : (1 : Real) <= physicalInputCount m w := by exact_mod_cast hn
    nlinarith
  exact mul_le_mul_of_nonneg_right hscale
    (routedDepthScheduleErrorEnvelope_nonneg w r m epsilon depth)
theorem decodedRetryPoolPhysicalExactBatchActualOutputError_le_targetError
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolPhysicalExactBatchActualOutputError
        h hdegree epsilon depth rhoUnit <=
      routedDepthScheduleTargetError w r m epsilon (depth + 1) := by
  classical
  unfold decodedRetryPoolPhysicalExactBatchActualOutputError
  apply Finset.sup'_le
  intro coordinate _
  exact (decodedRetryPoolPhysicalProtocolRun_coordinateError_le_four_thirds_envelope
    h hdegree epsilon hpool (depth + 1)
      (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
      (Nat.succ_pos depth) rhoUnit coordinate).trans
    (four_thirds_mul_routedDepthErrorEnvelope_le_scheduleTargetError
      h epsilon (depth + 1))
noncomputable def decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient
    {w r m : Nat} (_h : Admissible w r m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : Real :=
  (16 / 9 : Real) /
    Real.rpow (routedDepthScheduleLogGrowthBase w r m epsilon)
      (routedDepthScheduleGamma w r m)
abbrev decodedRetryPoolPhysicalExactBatchInputCarrier
    (m w depth : Nat) :=
  decodedRetryPoolProtocolRootInputCarrier m w (depth + 1)
    (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
    (Nat.succ_pos depth)
abbrev decodedRetryPoolPhysicalExactBatchOutputCarrier
    (m w depth : Nat) :=
  decodedRetryPoolPhysicalProtocolOutputCarrier m w (depth + 1)
    (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
    (Nat.succ_pos depth)
abbrev decodedRetryPoolPhysicalExactBatchBaseOutputSlots
    (m w depth : Nat) :=
  Fin (decodedRetryPoolBackwardSchedule m w (depth + 1)
    (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
    (decodedRetryPoolProtocolTerminalStage (depth + 1)
      (Nat.succ_pos depth))) × LogicalSite m w
noncomputable def decodedRetryPoolNestedProductDensity
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (rho : DensityOperator H) (branches : Nat) :
    (depth : Nat) → DensityOperator (nestedTensorCarrier H branches depth)
  | 0 => rho
  | depth + 1 =>
      decodedRetryPoolNestedProductDensity
        (tensorPowerProductInput rho decodedRetryPoolTensorUnitDensity branches)
        branches depth
noncomputable def decodedRetryPoolPhysicalExactBatchBaseIdealOutput
    (m w depth : Nat) :
    DensityOperator
      (QubitRegister
        (decodedRetryPoolPhysicalExactBatchBaseOutputSlots m w depth)) :=
  DensityOperator.pureDensity
    (Triorthogonal.BinaryRowFamily.logicalMagicState
      (decodedRetryPoolPhysicalExactBatchBaseOutputSlots m w depth)) (by
        have hinner :=
          Triorthogonal.BinaryRowFamily.logicalMagicState_inner_self
            (decodedRetryPoolPhysicalExactBatchBaseOutputSlots m w depth)
        rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex), hinner]
        norm_num)
noncomputable def decodedRetryPoolPhysicalExactBatchIdealOutput
    (m w depth : Nat) :
    DensityOperator (decodedRetryPoolPhysicalExactBatchOutputCarrier m w depth) :=
  decodedRetryPoolNestedProductDensity
    (decodedRetryPoolPhysicalExactBatchBaseIdealOutput m w depth)
    (logicalOutputCount m w) depth
noncomputable def decodedRetryPoolPhysicalExactBatchOutputError
    (m w depth : Nat)
    (rho _sigma : DensityOperator
      (decodedRetryPoolPhysicalExactBatchOutputCarrier m w depth)) : Real := by
  classical
  exact Finset.univ.sup'
    ⟨(decodedRetryPoolPhysicalExactBatchOutputSlots_nonempty
      m w depth).some, Finset.mem_univ _⟩
    fun coordinate =>
      decodedRetryPoolPhysicalProtocolCoordinateRawError m w (depth + 1)
        (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
        (Nat.succ_pos depth) coordinate rho
theorem decodedRetryPoolPhysicalExactBatchOutputError_nonneg
    (m w depth : Nat)
    (rho sigma : DensityOperator
      (decodedRetryPoolPhysicalExactBatchOutputCarrier m w depth)) :
    0 ≤ decodedRetryPoolPhysicalExactBatchOutputError m w depth rho sigma := by
  classical
  unfold decodedRetryPoolPhysicalExactBatchOutputError
  obtain ⟨coordinate, _, hcoordinate⟩ := Finset.exists_mem_eq_sup'
    ⟨(decodedRetryPoolPhysicalExactBatchOutputSlots_nonempty
      m w depth).some, Finset.mem_univ _⟩
    (fun coordinate : decodedRetryPoolPhysicalExactBatchOutputSlots m w depth =>
      decodedRetryPoolPhysicalProtocolCoordinateRawError m w (depth + 1)
        (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
        (Nat.succ_pos depth) coordinate rho)
  rw [hcoordinate]
  exact decodedRetryPoolPhysicalProtocolCoordinateRawError_nonneg
    m w (depth + 1)
      (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
      (Nat.succ_pos depth) coordinate rho
def decodedRetryPoolPhysicalExactBatchIndependentInputModel
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    IndependentInputErrorModel
      (decodedRetryPoolPhysicalExactBatchRun
        h hdegree epsilon depth rhoUnit).resourceCount QubitSpace where
  rate := fun _ => epsilon.1
  rate_nonneg := fun _ => epsilon.property.1
  rate_le_one := fun _ => by linarith [epsilon.property.2]
  admissible := fun rates inputs =>
    (∀ slot, rates slot = epsilon.1) ∧
      inputs = (decodedRetryPoolPhysicalExactBatchRun
        h hdegree epsilon depth rhoUnit).noisyInput
noncomputable def decodedRetryPoolPhysicalExactBatchMagicStateProtocol
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    MagicStateDistillationProtocol QubitSpace
      (decodedRetryPoolPhysicalExactBatchInputCarrier m w depth)
      (decodedRetryPoolPhysicalExactBatchOutputCarrier m w depth) where
  run := decodedRetryPoolPhysicalExactBatchRun
    h hdegree epsilon depth rhoUnit
  inputErrorModel := .independent
    (decodedRetryPoolPhysicalExactBatchIndependentInputModel
      h hdegree epsilon depth rhoUnit)
  inputPermitted := by
    exact ⟨fun _ => rfl, rfl⟩
  behavior := .postselected
  idealOutput := decodedRetryPoolPhysicalExactBatchIdealOutput m w depth
  outputError := decodedRetryPoolPhysicalExactBatchOutputError m w depth
  outputError_nonneg := decodedRetryPoolPhysicalExactBatchOutputError_nonneg
    m w depth
theorem decodedRetryPoolPhysicalExactBatchMagicStateProtocol_successfulOutputError
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (decodedRetryPoolPhysicalExactBatchMagicStateProtocol
      h hdegree epsilon depth rhoUnit).successfulOutputError =
      decodedRetryPoolPhysicalExactBatchActualOutputError
        h hdegree epsilon depth rhoUnit := by
  rfl
noncomputable def decodedRetryPoolPhysicalExactBatchProtocolFamily
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    DistillationProtocolFamily QubitSpace
      (decodedRetryPoolPhysicalExactBatchInputCarrier m w depth)
      (decodedRetryPoolPhysicalExactBatchOutputCarrier m w depth) PUnit where
  targetError := fun _ =>
    routedDepthScheduleTargetError w r m epsilon (depth + 1)
  protocol := fun _ =>
    decodedRetryPoolPhysicalExactBatchMagicStateProtocol
      h hdegree epsilon depth rhoUnit
  outputResourceCount := fun _ =>
    Fintype.card (decodedRetryPoolPhysicalExactBatchOutputSlots m w depth)
  outputResourceCount_pos := by
    intro _
    exact Fintype.card_pos_iff.mpr
      (decodedRetryPoolPhysicalExactBatchOutputSlots_nonempty m w depth)
  successfulOutputError_le_targetError := by
    intro _
    rw [decodedRetryPoolPhysicalExactBatchMagicStateProtocol_successfulOutputError]
    exact decodedRetryPoolPhysicalExactBatchActualOutputError_le_targetError
      h hdegree epsilon hpool depth rhoUnit
end HH18Parameterized
end Distillation
end QEC


