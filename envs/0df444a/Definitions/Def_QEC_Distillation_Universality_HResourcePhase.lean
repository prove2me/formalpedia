-- Prove2me | Definitions.Def_QEC_Distillation_Universality_HResourcePhase
-- name    : QEC_Distillation_Universality_HResourcePhase
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T12:05:43.16196+00:00
-- url     : https://prove2.me/theorems/1953cf6e-732e-4c29-b5aa-db2cbf3d5f3f
-- title:
--   HResource Phase
-- statement:
--   Definitions and structural lemmas for HResource Phase, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/HResourcePhase.lean

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace OneQubitMagic
open Semantics Semantics.Qubit
def sourceHState : QubitSpace :=
  WithLp.toLp 2 fun b =>
    if b = 0 then (Real.cos (Real.pi / 8) : Complex)
    else (Real.sin (Real.pi / 8) : Complex)
@[simp] theorem sourceHState_apply_zero :
    sourceHState 0 = (Real.cos (Real.pi / 8) : Complex) := by
  simp [sourceHState]
@[simp] theorem sourceHState_apply_one :
    sourceHState 1 = (Real.sin (Real.pi / 8) : Complex) := by
  simp [sourceHState]
theorem sourceHState_inner_self :
    inner Complex sourceHState sourceHState = 1 := by
  rw [PiLp.inner_apply]
  simp only [Fin.sum_univ_two, sourceHState_apply_zero, sourceHState_apply_one,
    RCLike.inner_apply, Complex.conj_ofReal]
  norm_cast
  simpa [pow_two] using Real.cos_sq_add_sin_sq (Real.pi / 8)
@[simp] theorem sourceHState_norm : ‖sourceHState‖ = 1 := by
  have hinner := sourceHState_inner_self
  rw [inner_self_eq_norm_sq_to_K] at hinner
  have hsq : ‖sourceHState‖ ^ 2 = 1 := by
    have hsq_complex : ((‖sourceHState‖ ^ 2 : Real) : Complex) = 1 := by
      simpa using hinner
    exact_mod_cast hsq_complex
  nlinarith [norm_nonneg sourceHState]
theorem sourceHState_ne_zero : sourceHState ≠ 0 := by
  intro hzero
  have hnorm := sourceHState_norm
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm
noncomputable def sourceHDensity : DensityOperator QubitSpace :=
  DensityOperator.pureOfNonzero sourceHState sourceHState_ne_zero
noncomputable def hResourceTransport : UnitaryTransport QubitSpace QubitSpace where
  toLinearEquiv := phaseTransport.toLinearEquiv.trans hadamardTransport.toLinearEquiv
  map_inner := by
    intro x y
    exact (hadamardTransport.map_inner (phaseTransport x) (phaseTransport y)).trans
      (phaseTransport.map_inner x y)
end OneQubitMagic
end Distillation
end QEC


