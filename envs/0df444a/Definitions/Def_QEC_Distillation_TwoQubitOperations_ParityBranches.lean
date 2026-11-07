-- Prove2me | Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityBranches
-- name    : QEC_Distillation_TwoQubitOperations_ParityBranches
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T14:03:02.886055+00:00
-- url     : https://prove2.me/theorems/fd79c482-b80f-4773-a1ff-b7a3e7fefd77
-- title:
--   Parity Branches
-- statement:
--   Definitions and structural lemmas for Parity Branches, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/ParityBranches.lean

import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityWeights
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_apply_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_involutive
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_symm_apply
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_tensor_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenProjector_apply_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenWeight_eq_zero_iff
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOddProjector_apply_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOddWeight_eq_zero_iff
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOperator_apply
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOperator_apply_basis
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_apply_basis
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_involutive
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_symm_apply
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_tensor_basis
attribute [local simp] QEC.Distillation.TwoQubit.zzEvenProjector_apply_basis
attribute [local simp] QEC.Distillation.TwoQubit.zzOddProjector_apply_basis
attribute [local simp] QEC.Distillation.TwoQubit.zzOperator_apply
attribute [local simp] QEC.Distillation.TwoQubit.zzOperator_apply_basis
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace TwoQubit
open Semantics
def zzEvenBranchState
    (psi : TwoQubitSpace) (_h : 0 < zzEvenWeight psi) :
    TwoQubitSpace :=
  (Real.sqrt (zzEvenWeight psi) : Complex)⁻¹ •
    zzEvenProjector psi
def zzOddBranchState
    (psi : TwoQubitSpace) (_h : 0 < zzOddWeight psi) :
    TwoQubitSpace :=
  (Real.sqrt (zzOddWeight psi) : Complex)⁻¹ •
    zzOddProjector psi
@[simp] theorem zzEvenBranchState_norm
    (psi : TwoQubitSpace) (h : 0 < zzEvenWeight psi) :
    ‖zzEvenBranchState psi h‖ = 1 := by
  have hprojector : zzEvenProjector psi ≠ 0 := by
    intro hzero
    exact h.ne' ((zzEvenWeight_eq_zero_iff psi).2 hzero)
  have hnorm : ‖zzEvenProjector psi‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hprojector
  have hsqrt :
      Real.sqrt (zzEvenWeight psi) = ‖zzEvenProjector psi‖ := by
    rw [zzEvenWeight, Real.sqrt_sq (norm_nonneg _)]
  unfold zzEvenBranchState
  rw [norm_smul, norm_inv, Complex.norm_real, hsqrt]
  simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    inv_mul_cancel₀ hnorm
@[simp] theorem zzOddBranchState_norm
    (psi : TwoQubitSpace) (h : 0 < zzOddWeight psi) :
    ‖zzOddBranchState psi h‖ = 1 := by
  have hprojector : zzOddProjector psi ≠ 0 := by
    intro hzero
    exact h.ne' ((zzOddWeight_eq_zero_iff psi).2 hzero)
  have hnorm : ‖zzOddProjector psi‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hprojector
  have hsqrt :
      Real.sqrt (zzOddWeight psi) = ‖zzOddProjector psi‖ := by
    rw [zzOddWeight, Real.sqrt_sq (norm_nonneg _)]
  unfold zzOddBranchState
  rw [norm_smul, norm_inv, Complex.norm_real, hsqrt]
  simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    inv_mul_cancel₀ hnorm
noncomputable def zzEvenBranchDensity
    (psi : TwoQubitSpace) (h : 0 < zzEvenWeight psi) :
    DensityOperator TwoQubitSpace :=
  DensityOperator.pureOfNonzero (zzEvenBranchState psi h) (by
    intro hzero
    have hnorm := zzEvenBranchState_norm psi h
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm)
noncomputable def zzOddBranchDensity
    (psi : TwoQubitSpace) (h : 0 < zzOddWeight psi) :
    DensityOperator TwoQubitSpace :=
  DensityOperator.pureOfNonzero (zzOddBranchState psi h) (by
    intro hzero
    have hnorm := zzOddBranchState_norm psi h
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm)
end TwoQubit
end Distillation
end QEC


