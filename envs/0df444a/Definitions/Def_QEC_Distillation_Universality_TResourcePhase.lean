-- Prove2me | Definitions.Def_QEC_Distillation_Universality_TResourcePhase
-- name    : QEC_Distillation_Universality_TResourcePhase
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T12:22:42.275859+00:00
-- url     : https://prove2.me/theorems/72db2d47-5203-400b-8a0b-44cef5462801
-- title:
--   TResource Phase
-- statement:
--   Definitions and structural lemmas for TResource Phase, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/TResourcePhase.lean

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Core
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_apply_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_involutive
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_symm_apply
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_tensor_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenBranchDensity_toOperator
import Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenProjector_apply_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenProjector_branchState
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOddBranchDensity_toOperator
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOddProjector_apply_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOddProjector_branchState
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOperator_apply
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOperator_apply_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_zzWeights_sum_of_normSq_one
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
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
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_apply_basis
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_involutive
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_symm_apply
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_tensor_basis
attribute [local simp] QEC.Distillation.TwoQubit.zzEvenBranchDensity_toOperator
attribute [local simp] QEC.Distillation.TwoQubit.zzEvenProjector_apply_basis
attribute [local simp] QEC.Distillation.TwoQubit.zzEvenProjector_branchState
attribute [local simp] QEC.Distillation.TwoQubit.zzOddBranchDensity_toOperator
attribute [local simp] QEC.Distillation.TwoQubit.zzOddProjector_apply_basis
attribute [local simp] QEC.Distillation.TwoQubit.zzOddProjector_branchState
attribute [local simp] QEC.Distillation.TwoQubit.zzOperator_apply
attribute [local simp] QEC.Distillation.TwoQubit.zzOperator_apply_basis
attribute [local simp] QEC.Semantics.DensityOperator.convexCombination_toOperator
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
open TwoQubit
open scoped InnerProductSpace TensorProduct
def sourceTParameter : Real := (Real.sqrt 3)⁻¹
def sourceTCos : Real := Real.sqrt ((1 + sourceTParameter) / 2)
def sourceTSin : Real := sourceTParameter / (Real.sqrt 2 * sourceTCos)
theorem sqrt_three_pos : 0 < Real.sqrt 3 :=
  Real.sqrt_pos.2 (by norm_num)
theorem sqrt_three_ne_zero : Real.sqrt 3 ≠ 0 :=
  sqrt_three_pos.ne'
theorem sourceTParameter_nonneg : 0 ≤ sourceTParameter := by
  unfold sourceTParameter
  exact inv_nonneg.mpr (le_of_lt sqrt_three_pos)
theorem sourceTParameter_sq : sourceTParameter ^ 2 = 1 / 3 := by
  unfold sourceTParameter
  have hsquare : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  field_simp [sqrt_three_ne_zero]
  nlinarith
theorem sourceTCos_sq : sourceTCos ^ 2 = (1 + sourceTParameter) / 2 := by
  unfold sourceTCos
  rw [Real.sq_sqrt]
  nlinarith [sourceTParameter_nonneg]
theorem sourceTCos_pos : 0 < sourceTCos := by
  unfold sourceTCos
  apply Real.sqrt_pos.2
  nlinarith [sourceTParameter_nonneg]
theorem sourceTCos_ne_zero : sourceTCos ≠ 0 :=
  sourceTCos_pos.ne'
theorem sourceTSin_sq : sourceTSin ^ 2 = (1 - sourceTParameter) / 2 := by
  have hcos := sourceTCos_sq
  have hparameter := sourceTParameter_sq
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := by
    nlinarith [sqrt_two_mul_self]
  unfold sourceTSin
  field_simp [sourceTCos_ne_zero, sqrt_two_pos.ne']
  rw [hsqrt, hcos]
  nlinarith
theorem sourceTCos_sq_add_sourceTSin_sq :
    sourceTCos ^ 2 + sourceTSin ^ 2 = 1 := by
  rw [sourceTCos_sq, sourceTSin_sq]
  ring
def sourceTState : QubitSpace :=
  WithLp.toLp 2 fun b =>
    if b = 0 then (sourceTCos : Complex)
    else phaseAmplitude (Real.pi / 4) * (sourceTSin : Complex)
@[simp] theorem sourceTState_apply_zero :
    sourceTState 0 = (sourceTCos : Complex) := by
  simp [sourceTState]
@[simp] theorem sourceTState_apply_one :
    sourceTState 1 =
      phaseAmplitude (Real.pi / 4) * (sourceTSin : Complex) := by
  simp [sourceTState]
theorem sourceTState_inner_self :
    inner Complex sourceTState sourceTState = 1 := by
  rw [PiLp.inner_apply]
  simp only [Fin.sum_univ_two, sourceTState_apply_zero, sourceTState_apply_one,
    RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  have hsum := sourceTCos_sq_add_sourceTSin_sq
  calc
    (sourceTCos : Complex) * sourceTCos +
        phaseAmplitude (Real.pi / 4) * sourceTSin *
          (star (phaseAmplitude (Real.pi / 4)) * sourceTSin) =
        ((sourceTCos ^ 2 + sourceTSin ^ 2 : Real) : Complex) := by
      calc
        (sourceTCos : Complex) * sourceTCos +
            phaseAmplitude (Real.pi / 4) * sourceTSin *
              (star (phaseAmplitude (Real.pi / 4)) * sourceTSin) =
            (sourceTCos : Complex) * sourceTCos +
              (phaseAmplitude (Real.pi / 4) *
                star (phaseAmplitude (Real.pi / 4))) *
                  (sourceTSin : Complex) * sourceTSin := by ring
        _ = ((sourceTCos ^ 2 + sourceTSin ^ 2 : Real) : Complex) := by
          rw [phaseAmplitude_mul_conj]
          push_cast
          ring
    _ = 1 := by norm_cast
@[simp] theorem sourceTState_norm : ‖sourceTState‖ = 1 := by
  have hinner := sourceTState_inner_self
  rw [inner_self_eq_norm_sq_to_K] at hinner
  have hsq : ‖sourceTState‖ ^ 2 = 1 := by
    have hsq_complex : ((‖sourceTState‖ ^ 2 : Real) : Complex) = 1 := by
      simpa using hinner
    exact_mod_cast hsq_complex
  nlinarith [norm_nonneg sourceTState]
theorem sourceTState_ne_zero : sourceTState ≠ 0 := by
  intro hzero
  have hnorm := sourceTState_norm
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm
noncomputable def sourceTDensity : DensityOperator QubitSpace :=
  DensityOperator.pureOfNonzero sourceTState sourceTState_ne_zero
@[simp] theorem sourceTDensity_toOperator :
    sourceTDensity.toOperator =
      (InnerProductSpace.rankOne Complex sourceTState sourceTState).toLinearMap := by
  rw [sourceTDensity, DensityOperator.pureOfNonzero_toOperator]
  rw [sourceTState_inner_self]
  simp
noncomputable def sourceTTwoQubitState : TwoQubitSpace :=
  tensorRegisterTransport (sourceTState ⊗ₜ[Complex] sourceTState)
noncomputable def sourceTEvenWeight : Real := zzEvenWeight sourceTTwoQubitState
theorem tensorRegisterTransport_apply_tmul_coordinate
    (x y : QubitSpace) (bits : Bitstring (Fin 2)) :
    tensorRegisterTransport (x ⊗ₜ[Complex] y) bits =
      x (bits 0) * y (bits 1) := by
  have hinner := tensorRegisterTransport.map_inner
    (EuclideanSpace.basisFun (Fin 2) Complex (bits 0) ⊗ₜ[Complex]
      EuclideanSpace.basisFun (Fin 2) Complex (bits 1))
    (x ⊗ₜ[Complex] y)
  change inner Complex
      (tensorRegisterTransport
        (EuclideanSpace.basisFun (Fin 2) Complex (bits 0) ⊗ₜ[Complex]
          EuclideanSpace.basisFun (Fin 2) Complex (bits 1)))
      (tensorRegisterTransport (x ⊗ₜ[Complex] y)) =
    inner Complex
      (EuclideanSpace.basisFun (Fin 2) Complex (bits 0) ⊗ₜ[Complex]
        EuclideanSpace.basisFun (Fin 2) Complex (bits 1))
      (x ⊗ₜ[Complex] y) at hinner
  rw [tensorRegisterTransport_apply_basis] at hinner
  have hp : pairBitstring (bits 0, bits 1) = bits := by
    simpa only [splitBitstring] using pair_splitBitstring bits
  rw [hp, EuclideanSpace.basisFun_inner, TensorProduct.inner_tmul,
    EuclideanSpace.basisFun_inner, EuclideanSpace.basisFun_inner] at hinner
  exact hinner
theorem zzEvenProjector_sourceTTwoQubitState_apply
    (a b : Fin 2) :
    zzEvenProjector sourceTTwoQubitState (pairBitstring (a, b)) =
      if a = b then sourceTState a * sourceTState b else 0 := by
  unfold zzEvenProjector
  simp only [LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply]
  simp only [WithLp.ofLp_smul, WithLp.ofLp_add]
  change (2 : Complex)⁻¹ *
      (sourceTTwoQubitState.ofLp (pairBitstring (a, b)) +
        (zzOperator sourceTTwoQubitState).ofLp (pairBitstring (a, b))) = _
  have hzz : (zzOperator sourceTTwoQubitState).ofLp (pairBitstring (a, b)) =
      zPhase a * zPhase b * sourceTTwoQubitState.ofLp (pairBitstring (a, b)) := by
    simpa only [pairBitstring_zero, pairBitstring_one] using
      zzOperator_apply sourceTTwoQubitState (pairBitstring (a, b))
  rw [hzz]
  unfold sourceTTwoQubitState
  rw [tensorRegisterTransport_apply_tmul_coordinate]
  by_cases h : a = b
  · subst b
    fin_cases a <;> simp [zPhase] <;> ring
  · fin_cases a <;> fin_cases b <;> simp_all [zPhase]
theorem sourceTEvenProjection_inner :
    inner Complex (zzEvenProjector sourceTTwoQubitState)
      (zzEvenProjector sourceTTwoQubitState) = (2 / 3 : Complex) := by
  rw [PiLp.inner_apply]
  rw [← Equiv.sum_comp bitstringPairEquiv
    (fun bits => inner Complex ((zzEvenProjector sourceTTwoQubitState).ofLp bits)
      ((zzEvenProjector sourceTTwoQubitState).ofLp bits))]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  have h00 : (zzEvenProjector sourceTTwoQubitState).ofLp
      (bitstringPairEquiv (0, 0)) = (sourceTCos : Complex) * sourceTCos := by
    simpa [bitstringPairEquiv] using zzEvenProjector_sourceTTwoQubitState_apply 0 0
  have h01 : (zzEvenProjector sourceTTwoQubitState).ofLp
      (bitstringPairEquiv (0, 1)) = 0 := by
    simpa [bitstringPairEquiv] using zzEvenProjector_sourceTTwoQubitState_apply 0 1
  have h10 : (zzEvenProjector sourceTTwoQubitState).ofLp
      (bitstringPairEquiv (1, 0)) = 0 := by
    simpa [bitstringPairEquiv] using zzEvenProjector_sourceTTwoQubitState_apply 1 0
  have h11 : (zzEvenProjector sourceTTwoQubitState).ofLp
      (bitstringPairEquiv (1, 1)) =
        (phaseAmplitude (Real.pi / 4) * sourceTSin) *
          (phaseAmplitude (Real.pi / 4) * sourceTSin) := by
    simpa [bitstringPairEquiv] using zzEvenProjector_sourceTTwoQubitState_apply 1 1
  rw [h00, h01, h10, h11]
  simp only [RCLike.inner_apply, map_zero, zero_mul, add_zero]
  have hfourth : sourceTCos ^ 4 + sourceTSin ^ 4 = 2 / 3 := by
    rw [show sourceTCos ^ 4 = (sourceTCos ^ 2) ^ 2 by ring,
      show sourceTSin ^ 4 = (sourceTSin ^ 2) ^ 2 by ring]
    rw [sourceTCos_sq, sourceTSin_sq]
    ring_nf
    rw [sourceTParameter_sq]
    norm_num
  have hphase : phaseAmplitude (Real.pi / 4) *
      star (phaseAmplitude (Real.pi / 4)) = 1 :=
    phaseAmplitude_mul_conj (Real.pi / 4)
  simp only [map_mul, Complex.conj_ofReal]
  ring_nf
  have hangle : Real.pi * (1 / 4 : Real) = Real.pi / 4 := by ring
  rw [hangle]
  change (sourceTCos : Complex) ^ 4 +
      phaseAmplitude (Real.pi / 4) ^ 2 * (sourceTSin : Complex) ^ 4 *
        star (phaseAmplitude (Real.pi / 4)) ^ 2 = _
  have hphaseSq : phaseAmplitude (Real.pi / 4) ^ 2 *
      star (phaseAmplitude (Real.pi / 4)) ^ 2 = 1 := by
    rw [← mul_pow, hphase]
    norm_num
  calc
    _ = (sourceTCos : Complex) ^ 4 +
        (phaseAmplitude (Real.pi / 4) ^ 2 *
          star (phaseAmplitude (Real.pi / 4)) ^ 2) * sourceTSin ^ 4 := by ring
    _ = ((sourceTCos ^ 4 + sourceTSin ^ 4 : Real) : Complex) := by
      rw [hphaseSq]
      norm_num
    _ = 2 / 3 := by
      calc
        _ = ((2 / 3 : Real) : Complex) := congrArg (fun x : Real => (x : Complex)) hfourth
        _ = 2 / 3 := by norm_num
theorem sourceTEvenWeight_eq_two_thirds : sourceTEvenWeight = 2 / 3 := by
  unfold sourceTEvenWeight zzEvenWeight
  have hinner := sourceTEvenProjection_inner
  rw [inner_self_eq_norm_sq_to_K] at hinner
  have hnormC : ((‖zzEvenProjector sourceTTwoQubitState‖ ^ 2 : Real) : Complex) =
      2 / 3 := by
    calc
      _ = (‖zzEvenProjector sourceTTwoQubitState‖ : Complex) ^ 2 :=
        Complex.ofReal_pow _ _
      _ = 2 / 3 := hinner
  have hnormC' : ((‖zzEvenProjector sourceTTwoQubitState‖ ^ 2 : Real) : Complex) =
      ((2 / 3 : Real) : Complex) := by
    calc
      _ = 2 / 3 := hnormC
      _ = ((2 / 3 : Real) : Complex) := by norm_num
  exact_mod_cast hnormC'
theorem sourceTEvenWeight_pos : 0 < sourceTEvenWeight := by
  rw [sourceTEvenWeight_eq_two_thirds]
  norm_num
theorem sourceTTwoQubitState_norm : ‖sourceTTwoQubitState‖ = 1 := by
  unfold sourceTTwoQubitState
  change ‖tensorRegisterTransport.toLinearIsometryEquiv
      (sourceTState ⊗ₜ[Complex] sourceTState)‖ = 1
  rw [tensorRegisterTransport.toLinearIsometryEquiv.norm_map,
    TensorProduct.norm_tmul, sourceTState_norm]
  norm_num
theorem sourceTOddWeight_eq_one_third :
    zzOddWeight sourceTTwoQubitState = 1 / 3 := by
  have hsum := zzWeights_sum_of_normSq_one sourceTTwoQubitState (by
    rw [sourceTTwoQubitState_norm]
    norm_num)
  change sourceTEvenWeight + zzOddWeight sourceTTwoQubitState = 1 at hsum
  rw [sourceTEvenWeight_eq_two_thirds] at hsum
  linarith
theorem sourceTOddWeight_pos : 0 < zzOddWeight sourceTTwoQubitState := by
  rw [sourceTOddWeight_eq_one_third]
  norm_num
noncomputable def sourceTEvenBranch : DensityOperator TwoQubitSpace :=
  zzEvenBranchDensity sourceTTwoQubitState sourceTEvenWeight_pos
noncomputable def sourceTOddBranch : DensityOperator TwoQubitSpace :=
  zzOddBranchDensity sourceTTwoQubitState sourceTOddWeight_pos
noncomputable def sourceTEvenFirstQubit : QubitSpace :=
  zzEvenBranchFirstQubit sourceTTwoQubitState sourceTEvenWeight_pos
noncomputable def sourceTGlobalPhase : Complex :=
  (Real.sqrt 2 : Complex) * (hadamardOperator sourceTEvenFirstQubit) 0
inductive SourceTOutcomeAction
  | emitAccepted
  | retryWithFreshPair
deriving DecidableEq
def sourceTOutcomeAction : DistillationOutcome → SourceTOutcomeAction
  | .accepted => .emitAccepted
  | .rejected => .retryWithFreshPair
structure SourceTAttempt where
  resourceCount : Nat
  acceptedWeight : Real
  rejectedWeight : Real
  acceptedBranch : DensityOperator TwoQubitSpace
  rejectedBranch : DensityOperator TwoQubitSpace
  weights_sum : acceptedWeight + rejectedWeight = 1
noncomputable def sourceTAttempt : SourceTAttempt where
  resourceCount := 2
  acceptedWeight := sourceTEvenWeight
  rejectedWeight := zzOddWeight sourceTTwoQubitState
  acceptedBranch := sourceTEvenBranch
  rejectedBranch := sourceTOddBranch
  weights_sum := by
    rw [sourceTEvenWeight_eq_two_thirds, sourceTOddWeight_eq_one_third]
    norm_num
end OneQubitMagic
end Distillation
end QEC


