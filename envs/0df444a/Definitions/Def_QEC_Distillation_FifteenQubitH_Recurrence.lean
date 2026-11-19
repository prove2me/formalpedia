-- Prove2me | Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
-- name    : QEC_Distillation_FifteenQubitH_Recurrence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T04:14:47.862711+00:00
-- url     : https://prove2.me/theorems/874f4184-4924-4f4e-a539-c994621778a0
-- title:
--   Recurrence
-- statement:
--   Definitions and structural lemmas for Recurrence, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean

import Definitions.Def_QEC_Distillation_FifteenQubitH_Protocol
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_acceptedOutput
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_operation
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_rejectedOutput
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_resourceCount
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_successProbability
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hResourceTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceHDensity_toOperator
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_code
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_encoding
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalComputationalState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalMagicState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalPlusState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_oddWordLinearEquivLogicalQuotient_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_acceptedOutput
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_operation
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_rejectedOutput
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_resourceCount
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_successProbability
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Distillation.OneQubitMagic.hResourceTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.sourceHDensity_toOperator
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_code
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_encoding
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalComputationalState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalMagicState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalPlusState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.oddWordLinearEquivLogicalQuotient_apply
attribute [local simp] QEC.Semantics.DensityOperator.convexCombination_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
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
namespace BK15
namespace Recurrence
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open NoisyInput Protocol
open scoped BigOperators TensorProduct
def bk15_r (epsilon : BK15Epsilon) : Real := 1 - 2 * epsilon.epsilon
set_option maxRecDepth 65536 in
noncomputable def bk15TensorComputationalBasis :
    OrthonormalBasis BK15BitTuple Complex BK15Tensor :=
  let oneBasis := EuclideanSpace.basisFun (Fin 2) Complex
  oneBasis.tensorProduct
    (oneBasis.tensorProduct
      (oneBasis.tensorProduct
        (oneBasis.tensorProduct
          (oneBasis.tensorProduct
            (oneBasis.tensorProduct
              (oneBasis.tensorProduct
                (oneBasis.tensorProduct
                  (oneBasis.tensorProduct
                    (oneBasis.tensorProduct
                      (oneBasis.tensorProduct
                        (oneBasis.tensorProduct
                          (oneBasis.tensorProduct
                            (oneBasis.tensorProduct oneBasis)))))))))))))
set_option maxRecDepth 65536 in
noncomputable def tensor15Vector
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 : QubitSpace) :
    BK15Tensor :=
  v0 ⊗ₜ[Complex]
    (v1 ⊗ₜ[Complex]
      (v2 ⊗ₜ[Complex]
        (v3 ⊗ₜ[Complex]
          (v4 ⊗ₜ[Complex]
            (v5 ⊗ₜ[Complex]
              (v6 ⊗ₜ[Complex]
                (v7 ⊗ₜ[Complex]
                  (v8 ⊗ₜ[Complex]
                    (v9 ⊗ₜ[Complex]
                      (v10 ⊗ₜ[Complex]
                        (v11 ⊗ₜ[Complex]
                          (v12 ⊗ₜ[Complex]
                            (v13 ⊗ₜ[Complex] v14)))))))))))))
set_option maxRecDepth 65536 in
@[simp] theorem bk15TensorComputationalBasis_apply
    (bits : BK15BitTuple) :
    bk15TensorComputationalBasis bits =
      tensor15Vector
        (EuclideanSpace.basisFun (Fin 2) Complex bits.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.2.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.2.2.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.2.2.2.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.2.2.2.2.2.2.2.2.2) := by
  simp only [bk15TensorComputationalBasis,
    OrthonormalBasis.tensorProduct_apply', tensor15Vector]
set_option maxRecDepth 65536 in
@[simp] theorem bk15TensorRegisterTransport_apply_computationalBasis
    (bits : BK15BitTuple) :
    bk15TensorRegisterTransport (bk15TensorComputationalBasis bits) =
      EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex
        (bk15TupleBitstring bits) := by
  dsimp [bk15TensorRegisterTransport, bk15TensorComputationalBasis]
  rw [OrthonormalBasis.equiv_apply_basis]
  rfl
noncomputable def bk15TensorErrorVector
    (error : Word) : BK15Tensor :=
  tensor15Vector
    (aInputState (wordBits error 0))
    (aInputState (wordBits error 1))
    (aInputState (wordBits error 2))
    (aInputState (wordBits error 3))
    (aInputState (wordBits error 4))
    (aInputState (wordBits error 5))
    (aInputState (wordBits error 6))
    (aInputState (wordBits error 7))
    (aInputState (wordBits error 8))
    (aInputState (wordBits error 9))
    (aInputState (wordBits error 10))
    (aInputState (wordBits error 11))
    (aInputState (wordBits error 12))
    (aInputState (wordBits error 13))
    (aInputState (wordBits error 14))
def fin15Nested (f : Fin 15 → Complex) : Complex :=
    f 0 * (f 1 * (f 2 * (f 3 * (f 4 * (f 5 * (f 6 *
      (f 7 * (f 8 * (f 9 * (f 10 * (f 11 * (f 12 *
        (f 13 * f 14)))))))))))))
def finBitToBit (bit : Fin 2) : Bit :=
  if bit = 0 then 0 else 1
@[simp] theorem binaryPhaseScalar_mul_self (bit : ZMod 2) :
    binaryPhaseScalar bit * binaryPhaseScalar bit = 1 := by
  rw [← binaryPhaseScalar_add]
  have h : bit + bit = 0 := by
    fin_cases bit <;> decide
  rw [h, binaryPhaseScalar_zero]
@[simp] theorem binaryPhaseScalar_signToBit
    (outcome : StabilizerOutcome) :
    binaryPhaseScalar (signToBit outcome) = outcome.sign := by
  cases outcome <;> norm_num [signToBit, binaryPhaseScalar,
    StabilizerOutcome.sign]
@[simp] theorem phaseState_apply_bit
    (theta : Real) (bit : Fin 2) :
    OneQubitMagic.phaseState theta bit =
      (Real.sqrt 2 : Complex)⁻¹ *
        OneQubitMagic.phaseAmplitude theta ^ bit.val := by
  fin_cases bit <;>
    simp [OneQubitMagic.phaseState_apply_zero,
      OneQubitMagic.phaseState_apply_one]
noncomputable def logicalNegativeAState : LogicalRegister :=
  WithLp.toLp 2 fun bits =>
    (Real.sqrt 2 : Complex)⁻¹ *
      OneQubitMagic.phaseAmplitude (-Real.pi / 4) ^ (bits ()).val
@[simp] theorem logicalNegativeAState_apply
    (bits : Bitstring Unit) :
    logicalNegativeAState bits =
      (Real.sqrt 2 : Complex)⁻¹ *
        OneQubitMagic.phaseAmplitude (-Real.pi / 4) ^ (bits ()).val :=
  rfl
noncomputable def logicalAErrorState (c : Bit) : LogicalRegister :=
  WithLp.toLp 2 fun bits =>
    binaryPhaseScalar (c * (bitstringWordEquiv Unit bits) ()) *
      logicalNegativeAState bits
@[simp] theorem logicalRegisterToQubit_apply
    (psi : LogicalRegister) (bit : Fin 2) :
    logicalRegisterToQubit psi bit = psi (fun _ => flipBit bit) := by
  rfl
set_option maxRecDepth 262144 in
/-- The complex raw negative-A functional after the concrete decoder. -/
noncomputable def negativeADecodedTrace :
    Operator BK15Register →ₗ[Complex] Complex where
  toFun A := LinearMap.trace Complex QubitSpace
    (aBasisProjector .negative * decoderToQubitChannel A)
  map_add' A B := by simp [mul_add]
  map_smul' scalar A := by simp [mul_smul_comm]
set_option maxRecDepth 262144 in
/-- The unnormalised negative-A numerator of the literal accepted physical
branch after the concrete total decoder. -/
noncomputable def acceptedNegativeAWeight (epsilon : BK15Epsilon) : Real :=
  (negativeADecodedTrace (rawEndpoint epsilon .accepted)).re
theorem hammingWeight_le_fifteen (word : Word) :
    Coding.HammingWeight word ≤ 15 := by
  rw [Coding.HammingWeight_eq_card_hammingSupport]
  calc
    (Coding.hammingSupport word).card ≤ (Finset.univ : Finset (Fin 15)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = 15 := by simp
def bk15WeightIndex (word : Word) : Fin 16 :=
  ⟨Coding.HammingWeight word, by
    have hweight := hammingWeight_le_fifteen word
    omega⟩
end Recurrence
end BK15
end Distillation
end QEC


