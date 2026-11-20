-- Prove2me | Definitions.Def_QEC_Distillation_BK15_EndpointPart2_QECert
-- name    : QEC_Distillation_BK15_EndpointPart2_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T10:26:07.220612+00:00
-- url     : https://prove2.me/theorems/fad75f43-1685-4855-88f7-028db7f06473
-- title:
--   BK15 accepted endpoint exact helper part 2
-- statement:
--   Source-exact checked intermediate declarations for the BK15 accepted endpoint formula.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean#L1630-L1656

import Definitions.Def_QEC_Distillation_FifteenQubitH_Protocol
import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_adjoint_toHermitianQubitOperator_eq_self
import Theorems.Thm_QEC_Coding_PauliSymplectic_cssXCheck_toQubitOperator_commute_cssZCheck_of_wordPairing_eq_zero
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerProjector_eigen
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerProjector_fixed_iff
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerProjector_mul_of_ne
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_square
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_anticommute_of_not_commutes
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_commute_of_commutes
import Theorems.Thm_QEC_Coding_symplecticForm_x_zero_zero_z_eq_wordPairing
import Theorems.Thm_QEC_Distillation_BK15_Protocol_aWordCorrectionTransport_eigen
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_acceptedOutput
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_operation
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_rejectedOutput
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_resourceCount
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_successProbability
import Theorems.Thm_QEC_Distillation_BK15_l1CoefficientMap_eq_sum
import Theorems.Thm_QEC_Distillation_BK15_l1_dimension
import Theorems.Thm_QEC_Distillation_BK15_l1_dual_carrier_eq_l1Syndrome_ker
import Theorems.Thm_QEC_Distillation_BK15_l2_dual_carrier_eq_l2Syndrome_ker
import Theorems.Thm_QEC_Distillation_BK15_mem_l1DualWords_iff
import Theorems.Thm_QEC_Distillation_BK15_mem_l2_dual_iff_exists_l1_plus_allOnes
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hResourceTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceHDensity_toOperator
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_code
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_encoding
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encoding_apply_of_mem
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encoding_apply_of_not_mem
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
import Definitions.Def_QEC_Distillation_BK15_EndpointPart1_QECert
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


section
noncomputable section
namespace QEC
namespace Distillation
namespace BK15
namespace Recurrence
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open NoisyInput Protocol
open scoped BigOperators TensorProduct
theorem zeroZProjectedIdeal_QECertEndpoint :
    zProjector (signSyndrome (0 : ZCheckIndex → Bit))
        (bk15ErrorWordState (0 : Word)) =
      (32 : Complex)⁻¹ •
        ambientEncodingIsometry logicalNegativeAState := by
  ext bits
  rw [zProjector_zero_apply_QECertEndpoint, bk15IdealState_apply_QECertEndpoint]
  by_cases hzero : l2Syndrome (bitstringWordEquiv (Fin 15) bits) = 0
  · rw [if_pos hzero]
    have hL2 : bitstringWordEquiv (Fin 15) bits ∈ L2.dual.carrier := by
      rw [l2_dual_carrier_eq_l2Syndrome_ker]
      exact hzero
    have hrow : bitstringWordEquiv (Fin 15) bits ∈
        bk15CSSRows.rowCode.dual.dual.carrier :=
      mem_rowCode_doubleDual_of_mem_L2_dual_QECertEndpoint hL2
    obtain ⟨a, c, hac⟩ :=
      (mem_l2_dual_iff_exists_l1_plus_allOnes
        (bitstringWordEquiv (Fin 15) bits)).1 hL2
    simp only [PiLp.smul_apply, smul_eq_mul, ambientEncodingIsometry_apply]
    change _ = (32 : Complex)⁻¹ *
      (bk15CSSRows.encoding bk15CSSRows_triorthogonal
        logicalNegativeAState : BK15Register) bits
    rw [bk15CSSRows.encoding_apply_of_mem
      bk15CSSRows_triorthogonal logicalNegativeAState hrow]
    have hrowDecomp : l1CoefficientMap a + c • allOnes ∈
        bk15CSSRows.rowCode.dual.dual.carrier := by
      rw [← hac]
      exact hrow
    have hsubtype :
        (⟨bitstringWordEquiv (Fin 15) bits, hrow⟩ :
            bk15CSSRows.rowCode.dual.dual.carrier) =
          ⟨l1CoefficientMap a + c • allOnes, hrowDecomp⟩ :=
      Subtype.ext hac
    have hlabel :
        (bk15CSSRows.logicalBasisEquivLogicalQuotient
            bk15CSSRows_triorthogonal).symm
            (Submodule.Quotient.mk
              (⟨bitstringWordEquiv (Fin 15) bits, hrow⟩ :
                bk15CSSRows.rowCode.dual.dual.carrier)) =
          (bitstringWordEquiv Unit).symm (fun _ => c) := by
      calc
        _ = (bk15CSSRows.logicalBasisEquivLogicalQuotient
              bk15CSSRows_triorthogonal).symm
              (Submodule.Quotient.mk
                (⟨l1CoefficientMap a + c • allOnes, hrowDecomp⟩ :
                  bk15CSSRows.rowCode.dual.dual.carrier)) :=
            congrArg
              (fun value : bk15CSSRows.rowCode.dual.dual.carrier =>
                (bk15CSSRows.logicalBasisEquivLogicalQuotient
                  bk15CSSRows_triorthogonal).symm
                  (Submodule.Quotient.mk value)) hsubtype
        _ = _ := logicalLabel_l1_plus_allOnes_QECertEndpoint a c hrowDecomp
    have hweight :
        Coding.HammingWeight (bitstringWordEquiv (Fin 15) bits) =
          Coding.HammingWeight (l1CoefficientMap a + c • allOnes) :=
      congrArg Coding.HammingWeight hac
    rw [hweight, hlabel, logicalNegativeAState_apply,
      l1_plus_allOnes_phase_QECertEndpoint, bk15_cssNormalizationScalar_QECertEndpoint,
      inv_sqrt_two_pow_fifteen_QECertEndpoint, logical_const_bit_val_QECertEndpoint]
    ring
  · rw [if_neg hzero]
    have hrow : bitstringWordEquiv (Fin 15) bits ∉
        bk15CSSRows.rowCode.dual.dual.carrier := by
      intro hmem
      exact hzero (l2Syndrome_eq_zero_of_mem_rowCode_doubleDual_QECertEndpoint hmem)
    simp only [PiLp.smul_apply, smul_eq_mul, ambientEncodingIsometry_apply]
    change 0 = (32 : Complex)⁻¹ *
      (bk15CSSRows.encoding bk15CSSRows_triorthogonal
        logicalNegativeAState : BK15Register) bits
    rw [bk15CSSRows.encoding_apply_of_not_mem
      bk15CSSRows_triorthogonal logicalNegativeAState hrow]
    simp

end Recurrence
end BK15
end Distillation
end QEC
end
end


