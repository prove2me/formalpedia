-- Prove2me | Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_OneRound
-- name    : QEC_Distillation_ConstantOverheadProtocol_OneRound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T09:32:34.324325+00:00
-- url     : https://prove2.me/theorems/e8e66f8a-bb1c-4848-8127-61dd89128232
-- title:
--   One Round
-- statement:
--   Definitions and structural lemmas for One Round, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/OneRound.lean

import Definitions.Def_QEC_Coding_QuditQubitConversion_ResourceCircuit
import Definitions.Def_QEC_Distillation_Core_FiniteDecodedTrace
import Definitions.Def_QEC_Distillation_Core_FiniteInstrumentBinaryRun
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_MagicResource
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_AlgebraicGeometryFamily
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Definitions.Def_QEC_Semantics_Instruments_Registers_ProductDensity
import Definitions.Def_QEC_Semantics_Instruments_Registers_Marginal
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorResidueTransport_directFactorResidueEquiv_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSmithTraceResidue_directBaseResidueRationalAdicEquiv_quotientResidueEquiv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_finiteDimensional_riemannRochSubmodule
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleSmulIntoDifferentialSpace_coe
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_mul_mem_riemannRochSubmodule_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicIdealResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseFibreDirectFactor_infinityFibreEquivDirectFactors_apply_asIdeal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluationLinearMap_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agWordStar_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywisePolynomialDerivative_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_zeroCoordinateDivisor_apply_eq_zero_of_not_mem
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_xCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_zCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary1
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary2
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstTransposeCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_secondCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_secondTransposeCode_iff
import Theorems.Thm_QEC_Coding_Why24BooleanANF_evaluate_generator
import Theorems.Thm_QEC_Coding_Why24BooleanANF_generator_mul_self
import Theorems.Thm_QEC_Coding_f1024SelectedCoordinates_label_symm
import Theorems.Thm_QEC_Coding_f1024_card
import Theorems.Thm_QEC_Coding_why24AppendixGateCounts_eq_source
import Theorems.Thm_QEC_Coding_why24AppendixReverseBornWeight_eq_source
import Theorems.Thm_QEC_Coding_why24QubitPlusState_norm
import Theorems.Thm_QEC_Coding_why24QuditQubitUnitary_conj_isUnitary_iff
import Theorems.Thm_QEC_Coding_why24QuditZ_apply
import Theorems.Thm_QEC_Coding_why24UOneSevenQubitResource_norm
import Theorems.Thm_QEC_Coding_why24U_apply
import Theorems.Thm_QEC_Coding_why24U_isUnitary
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_KT19MagicResource_KT19PrimeQuditCSS_characterKet_inner
import Theorems.Thm_QEC_Distillation_KT19MagicResource_KT19PrimeQuditCSS_sum_characterKet_rankOne_eq_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_Why24AGFamily_f1024Why24OddStabilizerCode_eq_scaledShortenedAGCode
import Theorems.Thm_QEC_Distillation_assembleTagged_extractBlock
import Theorems.Thm_QEC_Distillation_extractBlock_assembleTagged
import Theorems.Thm_QEC_Distillation_mem_coordinateSupport
import Theorems.Thm_QEC_Distillation_taggedCczLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_taggedCczLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_taggedCczTransport_apply
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_binaryDistillationRun_successProbability
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bind_complete
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_fixedDensityReplacementSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_FiniteInstrument_leftMarginal_tensorDensity
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerObservedAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_partialTraceRightRaw_mapDensity_tensorDensity
import Theorems.Thm_QEC_Semantics_FiniteInstrument_rawBranchOperator_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBasis_succ_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBasis_zero_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerInputMarginal_productInput
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitBitstringEquiv_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitBitstringEquiv_symm_at
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitRegisterTransport_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitRegisterTransport_symm_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerRegisterProductDensity_matrixEntry
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedComplementBitstring_equiv_symm
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedHistoryBitstringEquiv_apply_fst
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedHistoryBitstringEquiv_apply_snd
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedOutputBitstring_equiv_symm
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedPartialTraceChannel_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedRegisterReindex_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_toQuantumChannel_apply_sum
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_registerFactorization_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorization_apply_basis
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_traceNorm_neg
import Theorems.Thm_QEC_Semantics_traceNorm_nonneg
attribute [local simp] Ideal.Factors.quotientResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicPolynomialDifferential
attribute [local simp] QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport.directFactorResidueEquiv_algebraMap
attribute [local simp] QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv_quotientResidueEquiv
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSmulIntoDifferentialSpace_coe
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicIdealResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.infinityFibreEquivDirectFactors_apply_asIdeal
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.agWordStar_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_add
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_one
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywisePolynomialDerivative_apply
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.HypergraphProduct.binaryCSSCode_xCode
attribute [local simp] QEC.Coding.HypergraphProduct.binaryCSSCode_zCode
attribute [local simp] QEC.Coding.HypergraphProduct.chainComplex_boundary1
attribute [local simp] QEC.Coding.HypergraphProduct.chainComplex_boundary2
attribute [local simp] QEC.Coding.HypergraphProduct.mem_firstCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_firstTransposeCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_secondCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_secondTransposeCode_iff
attribute [local simp] QEC.Coding.Why24BooleanANF.evaluate_generator
attribute [local simp] QEC.Coding.Why24BooleanANF.generator_mul_self
attribute [local simp] QEC.Coding.why24QuditZ_apply
attribute [local simp] QEC.Coding.why24U_apply
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Distillation.assembleTagged_extractBlock
attribute [local simp] QEC.Distillation.extractBlock_assembleTagged
attribute [local simp] QEC.Distillation.mem_coordinateSupport
attribute [local simp] QEC.Distillation.taggedCczLinearEquiv_apply
attribute [local simp] QEC.Distillation.taggedCczLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.taggedCczTransport_apply
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
attribute [local simp] QEC.Semantics.DensityOperator.convexCombination_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.binaryDistillationRun_successProbability
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.fixedDensityReplacementSwap_apply_tmul
attribute [local simp] QEC.Semantics.FiniteInstrument.leftMarginal_tensorDensity
attribute [local simp] QEC.Semantics.FiniteInstrument.mem_tensorPowerAcceptedIndices
attribute [local simp] QEC.Semantics.FiniteInstrument.mem_tensorPowerObservedAcceptedIndices
attribute [local simp] QEC.Semantics.FiniteInstrument.partialTraceRightRaw_mapDensity_tensorDensity
attribute [local simp] QEC.Semantics.FiniteInstrument.rawBranchOperator_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerBasis_succ_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerBasis_zero_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerInputMarginal_productInput
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitBitstringEquiv_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitBitstringEquiv_symm_at
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitRegisterTransport_apply_basis
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitRegisterTransport_symm_apply_basis
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedComplementBitstring_equiv_symm
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedHistoryBitstringEquiv_apply_fst
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedHistoryBitstringEquiv_apply_snd
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedOutputBitstring_equiv_symm
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedPartialTraceChannel_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedRegisterReindex_apply_basis
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.log2Matrix_apply
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.logMatrix_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
attribute [local simp] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
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
attribute [local simp] QEC.Semantics.traceNorm_neg


set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.Why24OneRoundProtocol
open QEC.Coding
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
open QEC.Distillation
open QEC.Distillation.Why24AGFamily
open QEC.Distillation.KT19PrimeQuditCSS
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
open QEC.Distillation.Why24WeightedTriorthogonalCSS
open QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix
open QEC.Semantics
open scoped BigOperators ComplexOrder
attribute [local instance]
  QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
local instance instWhy24OneRoundClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype QEC.Distillation.Why24OneRoundProtocol.instWhy24OneRoundClassicalDecidable
abbrev Why24CCZFaultLocation (r : Nat) : Type :=
  Fin (70 * f1024Why24OddLength r)
abbrev Why24CCZPhysicalQubit (Location : Type) : Type := Location × Fin 3
abbrev Why24CCZRegister (Location : Type) [Fintype Location] : Type :=
  Qubit.QubitRegister (Why24CCZPhysicalQubit Location)
def why24FaultSubsystem {Location : Type} [Fintype Location]
    [DecidableEq Location] (fault : Finset Location) :
    QuditSubsystem (fun _ : Why24CCZPhysicalQubit Location => 2) where
  selected := fault.product Finset.univ
@[simp]
theorem why24FaultSubsystem_selected {Location : Type} [Fintype Location]
    [DecidableEq Location] (fault : Finset Location) :
    (why24FaultSubsystem fault).selected = fault.product Finset.univ :=
  rfl
structure Why24CCZFaultOperation (Location : Type) [Fintype Location]
    [DecidableEq Location] (fault : Finset Location) where
  krausCount : Nat
  kraus : FiniteKrausFamily (Fin krausCount)
    (Why24CCZRegister Location) (Why24CCZRegister Location)
  complete : kraus.Complete
  supported : forall index,
    (why24FaultSubsystem fault).OperatorSupportedOnRegister
      (kraus.operator index)
namespace Why24CCZFaultOperation
variable {Location : Type} [Fintype Location] [DecidableEq Location]
variable {fault : Finset Location}
noncomputable def channel
    (operation : Why24CCZFaultOperation Location fault) :
    QuantumChannel (Why24CCZRegister Location) (Why24CCZRegister Location) :=
  operation.kraus.toQuantumChannel operation.complete
@[simp]
theorem channel_apply
    (operation : Why24CCZFaultOperation Location fault)
    (A : Operator (Why24CCZRegister Location)) :
    operation.channel A = operation.kraus.inducedMap A :=
  rfl
end Why24CCZFaultOperation
structure Why24LocalStochasticPreparation (Location : Type)
    [Fintype Location] [DecidableEq Location]
    (ideal : DensityOperator (Why24CCZRegister Location)) where
  faultMass : Finset Location -> Real
  faultMass_nonneg : forall fault, 0 <= faultMass fault
  faultMass_sum : (∑ fault : Finset Location, faultMass fault) = 1
  siteRate : Location -> Real
  siteRate_nonneg : forall location, 0 <= siteRate location
  siteRate_le_one : forall location, siteRate location <= 1
  rate : Real
  rate_nonneg : 0 <= rate
  rate_le_one : rate <= 1
  siteRate_le_rate : forall location, siteRate location <= rate
  faultOperation : (fault : Finset Location) ->
    Why24CCZFaultOperation Location fault
  tail_bound : forall sites : Finset Location,
    (∑ fault : Finset Location,
      if sites ⊆ fault then faultMass fault else 0) <=
        ∏ location ∈ sites, siteRate location
namespace Why24LocalStochasticPreparation
variable {Location : Type} [Fintype Location] [DecidableEq Location]
variable {ideal : DensityOperator (Why24CCZRegister Location)}
noncomputable def branchDensity
    (preparation : Why24LocalStochasticPreparation Location ideal)
    (fault : Finset Location) : DensityOperator (Why24CCZRegister Location) :=
  (preparation.faultOperation fault).channel.mapDensity ideal
noncomputable def why24LocalStochasticPreparedDensity
    (preparation : Why24LocalStochasticPreparation Location ideal) :
    DensityOperator (Why24CCZRegister Location) :=
  DensityOperator.convexCombination Finset.univ preparation.faultMass
    preparation.branchDensity
    (by intro fault _; exact preparation.faultMass_nonneg fault)
    (by simpa using preparation.faultMass_sum)
@[simp]
theorem why24LocalStochasticPreparedDensity_toOperator
    (preparation : Why24LocalStochasticPreparation Location ideal) :
    preparation.why24LocalStochasticPreparedDensity.toOperator =
      ∑ fault : Finset Location,
        (preparation.faultMass fault : Complex) •
          (preparation.branchDensity fault).toOperator := by
  simp [why24LocalStochasticPreparedDensity,
    DensityOperator.convexCombinationOperator]
end Why24LocalStochasticPreparation
noncomputable def why24CCZTensorUnitDensity :
    DensityOperator
      (FiniteInstrument.tensorPowerCarrier Why24CCZSpace 0) :=
  DensityOperator.pureDensity
    (FiniteInstrument.tensorPowerBasis
      (stdOrthonormalBasis Complex Why24CCZSpace) 0 PUnit.unit) (by
        erw [OrthonormalBasis.norm_eq_one]
        norm_num)
noncomputable def why24IdealCCZRegisterDensity (count : Nat) :
    DensityOperator (Why24CCZRegister (Fin count)) :=
  FiniteInstrument.tensorPowerRegisterProductDensity (Fin 3)
    why24CCZMagicStateDensity why24CCZTensorUnitDensity count
noncomputable def why24CCZSiteSubsystem (count : Nat) (site : Fin count) :
    QuditSubsystem (fun _ : Why24CCZPhysicalQubit (Fin count) => 2) :=
  why24FaultSubsystem ({site} : Finset (Fin count))
def why24CCZSiteCoordinate (count : Nat) (site : Fin count)
    (qubit : Fin 3) : (why24CCZSiteSubsystem count site).SelectedCoordinates :=
  ⟨(site, qubit), by simp [why24CCZSiteSubsystem, why24FaultSubsystem]⟩
def why24CCZSiteLabelEquiv (count : Nat) (site : Fin count) :
    Qudit.Label (why24CCZSiteSubsystem count site).selectedDimensions ≃
      Qubit.Bitstring (Fin 3) where
  toFun label qubit := label (why24CCZSiteCoordinate count site qubit)
  invFun bits coordinate := bits coordinate.1.2
  left_inv label := by
    funext coordinate
    rcases coordinate with ⟨⟨location, qubit⟩, hselected⟩
    have hlocation : location = site := by
      simpa [why24CCZSiteSubsystem, why24FaultSubsystem] using
        (Finset.mem_product.mp hselected).1
    subst location
    rfl
  right_inv bits := by
    funext qubit
    rfl
noncomputable def why24CCZSiteTransport (count : Nat)
    (site : Fin count) :
    UnitaryTransport (why24CCZSiteSubsystem count site).selectedSystem
      Why24CCZSpace := by
  let sourceBasis := EuclideanSpace.basisFun
    (Qudit.Label (why24CCZSiteSubsystem count site).selectedDimensions) Complex
  let targetBasis := EuclideanSpace.basisFun (Qubit.Bitstring (Fin 3)) Complex
  let U := sourceBasis.equiv targetBasis (why24CCZSiteLabelEquiv count site)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }
noncomputable def why24LocalStochasticSiteMarginal {count : Nat}
    (preparation : Why24LocalStochasticPreparation (Fin count)
      (why24IdealCCZRegisterDensity count))
    (site : Fin count) : DensityOperator Why24CCZSpace :=
  (why24CCZSiteTransport count site).conjDensity
    ((why24CCZSiteSubsystem count site).selectedPartialTraceFromRegister.mapDensity
      preparation.why24LocalStochasticPreparedDensity)
noncomputable def why24LocalStochasticResourceInputs {count : Nat}
    (preparation : Why24LocalStochasticPreparation (Fin count)
      (why24IdealCCZRegisterDensity count)) :
    ResourceInput count Why24CCZSpace :=
  fun site => why24LocalStochasticSiteMarginal preparation site
noncomputable def why24LocalStochasticInputErrorModel {count : Nat}
    (preparation : Why24LocalStochasticPreparation (Fin count)
      (why24IdealCCZRegisterDensity count)) :
    LocalStochasticInputErrorModel count Why24CCZSpace where
  rate := preparation.rate
  rate_nonneg := preparation.rate_nonneg
  rate_le_one := preparation.rate_le_one
  admissible actualRate inputs :=
    actualRate = preparation.rate ∧
      inputs = why24LocalStochasticResourceInputs preparation
theorem why24LocalStochasticInputErrorModel_permits {count : Nat}
    (preparation : Why24LocalStochasticPreparation (Fin count)
      (why24IdealCCZRegisterDensity count)) :
    InputErrorModel.Permits
      (InputErrorModel.localStochastic
        (why24LocalStochasticInputErrorModel preparation))
      (why24LocalStochasticResourceInputs preparation) :=
  ⟨rfl, rfl⟩
open QEC.Distillation.OneQubitMagic
noncomputable def why24OneQubitXBasis :
    OrthonormalBasis (Fin 2) Complex Qubit.QubitSpace :=
  (EuclideanSpace.basisFun (Fin 2) Complex).map
    hadamardTransport.toLinearIsometryEquiv
noncomputable def why24ThreeQubitTensorRegisterTransport :
    UnitaryTransport
      (FiniteInstrument.tensorPowerCarrier Qubit.QubitSpace 3)
      Why24CCZSpace := by
  let sourceBasis := FiniteInstrument.tensorPowerBasis
    (EuclideanSpace.basisFun (Fin 2) Complex) 3
  let targetBasis :=
    EuclideanSpace.basisFun (Qubit.Bitstring (Fin 3)) Complex
  let U := sourceBasis.equiv targetBasis
    (FiniteInstrument.tensorPowerHistoryEquiv (Fin 2) 3)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }
noncomputable def why24ThreeQubitXBasis :
    OrthonormalBasis (Qubit.Bitstring (Fin 3)) Complex Why24CCZSpace :=
  ((FiniteInstrument.tensorPowerBasis why24OneQubitXBasis 3).map
    why24ThreeQubitTensorRegisterTransport.toLinearIsometryEquiv).reindex
      (FiniteInstrument.tensorPowerHistoryEquiv (Fin 2) 3)
noncomputable def why24CCZPhaseOperator : Operator Why24CCZSpace where
  toFun psi := WithLp.toLp 2 fun bits =>
    PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits) * psi bits
  map_add' left right := by
    ext bits
    simp [mul_add]
  map_smul' scalar psi := by
    ext bits
    simp [smul_eq_mul, mul_left_comm]
@[simp] theorem why24CCZPhaseOperator_apply
    (psi : Why24CCZSpace) (bits : Qubit.Bitstring (Fin 3)) :
    why24CCZPhaseOperator psi bits =
      PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits) * psi bits :=
  rfl
theorem why24BinaryPhaseScalar_mul_self (phase : ZMod 2) :
    PauliSymplectic.binaryPhaseScalar phase *
        PauliSymplectic.binaryPhaseScalar phase = 1 := by
  rw [← PauliSymplectic.binaryPhaseScalar_add]
  have hself : phase + phase = 0 := by
    fin_cases phase <;> decide
  rw [hself, PauliSymplectic.binaryPhaseScalar_zero]
theorem why24CCZPhaseOperator_square :
    why24CCZPhaseOperator * why24CCZPhaseOperator = 1 := by
  ext psi bits
  simp only [Module.End.mul_apply, why24CCZPhaseOperator_apply,
    Module.End.one_apply, ← mul_assoc, why24BinaryPhaseScalar_mul_self, one_mul]
noncomputable def why24CCZPhaseLinearEquiv :
    Why24CCZSpace ≃ₗ[Complex] Why24CCZSpace :=
  LinearEquiv.mk why24CCZPhaseOperator why24CCZPhaseOperator
    (fun psi => by
      have h := LinearMap.congr_fun why24CCZPhaseOperator_square psi
      simpa [Module.End.mul_apply] using h)
    (fun psi => by
      have h := LinearMap.congr_fun why24CCZPhaseOperator_square psi
      simpa [Module.End.mul_apply] using h)
@[simp] theorem why24CCZPhaseLinearEquiv_apply
    (psi : Why24CCZSpace) :
    why24CCZPhaseLinearEquiv psi = why24CCZPhaseOperator psi :=
  rfl
noncomputable def why24CCZPhaseTransport :
    UnitaryTransport Why24CCZSpace Why24CCZSpace where
  toLinearEquiv := why24CCZPhaseLinearEquiv
  map_inner := by
    intro left right
    rw [PiLp.inner_apply, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro bits _
    simp only [why24CCZPhaseLinearEquiv_apply,
      why24CCZPhaseOperator_apply, RCLike.inner_apply, map_mul]
    have hstar :
        starRingEnd Complex
            (PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits)) =
          PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits) :=
      PauliSymplectic.binaryPhaseScalar_star _
    rw [hstar]
    calc
      (PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits) * right bits) *
          (PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits) *
            star (left bits)) =
          (PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits) *
              PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits)) *
            (right bits * star (left bits)) := by ring
      _ = right bits * star (left bits) := by
        rw [why24BinaryPhaseScalar_mul_self, one_mul]
noncomputable def why24CCZMagicBasis :
    OrthonormalBasis (Qubit.Bitstring (Fin 3)) Complex Why24CCZSpace :=
  why24ThreeQubitXBasis.map why24CCZPhaseTransport.toLinearIsometryEquiv
noncomputable def why24CCZMagicBasisKet
    (error : Qubit.Bitstring (Fin 3)) : Why24CCZSpace :=
  why24CCZMagicBasis error
theorem why24OneQubitXBasis_zero_apply (bit : Fin 2) :
    why24OneQubitXBasis 0 bit = (Real.sqrt 2 : Complex)⁻¹ := by
  change hadamardOperator
      (EuclideanSpace.basisFun (Fin 2) Complex 0) bit = _
  fin_cases bit <;> simp
theorem why24TensorPowerOneQubitBasis_inner_eq_prod
    (leftBasis rightBasis :
      OrthonormalBasis (Fin 2) Complex Qubit.QubitSpace) :
    forall (count : Nat)
      (left right : FiniteInstrument.tensorPowerHistory (Fin 2) count),
      inner Complex
          (FiniteInstrument.tensorPowerBasis leftBasis count left)
          (FiniteInstrument.tensorPowerBasis rightBasis count right) =
        ∏ site : Fin count,
          inner Complex
            (leftBasis (FiniteInstrument.tensorPowerHistoryAt
              (Fin 2) count left site))
            (rightBasis (FiniteInstrument.tensorPowerHistoryAt
              (Fin 2) count right site)) := by
  intro count
  induction count with
  | zero =>
      intro left right
      cases left
      cases right
      rw [FiniteInstrument.tensorPowerBasis_zero_apply,
        FiniteInstrument.tensorPowerBasis_zero_apply]
      rw [inner_self_eq_norm_sq_to_K,
        (EuclideanSpace.basisFun
          (ULift (Fin 1)) Complex).norm_eq_one]
      simp
  | succ count ih =>
      rintro ⟨leftHead, leftTail⟩ ⟨rightHead, rightTail⟩
      rw [FiniteInstrument.tensorPowerBasis_succ_apply,
        FiniteInstrument.tensorPowerBasis_succ_apply,
        TensorProduct.inner_tmul, Fin.prod_univ_succ]
      simp only [FiniteInstrument.tensorPowerHistoryAt,
        Fin.cases_zero, Fin.cases_succ]
      rw [ih leftTail rightTail]
set_option maxRecDepth 4096 in
theorem why24ThreeQubitXBasis_zero_apply
    (bits : Qubit.Bitstring (Fin 3)) :
    why24ThreeQubitXBasis 0 bits =
      ((Real.sqrt 2 : Complex)⁻¹) ^ 3 := by
  let computationalHistory :=
    (FiniteInstrument.tensorPowerHistoryEquiv (Fin 2) 3).symm bits
  let zeroHistory :=
    (FiniteInstrument.tensorPowerHistoryEquiv (Fin 2) 3).symm
      (0 : Qubit.Bitstring (Fin 3))
  have hinner := why24ThreeQubitTensorRegisterTransport.map_inner
    (FiniteInstrument.tensorPowerBasis
      (EuclideanSpace.basisFun (Fin 2) Complex) 3 computationalHistory)
    (FiniteInstrument.tensorPowerBasis
      why24OneQubitXBasis 3 zeroHistory)
  have hcomputational :
      why24ThreeQubitTensorRegisterTransport
          (FiniteInstrument.tensorPowerBasis
            (EuclideanSpace.basisFun (Fin 2) Complex)
            3 computationalHistory) =
        EuclideanSpace.basisFun
          (Qubit.Bitstring (Fin 3)) Complex bits := by
    dsimp [why24ThreeQubitTensorRegisterTransport]
    rw [OrthonormalBasis.equiv_apply_basis]
    exact congrArg
      (EuclideanSpace.basisFun (Qubit.Bitstring (Fin 3)) Complex)
      ((FiniteInstrument.tensorPowerHistoryEquiv
        (Fin 2) 3).apply_symm_apply bits)
  have hzero :
      why24ThreeQubitTensorRegisterTransport
          (FiniteInstrument.tensorPowerBasis
            why24OneQubitXBasis 3 zeroHistory) =
        why24ThreeQubitXBasis 0 := by
    rw [why24ThreeQubitXBasis, OrthonormalBasis.reindex_apply]
    rfl
  rw [hcomputational, hzero, EuclideanSpace.basisFun_inner] at hinner
  rw [why24TensorPowerOneQubitBasis_inner_eq_prod] at hinner
  have hcomputationalAt (site : Fin 3) :
      FiniteInstrument.tensorPowerHistoryAt
          (Fin 2) 3 computationalHistory site = bits site := by
    exact congrFun
      ((FiniteInstrument.tensorPowerHistoryEquiv
        (Fin 2) 3).apply_symm_apply bits) site
  have hzeroAt (site : Fin 3) :
      FiniteInstrument.tensorPowerHistoryAt
          (Fin 2) 3 zeroHistory site = 0 := by
    exact congrFun
      ((FiniteInstrument.tensorPowerHistoryEquiv
        (Fin 2) 3).apply_symm_apply
          (0 : Qubit.Bitstring (Fin 3))) site
  simp_rw [hcomputationalAt, hzeroAt,
    EuclideanSpace.basisFun_inner,
    why24OneQubitXBasis_zero_apply] at hinner
  simpa using hinner
theorem why24CCZMagicBasisKet_zero_apply
    (bits : Qubit.Bitstring (Fin 3)) :
    why24CCZMagicBasisKet 0 bits =
      PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits) *
        ((Real.sqrt 2 : Complex)⁻¹) ^ 3 := by
  change why24CCZPhaseOperator (why24ThreeQubitXBasis 0) bits = _
  rw [why24CCZPhaseOperator_apply, why24ThreeQubitXBasis_zero_apply]
theorem why24CCZMagicState_apply_in_magic_normalization
    (bits : Qubit.Bitstring (Fin 3)) :
    why24CCZMagicState bits =
      PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits) *
        ((Real.sqrt 2 : Complex)⁻¹) ^ 3 := by
  rw [why24CCZMagicState]
  change (Real.sqrt 128 : Complex) *
      (PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits) *
        (Real.sqrt (Fintype.card F1024 : Real) : Complex)⁻¹) = _
  have hsqrtCard :
      Real.sqrt (Fintype.card F1024 : Real) = 32 := by
    rw [f1024_card]
    norm_num
  have hsqrt128 : Real.sqrt (128 : Real) = 8 * Real.sqrt 2 := by
    have hsqrtNonneg := Real.sqrt_nonneg (128 : Real)
    have hsqrtTwoNonneg := Real.sqrt_nonneg (2 : Real)
    have hsqrtSq := Real.sq_sqrt (show (0 : Real) ≤ 128 by norm_num)
    have hsqrtTwoSq := Real.sq_sqrt (show (0 : Real) ≤ 2 by norm_num)
    nlinarith
  rw [hsqrtCard, hsqrt128]
  have hsqrtTwoNe : (Real.sqrt 2 : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr sqrt_two_pos.ne'
  have hsqrtTwoMul :
      (Real.sqrt 2 : Complex) * (Real.sqrt 2 : Complex) = 2 := by
    exact_mod_cast sqrt_two_mul_self
  have hsqrtTwoCube :
      (Real.sqrt 2 : Complex) ^ 3 = 2 * (Real.sqrt 2 : Complex) := by
    calc
      (Real.sqrt 2 : Complex) ^ 3 =
          ((Real.sqrt 2 : Complex) * (Real.sqrt 2 : Complex)) *
            (Real.sqrt 2 : Complex) := by ring
      _ = 2 * (Real.sqrt 2 : Complex) := by rw [hsqrtTwoMul]
  field_simp [hsqrtTwoNe]
  push_cast
  rw [hsqrtTwoCube]
  calc
    8 * (Real.sqrt 2 : Complex) *
          PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits) *
          (2 * (Real.sqrt 2 : Complex)) =
        ((Real.sqrt 2 : Complex) * (Real.sqrt 2 : Complex)) *
          (PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits) * 16) := by
      ring
    _ = 2 *
        (PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits) * 16) := by
      rw [hsqrtTwoMul]
    _ = PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits) * 32 := by
      ring
theorem why24CCZMagicBasisKet_zero_eq_magicState :
    why24CCZMagicBasisKet 0 = why24CCZMagicState := by
  ext bits
  rw [why24CCZMagicBasisKet_zero_apply,
    why24CCZMagicState_apply_in_magic_normalization]
theorem why24PureDensity_matrixEntry {ι : Type} [Fintype ι]
    (psi : EuclideanSpace Complex ι) (hnorm : ‖psi‖ ^ 2 = 1)
    (left right : ι) :
    inner Complex (EuclideanSpace.basisFun ι Complex left)
        ((DensityOperator.pureDensity psi hnorm).toOperator
          (EuclideanSpace.basisFun ι Complex right)) =
      star (psi right) * psi left := by
  rw [DensityOperator.pureDensity_toOperator]
  change inner Complex (EuclideanSpace.basisFun ι Complex left)
      (inner Complex psi (EuclideanSpace.basisFun ι Complex right) • psi) = _
  rw [inner_smul_right, EuclideanSpace.basisFun_inner,
    ← inner_conj_symm psi (EuclideanSpace.basisFun ι Complex right),
    EuclideanSpace.basisFun_inner]
  rfl
theorem why24CCZMagicStateDensity_matrixEntry
    (left right : Qubit.Bitstring (Fin 3)) :
    inner Complex
        (EuclideanSpace.basisFun (Qubit.Bitstring (Fin 3)) Complex left)
        (why24CCZMagicStateDensity.toOperator
          (EuclideanSpace.basisFun
            (Qubit.Bitstring (Fin 3)) Complex right)) =
      star (why24CCZMagicState right) * why24CCZMagicState left := by
  rw [why24CCZMagicStateDensity]
  exact why24PureDensity_matrixEntry why24CCZMagicState _ left right
noncomputable def why24JointCCZMagicBasis (count : Nat) :
    OrthonormalBasis (Fin count -> Qubit.Bitstring (Fin 3)) Complex
      (Why24CCZRegister (Fin count)) :=
  ((FiniteInstrument.tensorPowerBasis why24CCZMagicBasis count).map
      (FiniteInstrument.tensorPowerQubitRegisterTransport
        (Fin 3) count).toLinearIsometryEquiv).reindex
    (FiniteInstrument.tensorPowerHistoryEquiv
      (Qubit.Bitstring (Fin 3)) count)
noncomputable def why24JointCCZMagicBasisKet (count : Nat)
    (error : Fin count -> Qubit.Bitstring (Fin 3)) :
    Why24CCZRegister (Fin count) :=
  why24JointCCZMagicBasis count error
theorem why24JointCCZMagicBasisKet_norm (count : Nat)
    (error : Fin count -> Qubit.Bitstring (Fin 3)) :
    ‖why24JointCCZMagicBasisKet count error‖ = 1 :=
  (why24JointCCZMagicBasis count).orthonormal.norm_eq_one error
theorem why24JointCCZMagicBasisKet_normSq (count : Nat)
    (error : Fin count -> Qubit.Bitstring (Fin 3)) :
    ‖why24JointCCZMagicBasisKet count error‖ ^ 2 = 1 := by
  rw [why24JointCCZMagicBasisKet_norm]
  norm_num
theorem why24TensorPowerCCZBasis_inner_eq_prod
    (leftBasis rightBasis :
      OrthonormalBasis (Qubit.Bitstring (Fin 3)) Complex Why24CCZSpace) :
    forall (count : Nat)
      (left right : FiniteInstrument.tensorPowerHistory
        (Qubit.Bitstring (Fin 3)) count),
      inner Complex
          (FiniteInstrument.tensorPowerBasis leftBasis count left)
          (FiniteInstrument.tensorPowerBasis rightBasis count right) =
        ∏ site : Fin count,
          inner Complex
            (leftBasis (FiniteInstrument.tensorPowerHistoryAt
              (Qubit.Bitstring (Fin 3)) count left site))
            (rightBasis (FiniteInstrument.tensorPowerHistoryAt
              (Qubit.Bitstring (Fin 3)) count right site)) := by
  intro count
  induction count with
  | zero =>
      intro left right
      cases left
      cases right
      rw [FiniteInstrument.tensorPowerBasis_zero_apply,
        FiniteInstrument.tensorPowerBasis_zero_apply]
      rw [inner_self_eq_norm_sq_to_K,
        (EuclideanSpace.basisFun
          (ULift (Fin 1)) Complex).norm_eq_one]
      simp
  | succ count ih =>
      rintro ⟨leftHead, leftTail⟩ ⟨rightHead, rightTail⟩
      rw [FiniteInstrument.tensorPowerBasis_succ_apply,
        FiniteInstrument.tensorPowerBasis_succ_apply,
        TensorProduct.inner_tmul, Fin.prod_univ_succ]
      simp only [FiniteInstrument.tensorPowerHistoryAt,
        Fin.cases_zero, Fin.cases_succ]
      rw [ih leftTail rightTail]
theorem why24JointCCZMagicBasisKet_apply (count : Nat)
    (error : Fin count -> Qubit.Bitstring (Fin 3))
    (bits : Qubit.Bitstring (Fin count × Fin 3)) :
    why24JointCCZMagicBasisKet count error bits =
      ∏ site : Fin count,
        why24CCZMagicBasisKet (error site)
          (fun qubit => bits (site, qubit)) := by
  let computationalHistory :=
    (FiniteInstrument.tensorPowerQubitBitstringEquiv
      (Fin 3) count).symm bits
  let magicHistory :=
    FiniteInstrument.tensorPowerHistoryOf
      (Qubit.Bitstring (Fin 3)) count error
  have hinner := (FiniteInstrument.tensorPowerQubitRegisterTransport
      (Fin 3) count).map_inner
    (FiniteInstrument.tensorPowerBasis
      (EuclideanSpace.basisFun (Qubit.Bitstring (Fin 3)) Complex)
      count computationalHistory)
    (FiniteInstrument.tensorPowerBasis why24CCZMagicBasis
      count magicHistory)
  rw [FiniteInstrument.tensorPowerQubitRegisterTransport_apply_basis] at hinner
  have hcomputational :
      FiniteInstrument.tensorPowerQubitBitstringEquiv
          (Fin 3) count computationalHistory = bits := by
    exact (FiniteInstrument.tensorPowerQubitBitstringEquiv
      (Fin 3) count).apply_symm_apply bits
  have hjoint :
      FiniteInstrument.tensorPowerQubitRegisterTransport (Fin 3) count
          (FiniteInstrument.tensorPowerBasis why24CCZMagicBasis
            count magicHistory) =
        why24JointCCZMagicBasisKet count error := by
    rw [why24JointCCZMagicBasisKet, why24JointCCZMagicBasis,
      OrthonormalBasis.reindex_apply]
    rfl
  rw [hcomputational, hjoint, EuclideanSpace.basisFun_inner] at hinner
  rw [why24TensorPowerCCZBasis_inner_eq_prod] at hinner
  have hcomputationalAt (site : Fin count) :
      FiniteInstrument.tensorPowerHistoryAt
          (Qubit.Bitstring (Fin 3)) count computationalHistory site =
        fun qubit => bits (site, qubit) := by
    funext qubit
    exact FiniteInstrument.tensorPowerQubitBitstringEquiv_symm_at
      (Fin 3) count bits site qubit
  have hmagicAt (site : Fin count) :
      FiniteInstrument.tensorPowerHistoryAt
          (Qubit.Bitstring (Fin 3)) count magicHistory site = error site := by
    exact congrFun (FiniteInstrument.tensorPowerHistoryAt_of
      (Qubit.Bitstring (Fin 3)) count error) site
  simp_rw [hcomputationalAt, hmagicAt] at hinner
  simpa only [EuclideanSpace.basisFun_inner,
    why24CCZMagicBasisKet] using hinner
theorem why24IdealCCZRegisterDensity_eq_jointZeroPure (count : Nat) :
    why24IdealCCZRegisterDensity count =
      DensityOperator.pureDensity
        (why24JointCCZMagicBasisKet count 0)
        (why24JointCCZMagicBasisKet_normSq count 0) := by
  apply DensityOperator.ext_toOperator
  let basis := EuclideanSpace.basisFun
    (Qubit.Bitstring (Fin count × Fin 3)) Complex
  apply basis.toBasis.ext
  intro right
  apply InnerProductSpace.ext_inner_left_basis basis.toBasis
  intro left
  dsimp [basis]
  rw [why24IdealCCZRegisterDensity,
    FiniteInstrument.tensorPowerRegisterProductDensity_matrixEntry]
  simp_rw [why24CCZMagicStateDensity_matrixEntry]
  rw [inner_smul_right, EuclideanSpace.basisFun_inner,
    ← inner_conj_symm (why24JointCCZMagicBasisKet count 0)
      (EuclideanSpace.basisFun
        (Qubit.Bitstring (Fin count × Fin 3)) Complex right),
    EuclideanSpace.basisFun_inner,
    why24JointCCZMagicBasisKet_apply,
    why24JointCCZMagicBasisKet_apply]
  simp only [Pi.zero_apply]
  rw [why24CCZMagicBasisKet_zero_eq_magicState]
  rw [map_prod, Finset.prod_mul_distrib]
  rfl
theorem why24IdealCCZRegisterDensity_toOperator (count : Nat) :
    (why24IdealCCZRegisterDensity count).toOperator =
      (InnerProductSpace.rankOne Complex
        (why24JointCCZMagicBasisKet count 0)
        (why24JointCCZMagicBasisKet count 0)).toLinearMap := by
  rw [why24IdealCCZRegisterDensity_eq_jointZeroPure,
    DensityOperator.pureDensity_toOperator]
noncomputable def why24FaultSelectedMagicState {count : Nat}
    (fault : Finset (Fin count))
    (error : Fin count -> Qubit.Bitstring (Fin 3)) :
    (why24FaultSubsystem fault).selectedSystem :=
  WithLp.toLp 2 fun selected =>
    ∏ site : ↥fault,
      why24CCZMagicBasisKet (error site) fun qubit =>
        selected ⟨(site, qubit), by
          rw [why24FaultSubsystem_selected]
          exact Finset.mem_product.mpr ⟨site.property, Finset.mem_univ _⟩⟩
noncomputable def why24FaultComplementMagicState {count : Nat}
    (fault : Finset (Fin count))
    (error : Fin count -> Qubit.Bitstring (Fin 3)) :
    (why24FaultSubsystem fault).complementSystem :=
  WithLp.toLp 2 fun complement =>
    ∏ site : ↥faultᶜ,
      why24CCZMagicBasisKet (error site) fun qubit =>
        complement ⟨(site, qubit), by
          rw [why24FaultSubsystem_selected]
          intro hselected
          exact (Finset.mem_compl.mp site.property)
            (Finset.mem_product.mp hselected).1⟩
theorem why24FaultRegisterFactorization_symm_tmul_apply {count : Nat}
    (fault : Finset (Fin count))
    (selectedState : (why24FaultSubsystem fault).selectedSystem)
    (complementState : (why24FaultSubsystem fault).complementSystem)
    (bits : Qubit.Bitstring (Fin count × Fin 3)) :
    (why24FaultSubsystem fault).registerFactorization.symm
        (selectedState ⊗ₜ[Complex] complementState) bits =
      selectedState ((why24FaultSubsystem fault).splitLabel bits).1 *
        complementState ((why24FaultSubsystem fault).splitLabel bits).2 := by
  have hinner := (why24FaultSubsystem fault).registerFactorization.map_inner
    (EuclideanSpace.basisFun
      (Qubit.Bitstring (Fin count × Fin 3)) Complex bits)
    ((why24FaultSubsystem fault).registerFactorization.symm
      (selectedState ⊗ₜ[Complex] complementState))
  simp only [UnitaryTransport.symm_toLinearEquiv,
    LinearEquiv.apply_symm_apply] at hinner
  rw [QuditSubsystem.registerFactorization_apply_basis,
    TensorProduct.inner_tmul,
    EuclideanSpace.basisFun_inner,
    EuclideanSpace.basisFun_inner,
    EuclideanSpace.basisFun_inner] at hinner
  exact hinner.symm
theorem why24JointCCZMagicBasisKet_faultFactorization {count : Nat}
    (fault : Finset (Fin count))
    (error : Fin count -> Qubit.Bitstring (Fin 3)) :
    (why24FaultSubsystem fault).registerFactorization
        (why24JointCCZMagicBasisKet count error) =
      why24FaultSelectedMagicState fault error ⊗ₜ[Complex]
        why24FaultComplementMagicState fault error := by
  apply (why24FaultSubsystem fault).registerFactorization.symm.toLinearEquiv.injective
  simp only [UnitaryTransport.symm_toLinearEquiv,
    LinearEquiv.symm_apply_apply]
  ext bits
  change why24JointCCZMagicBasisKet count error bits =
    (why24FaultSubsystem fault).registerFactorization.symm
      (why24FaultSelectedMagicState fault error ⊗ₜ[Complex]
        why24FaultComplementMagicState fault error) bits
  rw [why24FaultRegisterFactorization_symm_tmul_apply,
    why24JointCCZMagicBasisKet_apply]
  change (∏ site : Fin count,
      why24CCZMagicBasisKet (error site) (fun qubit => bits (site, qubit))) =
    (∏ site : ↥fault,
      why24CCZMagicBasisKet (error site) (fun qubit =>
        ((why24FaultSubsystem fault).splitLabel bits).1
          ⟨(site, qubit), by
            rw [why24FaultSubsystem_selected]
            exact Finset.mem_product.mpr ⟨site.property, Finset.mem_univ _⟩⟩)) *
      ∏ site : ↥faultᶜ,
        why24CCZMagicBasisKet (error site) (fun qubit =>
          ((why24FaultSubsystem fault).splitLabel bits).2
            ⟨(site, qubit), by
              rw [why24FaultSubsystem_selected]
              intro hselected
              exact (Finset.mem_compl.mp site.property)
                (Finset.mem_product.mp hselected).1⟩)
  simp only [QuditSubsystem.splitLabel]
  let amplitude : Fin count -> Complex := fun site =>
    why24CCZMagicBasisKet (error site) (fun qubit => bits (site, qubit))
  change (∏ site, amplitude site) =
    (∏ site : ↥fault, amplitude site) * ∏ site : ↥faultᶜ, amplitude site
  calc
    (∏ site, amplitude site) =
        (∏ site ∈ fault, amplitude site) * ∏ site ∈ faultᶜ, amplitude site :=
      (Finset.prod_mul_prod_compl fault amplitude).symm
    _ = (∏ site : ↥fault, amplitude site) *
          ∏ site : ↥faultᶜ, amplitude site :=
      congrArg₂ (fun x y : Complex => x * y)
        (Finset.prod_coe_sort fault amplitude).symm
        (Finset.prod_coe_sort faultᶜ amplitude).symm
theorem why24FaultRegisterFactorization_extendLocalToRegister_apply
    {count : Nat} (fault : Finset (Fin count))
    (localOperator : Operator (why24FaultSubsystem fault).selectedSystem)
    (psi : Why24CCZRegister (Fin count)) :
    (why24FaultSubsystem fault).registerFactorization
        ((why24FaultSubsystem fault).extendLocalToRegister localOperator psi) =
      (why24FaultSubsystem fault).extendLocal localOperator
        ((why24FaultSubsystem fault).registerFactorization psi) := by
  simp [QuditSubsystem.extendLocalToRegister,
    UnitaryTransport.conjOperator_apply]
def why24OutsideFaultError {count : Nat}
    (fault : Finset (Fin count))
    (error : Fin count -> Qubit.Bitstring (Fin 3)) :
    Fin count -> Qubit.Bitstring (Fin 3) :=
  fun site => if site ∈ fault then 0 else error site
theorem why24OutsideFaultError_ne_zero {count : Nat}
    (fault : Finset (Fin count))
    (error : Fin count -> Qubit.Bitstring (Fin 3))
    (site : Fin count) (hsite : site ∉ fault)
    (herror : error site ≠ 0) :
    why24OutsideFaultError fault error ≠ 0 := by
  intro hzero
  have hat := congrFun hzero site
  rw [why24OutsideFaultError, if_neg hsite] at hat
  exact herror hat
theorem why24FaultSelectedMagicState_outside {count : Nat}
    (fault : Finset (Fin count))
    (error : Fin count -> Qubit.Bitstring (Fin 3)) :
    why24FaultSelectedMagicState fault
        (why24OutsideFaultError fault error) =
      why24FaultSelectedMagicState fault 0 := by
  ext selected
  simp [why24FaultSelectedMagicState, why24OutsideFaultError]
theorem why24FaultComplementMagicState_outside {count : Nat}
    (fault : Finset (Fin count))
    (error : Fin count -> Qubit.Bitstring (Fin 3)) :
    why24FaultComplementMagicState fault
        (why24OutsideFaultError fault error) =
      why24FaultComplementMagicState fault error := by
  ext complement
  apply Fintype.prod_congr
  intro site
  rw [why24OutsideFaultError,
    if_neg (Finset.mem_compl.mp site.property)]
theorem why24FaultComplementMagicState_inner_zero_of_outside
    {count : Nat} (fault : Finset (Fin count))
    (error : Fin count -> Qubit.Bitstring (Fin 3))
    (site : Fin count) (hsite : site ∉ fault)
    (herror : error site ≠ 0) :
    inner Complex (why24FaultComplementMagicState fault error)
        (why24FaultComplementMagicState fault 0) = 0 := by
  let outside := why24OutsideFaultError fault error
  have houtside_ne : outside ≠ 0 :=
    why24OutsideFaultError_ne_zero fault error site hsite herror
  have horthogonal :
      inner Complex (why24JointCCZMagicBasisKet count outside)
          (why24JointCCZMagicBasisKet count 0) = 0 := by
    change inner Complex
      ((why24JointCCZMagicBasis count) outside)
      ((why24JointCCZMagicBasis count) 0) = 0
    rw [(why24JointCCZMagicBasis count).inner_eq_ite,
      if_neg houtside_ne]
  have hfactored :=
    (why24FaultSubsystem fault).registerFactorization.map_inner
      (why24JointCCZMagicBasisKet count outside)
      (why24JointCCZMagicBasisKet count 0)
  rw [why24JointCCZMagicBasisKet_faultFactorization,
    why24JointCCZMagicBasisKet_faultFactorization,
    TensorProduct.inner_tmul,
    why24FaultSelectedMagicState_outside,
    why24FaultComplementMagicState_outside,
    horthogonal] at hfactored
  have hzeroFactored := hfactored
  have hzeroSelf :
      inner Complex (why24JointCCZMagicBasisKet count 0)
          (why24JointCCZMagicBasisKet count 0) = 1 := by
    change inner Complex
      ((why24JointCCZMagicBasis count) 0)
      ((why24JointCCZMagicBasis count) 0) = 1
    rw [inner_self_eq_norm_sq_to_K,
      (why24JointCCZMagicBasis count).orthonormal.norm_eq_one]
    norm_num
  have hself :=
    (why24FaultSubsystem fault).registerFactorization.map_inner
      (why24JointCCZMagicBasisKet count 0)
      (why24JointCCZMagicBasisKet count 0)
  rw [why24JointCCZMagicBasisKet_faultFactorization,
    TensorProduct.inner_tmul, hzeroSelf] at hself
  have hselected_ne :
      inner Complex (why24FaultSelectedMagicState fault 0)
          (why24FaultSelectedMagicState fault 0) ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hself
    norm_num at hself
  exact (mul_eq_zero.mp hzeroFactored).resolve_left hselected_ne
theorem why24SupportedOperator_magicAmplitude_eq_zero
    {count : Nat} (fault : Finset (Fin count))
    (operator : Operator (Why24CCZRegister (Fin count)))
    (hsupported :
      (why24FaultSubsystem fault).OperatorSupportedOnRegister operator)
    (error : Fin count -> Qubit.Bitstring (Fin 3))
    (site : Fin count) (hsite : site ∉ fault)
    (herror : error site ≠ 0) :
    inner Complex (why24JointCCZMagicBasisKet count error)
        (operator (why24JointCCZMagicBasisKet count 0)) = 0 := by
  rcases hsupported with ⟨localOperator, rfl⟩
  have hfactored :=
    (why24FaultSubsystem fault).registerFactorization.map_inner
      (why24JointCCZMagicBasisKet count error)
      ((why24FaultSubsystem fault).extendLocalToRegister localOperator
        (why24JointCCZMagicBasisKet count 0))
  rw [why24JointCCZMagicBasisKet_faultFactorization,
    why24FaultRegisterFactorization_extendLocalToRegister_apply,
    why24JointCCZMagicBasisKet_faultFactorization,
    QuditSubsystem.extendLocal_apply_tmul,
    TensorProduct.inner_tmul,
    why24FaultComplementMagicState_inner_zero_of_outside
      fault error site hsite herror,
    mul_zero] at hfactored
  exact hfactored.symm
theorem why24CCZMagicBasisKet_norm
    (error : Qubit.Bitstring (Fin 3)) :
    ‖why24CCZMagicBasisKet error‖ = 1 :=
  why24CCZMagicBasis.orthonormal.norm_eq_one error
theorem why24CCZMagicBasisKet_normSq
    (error : Qubit.Bitstring (Fin 3)) :
    ‖why24CCZMagicBasisKet error‖ ^ 2 = 1 := by
  rw [why24CCZMagicBasisKet_norm]
  norm_num
noncomputable def why24CCZStabilizer (generator : Fin 3) :
    Operator Why24CCZSpace :=
  ∑ error : Qubit.Bitstring (Fin 3),
    PauliSymplectic.binaryPhaseScalar
        ((PauliSymplectic.bitstringWordEquiv (Fin 3) error) generator) •
      (InnerProductSpace.rankOne Complex
        (why24CCZMagicBasisKet error)
        (why24CCZMagicBasisKet error)).toLinearMap
noncomputable def why24CCZTwirlKraus :
    FiniteKrausFamily (Qubit.Bitstring (Fin 3)) Why24CCZSpace Why24CCZSpace where
  operator error := (InnerProductSpace.rankOne Complex
    (why24CCZMagicBasisKet error)
    (why24CCZMagicBasisKet error)).toLinearMap
noncomputable def why24CCZTwirlInstrument :
    FiniteInstrument (Qubit.Bitstring (Fin 3)) (Qubit.Bitstring (Fin 3))
      Why24CCZSpace Why24CCZSpace where
  kraus := why24CCZTwirlKraus
  observe := id
theorem why24CCZTwirlKraus_adjoint
    (error : Qubit.Bitstring (Fin 3)) :
    LinearMap.adjoint (why24CCZTwirlKraus.operator error) =
      why24CCZTwirlKraus.operator error := by
  simp only [why24CCZTwirlKraus]
  rw [LinearMap.adjoint_eq_toCLM_adjoint]
  change ((InnerProductSpace.rankOne Complex
    (why24CCZMagicBasisKet error)
    (why24CCZMagicBasisKet error)).adjoint).toLinearMap = _
  rw [InnerProductSpace.adjoint_rankOne]
theorem why24CCZTwirlInstrument_complete :
    why24CCZTwirlInstrument.kraus.Complete := by
  unfold FiniteKrausFamily.Complete
  change (∑ error : Qubit.Bitstring (Fin 3),
    LinearMap.adjoint (why24CCZTwirlKraus.operator error) *
      why24CCZTwirlKraus.operator error) = 1
  calc
    (∑ error : Qubit.Bitstring (Fin 3),
      LinearMap.adjoint (why24CCZTwirlKraus.operator error) *
        why24CCZTwirlKraus.operator error) =
        ∑ error : Qubit.Bitstring (Fin 3),
          why24CCZTwirlKraus.operator error := by
      apply Finset.sum_congr rfl
      intro error _
      let P : Operator Why24CCZSpace := why24CCZTwirlKraus.operator error
      have hP : P.IsSymmetricProjection := by
        simpa [P, why24CCZTwirlKraus] using
          (InnerProductSpace.isSymmetricProjection_rankOne_self
            (𝕜 := Complex) (why24CCZMagicBasisKet_norm error))
      rw [why24CCZTwirlKraus_adjoint]
      change P * P = P
      exact hP.isIdempotentElem.eq
    _ = 1 := by
      have hport := congrArg ContinuousLinearMap.toLinearMap
        (OrthonormalBasis.sum_rankOne_eq_id why24CCZMagicBasis)
      simp [why24CCZTwirlKraus, why24CCZMagicBasisKet] at hport ⊢
      exact hport
noncomputable def why24CCZTwirlChannel :
    QuantumChannel Why24CCZSpace Why24CCZSpace :=
  why24CCZTwirlInstrument.kraus.toQuantumChannel
    why24CCZTwirlInstrument_complete
noncomputable def why24TwirledZErrorDistribution
    (rho : DensityOperator Why24CCZSpace)
    (error : Qubit.Bitstring (Fin 3)) : Real :=
  (inner Complex (why24CCZMagicBasisKet error)
    (rho.toOperator (why24CCZMagicBasisKet error))).re
theorem why24TwirledZErrorDistribution_nonneg
    (rho : DensityOperator Why24CCZSpace)
    (error : Qubit.Bitstring (Fin 3)) :
    0 ≤ why24TwirledZErrorDistribution rho error := by
  exact rho.positive.re_inner_nonneg_right
    (why24CCZMagicBasisKet error)
theorem why24TwirledZErrorDistribution_sum
    (rho : DensityOperator Why24CCZSpace) :
    ∑ error : Qubit.Bitstring (Fin 3),
      why24TwirledZErrorDistribution rho error = 1 := by
  have htrace := rho.trace_one
  rw [LinearMap.trace_eq_sum_inner rho.toOperator why24CCZMagicBasis] at htrace
  have hre := congrArg Complex.re htrace
  simpa [why24TwirledZErrorDistribution, why24CCZMagicBasisKet,
    Complex.re_sum] using hre
noncomputable def why24CCZStochasticZMixture
    (rho : DensityOperator Why24CCZSpace) : DensityOperator Why24CCZSpace :=
  DensityOperator.convexCombination Finset.univ
    (why24TwirledZErrorDistribution rho)
    (fun error => DensityOperator.pureDensity
      (why24CCZMagicBasisKet error) (why24CCZMagicBasisKet_normSq error))
    (by
      intro error _
      exact why24TwirledZErrorDistribution_nonneg rho error)
    (by simpa using why24TwirledZErrorDistribution_sum rho)
noncomputable def why24TwirledZErrorFaultDistribution {count : Nat}
    (preparation : Why24LocalStochasticPreparation (Fin count)
      (why24IdealCCZRegisterDensity count)) : Finset (Fin count) → Real :=
  preparation.faultMass
@[reducible] noncomputable local instance (priority := 2000)
    why24DecoderDirectConstantAlgebra (height : Nat) :
    Algebra F1024 (F1024TowerLevel height) :=
  f1024TowerLevelCoordinateDivisorAlgebra height
noncomputable local instance (priority := 2000)
    why24DecoderDirectConstantScalarTower (height : Nat) :
    IsScalarTower F1024 F1024TowerF1 (F1024TowerLevel height) :=
  f1024TowerLevelCoordinateDivisorRationalScalarTower height
attribute [local instance 2000] QEC.Distillation.Why24OneRoundProtocol.why24DecoderDirectConstantAlgebra QEC.Distillation.Why24OneRoundProtocol.why24DecoderDirectConstantScalarTower
noncomputable def f1024Why24OddDecoderAuxiliaryDivisor (r : Nat) :
    Divisor (GlobalPlace F1024 (F1024TowerLevel (2 * r + 2))) :=
  selectedAuxiliaryDegree (oddGenus r) •
    Finsupp.single (f1024Why24OddEPlace r).place (1 : Int)
theorem f1024Why24OddDecoderAuxiliary_disjoint (r : Nat)
    (site : f1024Why24OddPhysicalSite r) :
    f1024Why24OddDecoderAuxiliaryDivisor r
        (f1024Why24OddPhysicalRationalPlace r site).place = 0 := by
  have hne : (f1024Why24OddEPlace r).place ≠
      (f1024Why24OddPhysicalRationalPlace r site).place := by
    exact (f1024Why24OddCandidatePlace_ne_EPlace r site.1.1).symm
  simp [f1024Why24OddDecoderAuxiliaryDivisor, hne]
noncomputable def f1024Why24OddDecoderComplementDivisor (r : Nat) :
    Divisor (GlobalPlace F1024 (F1024TowerLevel (2 * r + 2))) :=
  f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r -
    f1024Why24OddDecoderAuxiliaryDivisor r
theorem why24DecoderPivotDivisor_apply_physical (r : Nat)
    (site : f1024Why24OddPhysicalSite r) :
    f1024Why24OddPivotDivisor r
        (f1024Why24OddPhysicalRationalPlace r site).place = 0 := by
  simpa only [f1024Why24OddPivotDivisor, evaluationDivisor] using
    zeroCoordinateDivisor_apply_eq_zero_of_not_mem
      (f1024Why24OddPivotRationalPlace r) Finset.univ
      (f1024Why24OddPhysicalRationalPlace r site).place (by
        intro logical _ hplace
        apply site.2
        refine ⟨logical, ?_⟩
        apply f1024Why24OddRetainedRationalPlace_injective r
        exact hplace)
theorem why24DecoderShortenedDivisor_apply_physical (r : Nat)
    (site : f1024Why24OddPhysicalSite r) :
    (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)
        (f1024Why24OddPhysicalRationalPlace r site).place = 0 := by
  change f1024Why24OddADivisor r
        (f1024Why24OddRetainedRationalPlace r site.1).place -
      f1024Why24OddPivotDivisor r
        (f1024Why24OddPhysicalRationalPlace r site).place = 0
  rw [f1024Why24OddADivisor_apply_retained,
    why24DecoderPivotDivisor_apply_physical, sub_zero]
theorem why24DecoderComplementDivisor_apply_physical (r : Nat)
    (site : f1024Why24OddPhysicalSite r) :
    f1024Why24OddDecoderComplementDivisor r
        (f1024Why24OddPhysicalRationalPlace r site).place = 0 := by
  rw [f1024Why24OddDecoderComplementDivisor, Finsupp.sub_apply,
    why24DecoderShortenedDivisor_apply_physical,
    f1024Why24OddDecoderAuxiliary_disjoint]
  simp
noncomputable instance why24DecoderAuxiliary_finiteDimensional
    (r : Nat) :
    FiniteDimensional F1024
      (GlobalPlace.riemannRochSubmodule
        (f1024Why24OddDecoderAuxiliaryDivisor r)) :=
  GlobalPlace.finiteDimensional_riemannRochSubmodule
    (k := F1024) (F := F1024TowerLevel (2 * r + 2)) _
noncomputable instance why24DecoderComplement_finiteDimensional
    (r : Nat) :
    FiniteDimensional F1024
      (GlobalPlace.riemannRochSubmodule
        (f1024Why24OddDecoderComplementDivisor r)) :=
  GlobalPlace.finiteDimensional_riemannRochSubmodule
    (k := F1024) (F := F1024TowerLevel (2 * r + 2)) _
noncomputable instance why24DecoderShortened_finiteDimensional
    (r : Nat) :
    FiniteDimensional F1024
      (GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)) :=
  GlobalPlace.finiteDimensional_riemannRochSubmodule
    (k := F1024) (F := F1024TowerLevel (2 * r + 2)) _
noncomputable def why24DecoderMultiplyIntoShortened (r : Nat)
    (row : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderComplementDivisor r)) :
    GlobalPlace.riemannRochSubmodule
        (f1024Why24OddDecoderAuxiliaryDivisor r) →ₗ[F1024]
      GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r) where
  toFun locator := ⟨(locator : F1024TowerLevel (2 * r + 2)) * row,
    by
      have hproduct := GlobalPlace.mul_mem_riemannRochSubmodule_add
        locator.property row.property
      have hdivisor : f1024Why24OddDecoderAuxiliaryDivisor r +
          f1024Why24OddDecoderComplementDivisor r =
        f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r := by
        rw [f1024Why24OddDecoderComplementDivisor]
        abel
      rwa [hdivisor] at hproduct⟩
  map_add' left right := by
    apply Subtype.ext
    simp only [Submodule.coe_add, add_mul]
  map_smul' scalar locator := by
    apply Subtype.ext
    simpa only [Submodule.coe_smul_of_tower, RingHom.id_apply] using
      (smul_mul_assoc scalar
        (locator : F1024TowerLevel (2 * r + 2))
        (row : F1024TowerLevel (2 * r + 2)))
noncomputable def why24DecoderScaledEvaluationLinearMap (r : Nat) :
    GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r) →ₗ[F1024]
      Word F1024 (f1024Why24OddPhysicalSite r) where
  toFun function site := f1024Why24OddCoordinateWeight r site.1 *
    agEvaluationLinearMap
      (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)
      (f1024Why24OddPhysicalRationalPlace r)
      (why24DecoderShortenedDivisor_apply_physical r) function site
  map_add' left right := by
    funext site
    simp only [map_add, Pi.add_apply]
    ring
  map_smul' scalar function := by
    funext site
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]
    ring
theorem why24DecoderScaledEvaluation_mem_stabilizer (r : Nat)
    (function : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)) :
    why24DecoderScaledEvaluationLinearMap r function ∈
      (f1024Why24OddWeightedMatrix r).stabilizerCode.carrier := by
  rw [f1024Why24OddStabilizerCode_eq_scaledShortenedAGCode]
  exact ⟨function, rfl⟩
noncomputable def why24DecoderScaledEvaluationToStabilizer (r : Nat) :
    GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r) →ₗ[F1024]
      (f1024Why24OddWeightedMatrix r).stabilizerCode.carrier where
  toFun function := ⟨why24DecoderScaledEvaluationLinearMap r function,
    why24DecoderScaledEvaluation_mem_stabilizer r function⟩
  map_add' left right := by
    apply Subtype.ext
    exact map_add (why24DecoderScaledEvaluationLinearMap r) left right
  map_smul' scalar function := by
    apply Subtype.ext
    exact map_smul (why24DecoderScaledEvaluationLinearMap r) scalar function
def why24DecoderRawSyndromePairing (r : Nat) :
    Word F1024 (f1024Why24OddPhysicalSite r) →ₗ[F1024]
      ((f1024Why24OddWeightedMatrix r).stabilizerCode.carrier →ₗ[F1024]
        F1024) where
  toFun error :=
    { toFun := fun codeword => wordPairing error codeword.1
      map_add' := by
        intro left right
        simp only [Submodule.coe_add, map_add]
      map_smul' := by
        intro scalar codeword
        change wordPairing error (scalar • codeword.1) =
          scalar • wordPairing error codeword.1
        exact map_smul (wordPairing error) scalar codeword.1 }
  map_add' left right := by
    ext codeword
    change wordPairing (left + right) codeword.1 =
      wordPairing left codeword.1 + wordPairing right codeword.1
    exact LinearMap.congr_fun (map_add wordPairing left right) codeword.1
  map_smul' scalar error := by
    ext codeword
    change wordPairing (scalar • error) codeword.1 =
      scalar • wordPairing error codeword.1
    exact LinearMap.congr_fun (map_smul wordPairing scalar error) codeword.1
theorem why24DecoderStabilizerDual_le_pairingKernel (r : Nat) :
    (f1024Why24OddWeightedMatrix r).stabilizerCode.dual.carrier ≤
      LinearMap.ker (why24DecoderRawSyndromePairing r) := by
  intro error herror
  rw [LinearMap.mem_ker]
  ext codeword
  exact (f1024Why24OddWeightedMatrix r).stabilizerCode.orthogonal_of_mem_dual
    herror codeword.2
noncomputable def why24DecoderSyndromePairing (r : Nat) :
    f1024Why24OddZSyndrome r →ₗ[F1024]
      ((f1024Why24OddWeightedMatrix r).stabilizerCode.carrier →ₗ[F1024]
        F1024) :=
  (f1024Why24OddWeightedMatrix r).stabilizerCode.dual.carrier.liftQ
    (why24DecoderRawSyndromePairing r)
    (why24DecoderStabilizerDual_le_pairingKernel r)
abbrev f1024Why24OddDecoderEquationIndex (r : Nat) : Type :=
  Fin (Module.finrank F1024
    (GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderComplementDivisor r)))
noncomputable def f1024Why24OddDecoderLinearSystem (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    GlobalPlace.riemannRochSubmodule
        (f1024Why24OddDecoderAuxiliaryDivisor r) →ₗ[F1024]
      (f1024Why24OddDecoderEquationIndex r → F1024) :=
  LinearMap.pi fun equation =>
    (why24DecoderSyndromePairing r syndrome).comp
      ((why24DecoderScaledEvaluationToStabilizer r).comp
        (why24DecoderMultiplyIntoShortened r
          (Module.finBasis F1024
            (GlobalPlace.riemannRochSubmodule
              (f1024Why24OddDecoderComplementDivisor r)) equation)))
noncomputable def why24DecoderAuxiliarySupportEvaluation (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r)) :
    GlobalPlace.riemannRochSubmodule
        (f1024Why24OddDecoderAuxiliaryDivisor r) →ₗ[F1024]
      ({site // site ∈ hammingSupport error} → F1024) where
  toFun locator site :=
    agEvaluationLinearMap
      (f1024Why24OddDecoderAuxiliaryDivisor r)
      (f1024Why24OddPhysicalRationalPlace r)
      (f1024Why24OddDecoderAuxiliary_disjoint r) locator site.1
  map_add' left right := by
    funext site
    simp only [map_add, Pi.add_apply]
  map_smul' scalar locator := by
    funext site
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]
@[simp]
theorem why24DecoderSyndromePairing_mk (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r))
    (codeword : (f1024Why24OddWeightedMatrix r).stabilizerCode.carrier) :
    why24DecoderSyndromePairing r (f1024Why24OddZSyndromeMap r error)
        codeword = wordPairing error codeword.1 := by
  change (why24DecoderRawSyndromePairing r error) codeword =
    wordPairing error codeword.1
  rfl
noncomputable def why24DecoderLocator (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderAuxiliaryDivisor r) := by
  letI : Module.Free F1024
      (LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome)) :=
    Module.Free.of_divisionRing F1024
      (LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome))
  exact if hdimension : 0 < Module.finrank F1024
      (LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome)) then
    (Module.finBasis F1024
      (LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome))
      ⟨0, hdimension⟩ :
        LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome)).1
  else 0
noncomputable def why24DecoderComplementAGCode (r : Nat) :
    LinearCode F1024 (f1024Why24OddPhysicalSite r) :=
  agEvaluationCode
    (f1024Why24OddDecoderComplementDivisor r)
    (f1024Why24OddPhysicalRationalPlace r)
    (why24DecoderComplementDivisor_apply_physical r)
noncomputable def why24DecoderMultiplyLocatorIntoShortened (r : Nat)
    (locator : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderAuxiliaryDivisor r)) :
    GlobalPlace.riemannRochSubmodule
        (f1024Why24OddDecoderComplementDivisor r) →ₗ[F1024]
      GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r) where
  toFun row := why24DecoderMultiplyIntoShortened r row locator
  map_add' left right := by
    apply Subtype.ext
    change (locator : F1024TowerLevel (2 * r + 2)) *
        ((left : F1024TowerLevel (2 * r + 2)) + right) =
      (locator : F1024TowerLevel (2 * r + 2)) * left +
        (locator : F1024TowerLevel (2 * r + 2)) * right
    rw [mul_add]
  map_smul' scalar row := by
    apply Subtype.ext
    change (locator : F1024TowerLevel (2 * r + 2)) *
        (algebraMap F1024 (F1024TowerLevel (2 * r + 2)) scalar * row) =
      algebraMap F1024 (F1024TowerLevel (2 * r + 2)) scalar *
        ((locator : F1024TowerLevel (2 * r + 2)) * row)
    ring
noncomputable def why24DecoderLocatorEquationFunctional (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r)
    (locator : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderAuxiliaryDivisor r)) :
    GlobalPlace.riemannRochSubmodule
        (f1024Why24OddDecoderComplementDivisor r) →ₗ[F1024] F1024 :=
  (why24DecoderSyndromePairing r syndrome).comp
    ((why24DecoderScaledEvaluationToStabilizer r).comp
      (why24DecoderMultiplyLocatorIntoShortened r locator))
noncomputable def why24DecoderLocatorProductWord (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r))
    (locator : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderAuxiliaryDivisor r)) :
    Word F1024 (f1024Why24OddPhysicalSite r) := fun site =>
  error site *
    (f1024Why24OddCoordinateWeight r site.1 *
      agEvaluationLinearMap
        (f1024Why24OddDecoderAuxiliaryDivisor r)
        (f1024Why24OddPhysicalRationalPlace r)
        (f1024Why24OddDecoderAuxiliary_disjoint r) locator site)
noncomputable def why24DecoderLocatorZeroSet (r : Nat)
    (locator : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderAuxiliaryDivisor r)) :
    Finset (f1024Why24OddPhysicalSite r) :=
  Finset.univ.filter fun site =>
    agEvaluationLinearMap
      (f1024Why24OddDecoderAuxiliaryDivisor r)
      (f1024Why24OddPhysicalRationalPlace r)
      (f1024Why24OddDecoderAuxiliary_disjoint r) locator site = 0
noncomputable def why24DecoderLocatorProductLinearMap (r : Nat)
    (locator : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderAuxiliaryDivisor r)) :
    Word F1024 (f1024Why24OddPhysicalSite r) →ₗ[F1024]
      Word F1024 (f1024Why24OddPhysicalSite r) where
  toFun error := why24DecoderLocatorProductWord r error locator
  map_add' left right := by
    funext site
    simp only [why24DecoderLocatorProductWord, Pi.add_apply]
    ring
  map_smul' scalar error := by
    funext site
    simp only [why24DecoderLocatorProductWord, Pi.smul_apply,
      RingHom.id_apply, smul_eq_mul]
    ring
noncomputable def why24DecoderRecoverySyndromeMap (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    LinearMap.ker (why24DecoderLocatorProductLinearMap r
        (why24DecoderLocator r syndrome)) →ₗ[F1024]
      f1024Why24OddZSyndrome r :=
  ((f1024Why24OddWeightedMatrix r).stabilizerCode.dual.carrier.mkQ).comp
    (LinearMap.ker (why24DecoderLocatorProductLinearMap r
      (why24DecoderLocator r syndrome))).subtype
noncomputable def why24DecoderRecoveryCoordinates (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    LinearMap.ker (why24DecoderLocatorProductLinearMap r
        (why24DecoderLocator r syndrome)) →ₗ[F1024]
      (Fin (Module.finrank F1024
        (LinearMap.range (why24DecoderRecoverySyndromeMap r syndrome))) →
          F1024) := by
  let recovery := why24DecoderRecoverySyndromeMap r syndrome
  letI : Module.Free F1024 (LinearMap.range recovery) :=
    Module.Free.of_divisionRing F1024 (LinearMap.range recovery)
  exact (Module.finBasis F1024 (LinearMap.range recovery)).equivFun.toLinearMap.comp
    recovery.rangeRestrict
theorem why24DecoderRecoveryCoordinates_surjective (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    Function.Surjective (why24DecoderRecoveryCoordinates r syndrome) := by
  let recovery := why24DecoderRecoverySyndromeMap r syndrome
  letI : Module.Free F1024 (LinearMap.range recovery) :=
    Module.Free.of_divisionRing F1024 (LinearMap.range recovery)
  exact (Module.finBasis F1024
    (LinearMap.range recovery)).equivFun.surjective.comp
      recovery.surjective_rangeRestrict
noncomputable def why24DecoderRecoveryRangeSection (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    LinearMap.range (why24DecoderRecoverySyndromeMap r syndrome) →ₗ[F1024]
      LinearMap.ker (why24DecoderLocatorProductLinearMap r
        (why24DecoderLocator r syndrome)) := by
  let recovery := why24DecoderRecoverySyndromeMap r syndrome
  letI : Module.Free F1024 (LinearMap.range recovery) :=
    Module.Free.of_divisionRing F1024 (LinearMap.range recovery)
  exact (LinearMap.splittingOfFunOnFintypeSurjective
      (why24DecoderRecoveryCoordinates r syndrome)
      (why24DecoderRecoveryCoordinates_surjective r syndrome)).comp
    (Module.finBasis F1024 (LinearMap.range recovery)).equivFun.toLinearMap
noncomputable def f1024Why24OddAGDualDecoder (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    Word F1024 (f1024Why24OddPhysicalSite r) := by
  classical
  exact if hmem : syndrome ∈
      LinearMap.range (why24DecoderRecoverySyndromeMap r syndrome) then
    (why24DecoderRecoveryRangeSection r syndrome ⟨syndrome, hmem⟩).1
  else 0
def f1024Why24OddAGDualDecoderArithmeticCost (r : Nat) : Nat :=
  (f1024Why24OddLength r +
    Module.finrank F1024
      (GlobalPlace.riemannRochSubmodule
        (f1024Why24OddDecoderAuxiliaryDivisor r)) +
    Module.finrank F1024
      (GlobalPlace.riemannRochSubmodule
        (f1024Why24OddDecoderComplementDivisor r))) ^ 3
theorem why24LinearMap_comp_rankOne_comp_adjoint
    {H K : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (L : H →ₗ[Complex] K) (x y : H) :
    L.comp ((InnerProductSpace.rankOne Complex x y).toLinearMap.comp
      (LinearMap.adjoint L)) =
      (InnerProductSpace.rankOne Complex (L x) (L y)).toLinearMap := by
  ext z
  simp [LinearMap.comp_apply, InnerProductSpace.rankOne_apply,
    LinearMap.adjoint_inner_right]
theorem why24AppendixCircuit_isUnitary :
    Why24IsUnitary why24AppendixCircuit := by
  intro left right
  have hport := (why24QuditQubitUnitary_conj_isUnitary_iff why24UOneSeven).2
    (why24U_isUnitary (1 : F1024) 7) left right
  simp only [why24AppendixCircuit_apply_eq_why24QubitUOneSeven] at hport ⊢
  exact hport
noncomputable def why24AppendixCircuitInstrument :
    FiniteInstrument PUnit PUnit Why24QubitSpace Why24QubitSpace where
  kraus :=
    { operator := fun _ => why24AppendixCircuit }
  observe := id
theorem why24AppendixCircuitInstrument_complete :
    why24AppendixCircuitInstrument.kraus.Complete := by
  rw [FiniteKrausFamily.Complete]
  simp only [Fintype.sum_unique, why24AppendixCircuitInstrument]
  apply LinearMap.ext
  intro x
  apply ext_inner_right Complex
  intro y
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
  exact why24AppendixCircuit_isUnitary x y
theorem why24QubitPlusState_normSq :
    ‖why24QubitPlusState‖ ^ 2 = 1 := by
  rw [why24QubitPlusState_norm]
  norm_num
theorem why24UOneSevenQubitResource_normSq :
    ‖why24UOneSevenQubitResource‖ ^ 2 = 1 := by
  rw [why24UOneSevenQubitResource_norm]
  norm_num
noncomputable def why24QubitPlusStateDensity :
    DensityOperator Why24QubitSpace :=
  DensityOperator.pureDensity why24QubitPlusState
    why24QubitPlusState_normSq
noncomputable def why24UOneSevenQubitResourceDensity :
    DensityOperator Why24QubitSpace :=
  DensityOperator.pureDensity why24UOneSevenQubitResource
    why24UOneSevenQubitResource_normSq
def why24BinaryRegisterLabelEquiv (Site : Type)
    [Fintype Site] :
    PrimeQuditRegisterLabel 2 Site ≃ Qubit.Bitstring Site where
  toFun label site := (ZMod.finEquiv 2).symm (label site)
  invFun bits site := ZMod.finEquiv 2 (bits site)
  left_inv label := by
    funext site
    exact (ZMod.finEquiv 2).apply_symm_apply (label site)
  right_inv bits := by
    funext site
    exact (ZMod.finEquiv 2).symm_apply_apply (bits site)
noncomputable def why24BinaryRegisterTransport (Site : Type)
    [Fintype Site] [DecidableEq Site] :
    UnitaryTransport (PrimeQuditRegister 2 Site) (Qubit.QubitRegister Site) := by
  let sourceBasis := EuclideanSpace.basisFun
    (PrimeQuditRegisterLabel 2 Site) Complex
  let targetBasis := EuclideanSpace.basisFun (Qubit.Bitstring Site) Complex
  let U := sourceBasis.equiv targetBasis (why24BinaryRegisterLabelEquiv Site)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }
theorem why24CubicGateTriples_length :
    QEC.Coding.Why24AppendixANF.cubicGateTriples.length = 70 := by
  decide
def why24AppendixCCZGateAt (gate : Fin 70) :
    Fin 10 × Fin 10 × Fin 10 :=
  QEC.Coding.Why24AppendixANF.cubicGateTriples.get
    ⟨gate.1, by simpa [why24CubicGateTriples_length] using gate.2⟩
def why24AppendixCCZErrorContribution (gate : Fin 70)
    (error : Qubit.Bitstring (Fin 3)) : PrimeQuditRegisterLabel 2 (Fin 10) :=
  fun site =>
    (if (why24AppendixCCZGateAt gate).1 = site then
        ZMod.finEquiv 2 (error 0) else 0) +
      (if (why24AppendixCCZGateAt gate).2.1 = site then
        ZMod.finEquiv 2 (error 1) else 0) +
      (if (why24AppendixCCZGateAt gate).2.2 = site then
        ZMod.finEquiv 2 (error 2) else 0)
def why24CCZToUOneSevenErrorWord
    (error : Fin 70 -> Qubit.Bitstring (Fin 3)) : Qubit.Bitstring (Fin 10) :=
  (why24BinaryRegisterLabelEquiv (Fin 10))
    (∑ gate : Fin 70,
      why24AppendixCCZErrorContribution gate (error gate))
noncomputable def why24CCZToUOneSevenErrorKet
    (error : Fin 70 -> Qubit.Bitstring (Fin 3)) : Why24QubitSpace :=
  why24BinaryRegisterTransport (Fin 10)
    (zWordTransport 2
      ((why24BinaryRegisterLabelEquiv (Fin 10)).symm
        (why24CCZToUOneSevenErrorWord error))
      ((why24BinaryRegisterTransport (Fin 10)).symm
        why24UOneSevenQubitResource))
theorem why24CCZToUOneSevenErrorKet_norm
    (error : Fin 70 -> Qubit.Bitstring (Fin 3)) :
    ‖why24CCZToUOneSevenErrorKet error‖ = 1 := by
  rw [why24CCZToUOneSevenErrorKet]
  calc
    ‖why24BinaryRegisterTransport (Fin 10)
        (zWordTransport 2
          ((why24BinaryRegisterLabelEquiv (Fin 10)).symm
            (why24CCZToUOneSevenErrorWord error))
          ((why24BinaryRegisterTransport (Fin 10)).symm
            why24UOneSevenQubitResource))‖ =
        ‖zWordTransport 2
          ((why24BinaryRegisterLabelEquiv (Fin 10)).symm
            (why24CCZToUOneSevenErrorWord error))
          ((why24BinaryRegisterTransport (Fin 10)).symm
            why24UOneSevenQubitResource)‖ :=
      (why24BinaryRegisterTransport (Fin 10)).toLinearIsometryEquiv.norm_map _
    _ = ‖(why24BinaryRegisterTransport (Fin 10)).symm
          why24UOneSevenQubitResource‖ :=
      (zWordTransport 2 _).toLinearIsometryEquiv.norm_map _
    _ = ‖why24UOneSevenQubitResource‖ :=
      (why24BinaryRegisterTransport
        (Fin 10)).symm.toLinearIsometryEquiv.norm_map _
    _ = 1 := why24UOneSevenQubitResource_norm
theorem why24CCZToUOneSevenErrorKet_normSq
    (error : Fin 70 -> Qubit.Bitstring (Fin 3)) :
    ‖why24CCZToUOneSevenErrorKet error‖ ^ 2 = 1 := by
  rw [why24CCZToUOneSevenErrorKet_norm]
  norm_num
noncomputable def why24CCZToUOneSevenKraus :
    FiniteKrausFamily (Fin 70 -> Qubit.Bitstring (Fin 3))
      (Why24CCZRegister (Fin 70)) Why24QubitSpace where
  operator error :=
    (InnerProductSpace.rankOne Complex
      (why24CCZToUOneSevenErrorKet error)
      (why24JointCCZMagicBasisKet 70 error)).toLinearMap
theorem why24CCZToUOneSevenKraus_adjoint_comp
    (error : Fin 70 -> Qubit.Bitstring (Fin 3)) :
    (LinearMap.adjoint (why24CCZToUOneSevenKraus.operator error)).comp
        (why24CCZToUOneSevenKraus.operator error) =
      (InnerProductSpace.rankOne Complex
        (why24JointCCZMagicBasisKet 70 error)
        (why24JointCCZMagicBasisKet 70 error)).toLinearMap := by
  have hadjoint : LinearMap.adjoint
      ((InnerProductSpace.rankOne Complex
        (why24CCZToUOneSevenErrorKet error)
        (why24JointCCZMagicBasisKet 70 error)).toLinearMap) =
      (InnerProductSpace.rankOne Complex
        (why24JointCCZMagicBasisKet 70 error)
        (why24CCZToUOneSevenErrorKet error)).toLinearMap := by
    rw [LinearMap.adjoint_eq_toCLM_adjoint]
    change ((InnerProductSpace.rankOne Complex
      (why24CCZToUOneSevenErrorKet error)
      (why24JointCCZMagicBasisKet 70 error)).adjoint).toLinearMap = _
    rw [InnerProductSpace.adjoint_rankOne]
  ext psi
  simp only [why24CCZToUOneSevenKraus]
  rw [hadjoint]
  have hnormSq : (↑‖why24CCZToUOneSevenErrorKet error‖ : Complex) ^ 2 = 1 := by
    norm_cast
    exact why24CCZToUOneSevenErrorKet_normSq error
  simp [LinearMap.comp_apply, hnormSq]
theorem why24CCZToUOneSevenInstrument_complete :
    why24CCZToUOneSevenKraus.Complete := by
  rw [FiniteKrausFamily.Complete]
  simp_rw [why24CCZToUOneSevenKraus_adjoint_comp]
  have hport := congrArg ContinuousLinearMap.toLinearMap
    (OrthonormalBasis.sum_rankOne_eq_id (why24JointCCZMagicBasis 70))
  simp [why24JointCCZMagicBasisKet] at hport ⊢
  exact hport
noncomputable def why24CCZToUOneSevenInstrument :
    FiniteInstrument
      (Fin 70 -> Qubit.Bitstring (Fin 3))
      (Fin 70 -> Qubit.Bitstring (Fin 3))
      (Why24CCZRegister (Fin 70)) Why24QubitSpace where
  kraus := why24CCZToUOneSevenKraus
  observe := id
theorem why24CCZToUOneSevenErrorWord_zero :
    why24CCZToUOneSevenErrorWord
        (0 : Fin 70 -> Qubit.Bitstring (Fin 3)) = 0 := by
  funext site
  simp [why24CCZToUOneSevenErrorWord,
    why24BinaryRegisterLabelEquiv,
    why24AppendixCCZErrorContribution]
def why24AppendixReverseSplit
    (bits : Qubit.Bitstring (Fin 10)) :
    Why24AppendixReverseOutcome × Qubit.Bitstring (Fin 3) :=
  (fun site => bits ⟨site.1 + 3, by omega⟩,
    fun site => bits ⟨site.1, by omega⟩)
theorem why24AppendixReverseRecombine_split
    (bits : Qubit.Bitstring (Fin 10)) :
    why24AppendixReverseRecombine
        (why24AppendixReverseSplit bits).2
        (why24AppendixReverseSplit bits).1 = bits := by
  funext site
  fin_cases site <;> rfl
theorem why24AppendixReverseSplit_recombine
    (labels : Why24AppendixReverseOutcome × Qubit.Bitstring (Fin 3)) :
    why24AppendixReverseSplit
        (why24AppendixReverseRecombine labels.2 labels.1) = labels := by
  apply Prod.ext
  · funext site
    fin_cases site <;> rfl
  · funext site
    fin_cases site <;> rfl
def why24AppendixReverseLabelEquiv :
    Qubit.Bitstring (Fin 10) ≃
      Why24AppendixReverseOutcome × Qubit.Bitstring (Fin 3) where
  toFun := why24AppendixReverseSplit
  invFun labels := why24AppendixReverseRecombine labels.2 labels.1
  left_inv := why24AppendixReverseRecombine_split
  right_inv := why24AppendixReverseSplit_recombine
noncomputable def why24AppendixReverseKraus
    (outcome : Why24AppendixReverseOutcome) :
    Why24QubitSpace →ₗ[Complex] Why24CCZSpace where
  toFun psi := WithLp.toLp 2 fun retained =>
    PauliSymplectic.binaryPhaseScalar
        (why24AppendixReverseCorrectionPhase outcome retained) *
      psi (why24AppendixReverseRecombine retained outcome)
  map_add' left right := by
    ext retained
    simp [mul_add]
  map_smul' scalar psi := by
    ext retained
    simp [smul_eq_mul, mul_left_comm]
@[simp] theorem why24AppendixReverseKraus_apply
    (outcome : Why24AppendixReverseOutcome) (psi : Why24QubitSpace)
    (retained : Qubit.Bitstring (Fin 3)) :
    why24AppendixReverseKraus outcome psi retained =
      PauliSymplectic.binaryPhaseScalar
          (why24AppendixReverseCorrectionPhase outcome retained) *
        psi (why24AppendixReverseRecombine retained outcome) :=
  rfl
theorem why24AppendixReverseKraus_inner
    (outcome : Why24AppendixReverseOutcome)
    (left right : Why24QubitSpace) :
    inner Complex (why24AppendixReverseKraus outcome left)
        (why24AppendixReverseKraus outcome right) =
      ∑ retained : Qubit.Bitstring (Fin 3),
        inner Complex
          (left (why24AppendixReverseRecombine retained outcome))
          (right (why24AppendixReverseRecombine retained outcome)) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro retained _
  simp only [why24AppendixReverseKraus_apply, RCLike.inner_apply, map_mul]
  have hstar :
      starRingEnd Complex
          (PauliSymplectic.binaryPhaseScalar
            (why24AppendixReverseCorrectionPhase outcome retained)) =
        PauliSymplectic.binaryPhaseScalar
          (why24AppendixReverseCorrectionPhase outcome retained) :=
    PauliSymplectic.binaryPhaseScalar_star _
  rw [hstar]
  calc
    (PauliSymplectic.binaryPhaseScalar
          (why24AppendixReverseCorrectionPhase outcome retained) *
        right (why24AppendixReverseRecombine retained outcome)) *
      (PauliSymplectic.binaryPhaseScalar
          (why24AppendixReverseCorrectionPhase outcome retained) *
        star (left (why24AppendixReverseRecombine retained outcome))) =
        (PauliSymplectic.binaryPhaseScalar
            (why24AppendixReverseCorrectionPhase outcome retained) *
          PauliSymplectic.binaryPhaseScalar
            (why24AppendixReverseCorrectionPhase outcome retained)) *
          (right (why24AppendixReverseRecombine retained outcome) *
            star (left
              (why24AppendixReverseRecombine retained outcome))) := by ring
    _ = right (why24AppendixReverseRecombine retained outcome) *
        star (left (why24AppendixReverseRecombine retained outcome)) := by
      rw [why24BinaryPhaseScalar_mul_self, one_mul]
noncomputable def why24UOneSevenToCCZInstrument :
    FiniteInstrument Why24AppendixReverseOutcome
      Why24AppendixReverseOutcome Why24QubitSpace Why24CCZSpace where
  kraus :=
    { operator := why24AppendixReverseKraus }
  observe := id
theorem why24AppendixReverseKraus_resource
    (outcome : Why24AppendixReverseOutcome) :
    why24AppendixReverseKraus outcome why24UOneSevenQubitResource =
      why24AppendixReverseCorrection outcome
        (why24AppendixReverseRawBranch outcome) := by
  rfl
theorem why24AppendixReverseCorrection_normSq
    (outcome : Why24AppendixReverseOutcome) :
    ‖why24AppendixReverseCorrection outcome
        (why24AppendixReverseRawBranch outcome)‖ ^ 2 =
      why24AppendixReverseBornWeight outcome := by
  have hinner :
      inner Complex
          (why24AppendixReverseCorrection outcome
            (why24AppendixReverseRawBranch outcome))
          (why24AppendixReverseCorrection outcome
            (why24AppendixReverseRawBranch outcome)) =
        inner Complex (why24AppendixReverseRawBranch outcome)
          (why24AppendixReverseRawBranch outcome) := by
    rw [← why24AppendixReverseKraus_resource,
      why24AppendixReverseKraus_inner, PiLp.inner_apply]
    rfl
  calc
    ‖why24AppendixReverseCorrection outcome
        (why24AppendixReverseRawBranch outcome)‖ ^ 2 =
        Complex.re (inner Complex
          (why24AppendixReverseCorrection outcome
            (why24AppendixReverseRawBranch outcome))
          (why24AppendixReverseCorrection outcome
            (why24AppendixReverseRawBranch outcome))) :=
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex)
        (why24AppendixReverseCorrection outcome
          (why24AppendixReverseRawBranch outcome))
    _ = Complex.re (inner Complex
        (why24AppendixReverseRawBranch outcome)
        (why24AppendixReverseRawBranch outcome)) := by rw [hinner]
    _ = ‖why24AppendixReverseRawBranch outcome‖ ^ 2 :=
      (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex)
        (why24AppendixReverseRawBranch outcome)).symm
    _ = why24AppendixReverseBornWeight outcome := rfl
theorem why24UOneSevenToCCZ_branchOperator_ideal
    (outcome : Why24AppendixReverseOutcome) :
    why24UOneSevenToCCZInstrument.branchOperator outcome
        why24UOneSevenQubitResourceDensity.toOperator =
      (InnerProductSpace.rankOne Complex
        (why24AppendixReverseCorrection outcome
          (why24AppendixReverseRawBranch outcome))
        (why24AppendixReverseCorrection outcome
          (why24AppendixReverseRawBranch outcome))).toLinearMap := by
  classical
  rw [FiniteInstrument.branchOperator_apply]
  rw [Finset.sum_eq_single outcome]
  · rw [if_pos (show why24UOneSevenToCCZInstrument.observe outcome = outcome from rfl)]
    change why24AppendixReverseKraus outcome ∘ₗ
      why24UOneSevenQubitResourceDensity.toOperator ∘ₗ
      (why24AppendixReverseKraus outcome).adjoint = _
    rw [why24UOneSevenQubitResourceDensity,
      DensityOperator.pureDensity_toOperator,
      why24LinearMap_comp_rankOne_comp_adjoint,
      why24AppendixReverseKraus_resource]
  · intro other _ hne
    exact if_neg (show why24UOneSevenToCCZInstrument.observe other ≠ outcome from hne)
  · intro hnot
    exact (hnot (Finset.mem_univ outcome)).elim
theorem why24UOneSevenToCCZ_bornWeight_ideal
    (outcome : Why24AppendixReverseOutcome) :
    why24UOneSevenToCCZInstrument.bornWeight outcome
        why24UOneSevenQubitResourceDensity = (1 / 128 : Real) := by
  rw [FiniteInstrument.bornWeight,
    why24UOneSevenToCCZ_branchOperator_ideal,
    InnerProductSpace.trace_rankOne]
  calc
    Complex.re (inner Complex
        (why24AppendixReverseCorrection outcome
          (why24AppendixReverseRawBranch outcome))
        (why24AppendixReverseCorrection outcome
          (why24AppendixReverseRawBranch outcome))) =
        ‖why24AppendixReverseCorrection outcome
          (why24AppendixReverseRawBranch outcome)‖ ^ 2 :=
      (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex)
        (why24AppendixReverseCorrection outcome
          (why24AppendixReverseRawBranch outcome))).symm
    _ = why24AppendixReverseBornWeight outcome :=
      why24AppendixReverseCorrection_normSq outcome
    _ = (1 / 128 : Real) :=
      why24AppendixReverseBornWeight_eq_source outcome
def why24CCZToUOneSevenInputCount : Nat :=
  why24AppendixGateCounts.2.2
theorem why24CCZToUOneSeven_inputCount_eq_seventy :
    why24CCZToUOneSevenInputCount = 70 := by
  rw [why24CCZToUOneSevenInputCount,
    why24AppendixGateCounts_eq_source]
def why24UOneSevenToCCZOutputCount : Nat := 1
noncomputable def why24OneRoundBinaryLabelEquiv {Site : Type}
    [Fintype Site] :
    Why24Word Site ≃ PrimeQuditRegisterLabel 2 (Site × Fin 10) :=
  (Equiv.piCongrRight
      (fun _ : Site => f1024SelectedCoordinates.toEquiv)).trans
    (Equiv.curry Site (Fin 10) (ZMod 2)).symm
@[simp]
theorem why24OneRoundBinaryLabelEquiv_apply {Site : Type}
    [Fintype Site] (word : Why24Word Site) (site : Site) (bit : Fin 10) :
    why24OneRoundBinaryLabelEquiv word (site, bit) =
      f1024SelectedCoordinates (word site) bit :=
  rfl
noncomputable def why24OneRoundBinaryBasisIsometry {Site : Type}
    [Fintype Site] :
    ComputationalBasisRegister F1024 Site ≃ₗᵢ[Complex]
      PrimeQuditRegister 2 (Site × Fin 10) :=
  LinearIsometryEquiv.piLpCongrLeft 2 Complex Complex
    (why24OneRoundBinaryLabelEquiv (Site := Site))
noncomputable def why24OneRoundBinaryTransport {Site : Type}
    [Fintype Site] :
    UnitaryTransport (ComputationalBasisRegister F1024 Site)
      (PrimeQuditRegister 2 (Site × Fin 10)) where
  toLinearEquiv := why24OneRoundBinaryBasisIsometry.toLinearEquiv
  map_inner := why24OneRoundBinaryBasisIsometry.toLinearIsometry.inner_map_map
@[simp] theorem why24OneRoundBinaryTransport_symm_apply {Site : Type}
    [Fintype Site] (psi : PrimeQuditRegister 2 (Site × Fin 10))
    (word : Why24Word Site) :
    (why24OneRoundBinaryTransport (Site := Site)).symm psi word =
      psi (why24OneRoundBinaryLabelEquiv word) := by
  change (why24OneRoundBinaryBasisIsometry
    (Site := Site)).symm psi word = _
  rw [why24OneRoundBinaryBasisIsometry,
    LinearIsometryEquiv.piLpCongrLeft_symm,
    LinearIsometryEquiv.piLpCongrLeft_apply]
  rfl
noncomputable def why24OneRoundCharacterKet {Site : Type}
    [Fintype Site] (word : Why24Word Site) :
    ComputationalBasisRegister F1024 Site :=
  (why24OneRoundBinaryTransport (Site := Site)).symm
    (characterKet 2 (why24OneRoundBinaryLabelEquiv word))
@[simp]
theorem why24OneRoundCharacterKet_apply {Site : Type}
    [Fintype Site] (word label : Why24Word Site) :
    why24OneRoundCharacterKet word label =
      (Real.sqrt (2 : Real) : Complex)⁻¹ ^ Fintype.card (Site × Fin 10) *
        phase 2 (registerPairing 2
          (why24OneRoundBinaryLabelEquiv word)
          (why24OneRoundBinaryLabelEquiv label)) := by
  rw [why24OneRoundCharacterKet,
    why24OneRoundBinaryTransport_symm_apply, characterKet_apply]
  norm_num
def why24OneRoundStabilizerAddEquiv
    {Logical Stabilizer Site : Type} [Fintype Logical] [DecidableEq Logical]
    [Fintype Stabilizer] [DecidableEq Stabilizer]
    [Fintype Site] [DecidableEq Site]
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (shift : R.StabilizerCarrier) :
    R.StabilizerCarrier ≃ R.StabilizerCarrier where
  toFun word := ⟨word.1 + shift.1,
    R.stabilizerCode.carrier.add_mem word.property shift.property⟩
  invFun word := ⟨word.1 - shift.1,
    R.stabilizerCode.carrier.sub_mem word.property shift.property⟩
  left_inv word := by
    apply Subtype.ext
    exact add_sub_cancel_right word.1 shift.1
  right_inv word := by
    apply Subtype.ext
    exact sub_add_cancel word.1 shift.1
@[simp]
theorem why24OneRoundZSyndromeMap_add (r : Nat)
    (left right : Why24Word (f1024Why24OddPhysicalSite r)) :
    f1024Why24OddZSyndromeMap r (left + right) =
      f1024Why24OddZSyndromeMap r left +
        f1024Why24OddZSyndromeMap r right :=
  rfl
theorem why24OneRoundCharacterKet_inner {Site : Type}
    [Fintype Site] (left right : Why24Word Site) :
    inner Complex (why24OneRoundCharacterKet left)
        (why24OneRoundCharacterKet right) =
      if left = right then 1 else 0 := by
  rw [why24OneRoundCharacterKet, why24OneRoundCharacterKet,
    (why24OneRoundBinaryTransport (Site := Site)).symm.map_inner,
    characterKet_inner]
  simp only [Equiv.apply_eq_iff_eq]
theorem why24OneRoundCharacterRankOne_transport {Site : Type}
    [Fintype Site] (word : Why24Word Site)
    (psi : ComputationalBasisRegister F1024 Site) :
    why24OneRoundBinaryTransport
        ((InnerProductSpace.rankOne Complex
          (why24OneRoundCharacterKet word)
          (why24OneRoundCharacterKet word)).toLinearMap psi) =
      (InnerProductSpace.rankOne Complex
        (characterKet 2 (why24OneRoundBinaryLabelEquiv word))
        (characterKet 2 (why24OneRoundBinaryLabelEquiv word))).toLinearMap
          (why24OneRoundBinaryTransport psi) := by
  simp only [InnerProductSpace.toLinearMap_rankOne,
    LinearMap.smulRight_apply, innerₛₗ_apply_apply, map_smul,
    why24OneRoundCharacterKet]
  rw [← (why24OneRoundBinaryTransport (Site := Site)).map_inner]
  simp
theorem why24OneRound_sum_characterRankOne_eq_one {Site : Type}
    [Fintype Site] :
    (∑ word : Why24Word Site,
      (InnerProductSpace.rankOne Complex
        (why24OneRoundCharacterKet word)
        (why24OneRoundCharacterKet word)).toLinearMap) = 1 := by
  apply LinearMap.ext
  intro psi
  apply (why24OneRoundBinaryTransport
    (Site := Site)).toLinearEquiv.injective
  calc
    why24OneRoundBinaryTransport
        ((∑ word : Why24Word Site,
          (InnerProductSpace.rankOne Complex
            (why24OneRoundCharacterKet word)
            (why24OneRoundCharacterKet word)).toLinearMap) psi) =
        ∑ word : Why24Word Site,
          (InnerProductSpace.rankOne Complex
            (characterKet 2 (why24OneRoundBinaryLabelEquiv word))
            (characterKet 2 (why24OneRoundBinaryLabelEquiv word))).toLinearMap
              (why24OneRoundBinaryTransport psi) := by
      simp only [LinearMap.sum_apply, map_sum,
        why24OneRoundCharacterRankOne_transport]
    _ = ∑ word : PrimeQuditRegisterLabel 2 (Site × Fin 10),
        (InnerProductSpace.rankOne Complex
          (characterKet 2 word) (characterKet 2 word)).toLinearMap
            (why24OneRoundBinaryTransport psi) := by
      apply Fintype.sum_equiv
        (why24OneRoundBinaryLabelEquiv (Site := Site))
      intro word
      rfl
    _ = why24OneRoundBinaryTransport psi := by
      rw [← LinearMap.sum_apply, sum_characterKet_rankOne_eq_one]
      rfl
    _ = why24OneRoundBinaryTransport ((1 : Operator
        (ComputationalBasisRegister F1024 Site)) psi) := by rfl
theorem why24OneRoundCharacterRankOne_mul {Site : Type}
    [Fintype Site] (left right : Why24Word Site) :
    (InnerProductSpace.rankOne Complex
      (why24OneRoundCharacterKet left)
      (why24OneRoundCharacterKet left)).toLinearMap *
        (InnerProductSpace.rankOne Complex
          (why24OneRoundCharacterKet right)
          (why24OneRoundCharacterKet right)).toLinearMap =
      if left = right then
        (InnerProductSpace.rankOne Complex
          (why24OneRoundCharacterKet right)
          (why24OneRoundCharacterKet right)).toLinearMap
      else 0 := by
  classical
  ext psi
  simp only [Module.End.mul_apply, InnerProductSpace.toLinearMap_rankOne,
    LinearMap.smulRight_apply, innerₛₗ_apply_apply]
  rw [inner_smul_right]
  by_cases hsame : left = right
  · subst left
    rw [why24OneRoundCharacterKet_inner]
    simp
  · rw [why24OneRoundCharacterKet_inner]
    simp [hsame]
noncomputable def why24OneRoundSyndromeProjector (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    Operator (ComputationalBasisRegister F1024
      (f1024Why24OddPhysicalSite r)) :=
  ∑ word : Why24Word (f1024Why24OddPhysicalSite r),
    if f1024Why24OddZSyndromeMap r word = syndrome then
      (InnerProductSpace.rankOne Complex
        (why24OneRoundCharacterKet word)
        (why24OneRoundCharacterKet word)).toLinearMap
    else 0
theorem why24OneRound_sum_syndromeProjector_eq_one (r : Nat) :
    ∑ syndrome : f1024Why24OddZSyndrome r,
      why24OneRoundSyndromeProjector r syndrome = 1 := by
  classical
  unfold why24OneRoundSyndromeProjector
  rw [Finset.sum_comm]
  simp_rw [Fintype.sum_ite_eq]
  exact why24OneRound_sum_characterRankOne_eq_one
theorem why24OneRoundSyndromeProjector_adjoint (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    LinearMap.adjoint (why24OneRoundSyndromeProjector r syndrome) =
      why24OneRoundSyndromeProjector r syndrome := by
  classical
  unfold why24OneRoundSyndromeProjector
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro word _
  by_cases hsector : f1024Why24OddZSyndromeMap r word = syndrome
  · rw [if_pos hsector, LinearMap.adjoint_eq_toCLM_adjoint]
    change ((InnerProductSpace.rankOne Complex
      (why24OneRoundCharacterKet word)
      (why24OneRoundCharacterKet word)).adjoint).toLinearMap = _
    rw [InnerProductSpace.adjoint_rankOne]
  · simp [hsector]
theorem why24OneRoundSyndromeProjector_idempotent (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    (why24OneRoundSyndromeProjector r syndrome).comp
        (why24OneRoundSyndromeProjector r syndrome) =
      why24OneRoundSyndromeProjector r syndrome := by
  classical
  rw [← Module.End.mul_eq_comp]
  unfold why24OneRoundSyndromeProjector
  rw [Fintype.sum_mul_sum]
  simp_rw [ite_mul, mul_ite, zero_mul, mul_zero,
    why24OneRoundCharacterRankOne_mul]
  apply Finset.sum_congr rfl
  intro left _
  by_cases hsector : f1024Why24OddZSyndromeMap r left = syndrome
  · rw [if_pos hsector, Finset.sum_eq_single left]
    · simp [hsector]
    · intro right _ hne
      have hleftRight : left ≠ right := Ne.symm hne
      simp [hsector, hleftRight]
    · simp
  · simp [hsector]
noncomputable def why24OneRoundSyndromeInstrument (r : Nat) :
    FiniteInstrument (f1024Why24OddZSyndrome r)
      (f1024Why24OddZSyndrome r)
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r)) where
  kraus :=
    { operator := why24OneRoundSyndromeProjector r }
  observe := id
theorem why24OneRoundSyndromeInstrument_complete (r : Nat) :
    (why24OneRoundSyndromeInstrument r).kraus.Complete := by
  rw [FiniteKrausFamily.Complete]
  simp only [why24OneRoundSyndromeInstrument]
  rw [Finset.sum_congr rfl (fun syndrome _ => by
    rw [why24OneRoundSyndromeProjector_adjoint,
      why24OneRoundSyndromeProjector_idempotent])]
  exact why24OneRound_sum_syndromeProjector_eq_one r
noncomputable def why24OneRoundCorrection (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    UnitaryTransport
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r)) :=
  wordZTransport (f1024Why24OddAGDualDecoder r syndrome)
noncomputable def why24OneRoundCorrectionInstrument (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    FiniteInstrument PUnit PUnit
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r)) where
  kraus :=
    { operator := fun _ =>
        (why24OneRoundCorrection r syndrome).toLinearEquiv.toLinearMap }
  observe := id
theorem why24OneRoundCorrectionInstrument_complete (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    (why24OneRoundCorrectionInstrument r syndrome).kraus.Complete := by
  rw [FiniteKrausFamily.Complete]
  rw [show (Finset.univ : Finset PUnit) = {PUnit.unit} by
    ext index
    simp]
  rw [Finset.sum_singleton]
  change (LinearMap.adjoint
      (why24OneRoundCorrection r syndrome).toLinearEquiv.toLinearMap).comp
        (why24OneRoundCorrection r syndrome).toLinearEquiv.toLinearMap = 1
  rw [(why24OneRoundCorrection r syndrome).adjoint_toLinearMap]
  ext psi
  simp
noncomputable def why24OneRoundInstrument (r : Nat) :
    FiniteInstrument
      (f1024Why24OddZSyndrome r × PUnit)
      (Sigma (fun _ : f1024Why24OddZSyndrome r => PUnit))
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r)) :=
  (why24OneRoundSyndromeInstrument r).bind
    (why24OneRoundCorrectionInstrument r)
theorem why24OneRoundInstrument_complete (r : Nat) :
    (why24OneRoundInstrument r).kraus.Complete := by
  exact (why24OneRoundSyndromeInstrument r).bind_complete
    (why24OneRoundCorrectionInstrument r)
    (why24OneRoundSyndromeInstrument_complete r)
    (why24OneRoundCorrectionInstrument_complete r)
def why24OneRoundAmbientEncodingIsometry (r : Nat) :
    ComputationalBasisRegister F1024 (f1024Why24OddLogical r) →ₗᵢ[Complex]
      ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r) :=
  (f1024Why24OddEncodedCode r).code.carrier.subtypeₗᵢ.comp
    (f1024Why24OddEncodedCode r).encoding.toLinearIsometry
@[simp] theorem why24OneRoundAmbientEncodingIsometry_apply (r : Nat)
    (psi : ComputationalBasisRegister F1024 (f1024Why24OddLogical r)) :
    why24OneRoundAmbientEncodingIsometry r psi =
      ((f1024Why24OddEncodedCode r).encoding psi :
        ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r)) :=
  rfl
def why24OneRoundCodeDecoderBranch (r : Nat) :
    ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r) →ₗ[Complex]
      ComputationalBasisRegister F1024 (f1024Why24OddLogical r) :=
  LinearMap.adjoint (why24OneRoundAmbientEncodingIsometry r).toLinearMap
@[simp] theorem why24OneRoundCodeDecoderBranch_encoded (r : Nat)
    (psi : ComputationalBasisRegister F1024 (f1024Why24OddLogical r)) :
    why24OneRoundCodeDecoderBranch r
        (why24OneRoundAmbientEncodingIsometry r psi) = psi := by
  change LinearMap.adjoint
      (why24OneRoundAmbientEncodingIsometry r).toLinearMap
      ((why24OneRoundAmbientEncodingIsometry r).toLinearMap psi) = psi
  exact LinearMap.congr_fun
    (why24OneRoundAmbientEncodingIsometry r).adjoint_comp_self' psi
theorem why24OneRound_adjoint_codeDecoderBranch (r : Nat) :
    LinearMap.adjoint (why24OneRoundCodeDecoderBranch r) =
      (why24OneRoundAmbientEncodingIsometry r).toLinearMap := by
  rw [why24OneRoundCodeDecoderBranch, LinearMap.adjoint_adjoint]
def why24OneRoundDecoderCodeProjector (r : Nat) :
    Operator (ComputationalBasisRegister F1024
      (f1024Why24OddPhysicalSite r)) :=
  (LinearMap.adjoint (why24OneRoundCodeDecoderBranch r)).comp
    (why24OneRoundCodeDecoderBranch r)
@[simp] theorem why24OneRoundDecoderCodeProjector_encoded (r : Nat)
    (psi : ComputationalBasisRegister F1024 (f1024Why24OddLogical r)) :
    why24OneRoundDecoderCodeProjector r
        (why24OneRoundAmbientEncodingIsometry r psi) =
      why24OneRoundAmbientEncodingIsometry r psi := by
  change LinearMap.adjoint (why24OneRoundCodeDecoderBranch r)
      (why24OneRoundCodeDecoderBranch r
        (why24OneRoundAmbientEncodingIsometry r psi)) =
    why24OneRoundAmbientEncodingIsometry r psi
  rw [why24OneRoundCodeDecoderBranch_encoded,
    why24OneRound_adjoint_codeDecoderBranch]
  rfl
theorem why24OneRoundCodeDecoderBranch_comp_adjoint (r : Nat) :
    (why24OneRoundCodeDecoderBranch r).comp
        (LinearMap.adjoint (why24OneRoundCodeDecoderBranch r)) = 1 := by
  rw [why24OneRound_adjoint_codeDecoderBranch,
    why24OneRoundCodeDecoderBranch]
  exact (why24OneRoundAmbientEncodingIsometry r).adjoint_comp_self'
theorem why24OneRoundDecoderCodeProjector_idempotent (r : Nat) :
    (why24OneRoundDecoderCodeProjector r).comp
        (why24OneRoundDecoderCodeProjector r) =
      why24OneRoundDecoderCodeProjector r := by
  rw [why24OneRoundDecoderCodeProjector]
  calc
    ((LinearMap.adjoint (why24OneRoundCodeDecoderBranch r)).comp
        (why24OneRoundCodeDecoderBranch r)).comp
        ((LinearMap.adjoint (why24OneRoundCodeDecoderBranch r)).comp
          (why24OneRoundCodeDecoderBranch r)) =
      (LinearMap.adjoint (why24OneRoundCodeDecoderBranch r)).comp
        (((why24OneRoundCodeDecoderBranch r).comp
          (LinearMap.adjoint (why24OneRoundCodeDecoderBranch r))).comp
            (why24OneRoundCodeDecoderBranch r)) := by
              ext psi
              rfl
    _ = (LinearMap.adjoint (why24OneRoundCodeDecoderBranch r)).comp
        ((1 : Operator (ComputationalBasisRegister F1024
          (f1024Why24OddLogical r))).comp
            (why24OneRoundCodeDecoderBranch r)) := by
      rw [why24OneRoundCodeDecoderBranch_comp_adjoint]
    _ = (LinearMap.adjoint (why24OneRoundCodeDecoderBranch r)).comp
        (why24OneRoundCodeDecoderBranch r) := by
      ext psi
      rfl
theorem why24OneRoundDecoderCodeProjector_adjoint (r : Nat) :
    LinearMap.adjoint (why24OneRoundDecoderCodeProjector r) =
      why24OneRoundDecoderCodeProjector r := by
  simp [why24OneRoundDecoderCodeProjector, LinearMap.adjoint_comp]
def why24OneRoundDecoderComplementProjector (r : Nat) :
    Operator (ComputationalBasisRegister F1024
      (f1024Why24OddPhysicalSite r)) :=
  1 - why24OneRoundDecoderCodeProjector r
theorem why24OneRoundDecoderComplementProjector_adjoint (r : Nat) :
    LinearMap.adjoint (why24OneRoundDecoderComplementProjector r) =
      why24OneRoundDecoderComplementProjector r := by
  simp [why24OneRoundDecoderComplementProjector,
    why24OneRoundDecoderCodeProjector_adjoint]
theorem why24OneRoundDecoderComplementProjector_idempotent (r : Nat) :
    (why24OneRoundDecoderComplementProjector r).comp
        (why24OneRoundDecoderComplementProjector r) =
      why24OneRoundDecoderComplementProjector r := by
  ext psi
  have hprojector := LinearMap.congr_fun
    (why24OneRoundDecoderCodeProjector_idempotent r) psi
  simp only [why24OneRoundDecoderComplementProjector,
    LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply,
    map_sub] at hprojector ⊢
  rw [hprojector]
  abel_nf
@[simp] theorem why24OneRoundDecoderComplementProjector_encoded
    (r : Nat)
    (psi : ComputationalBasisRegister F1024 (f1024Why24OddLogical r)) :
    why24OneRoundDecoderComplementProjector r
        (why24OneRoundAmbientEncodingIsometry r psi) = 0 := by
  simp only [why24OneRoundDecoderComplementProjector,
    LinearMap.sub_apply, Module.End.one_apply]
  rw [why24OneRoundDecoderCodeProjector_encoded]
  abel_nf
noncomputable def why24OneRoundDecoderFallbackState (r : Nat) :
    ComputationalBasisRegister F1024 (f1024Why24OddLogical r) :=
  EuclideanSpace.basisFun
    (Why24Word (f1024Why24OddLogical r)) Complex (fun _ => 0)
theorem why24OneRoundDecoderFallbackState_normSq (r : Nat) :
    ‖why24OneRoundDecoderFallbackState r‖ ^ 2 = 1 := by
  simp [why24OneRoundDecoderFallbackState]
noncomputable def why24OneRoundDecoderPhysicalBasis (r : Nat) :=
  stdOrthonormalBasis Complex
    (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))
def why24OneRoundComplementDecoderBranch (r : Nat)
    (index : Fin (Module.finrank Complex
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r)))) :
    ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r) →ₗ[Complex]
      ComputationalBasisRegister F1024 (f1024Why24OddLogical r) :=
  (InnerProductSpace.rankOne Complex
    (why24OneRoundDecoderFallbackState r)
    (why24OneRoundDecoderComplementProjector r
      (why24OneRoundDecoderPhysicalBasis r index))).toLinearMap
theorem why24OneRoundComplementDecoderBranch_adjoint_comp (r : Nat)
    (index : Fin (Module.finrank Complex
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r)))) :
    (LinearMap.adjoint (why24OneRoundComplementDecoderBranch r index)).comp
        (why24OneRoundComplementDecoderBranch r index) =
      (InnerProductSpace.rankOne Complex
        (why24OneRoundDecoderComplementProjector r
          (why24OneRoundDecoderPhysicalBasis r index))
        (why24OneRoundDecoderComplementProjector r
          (why24OneRoundDecoderPhysicalBasis r index))).toLinearMap := by
  have hadjoint : LinearMap.adjoint
      ((InnerProductSpace.rankOne Complex
        (why24OneRoundDecoderFallbackState r)
        (why24OneRoundDecoderComplementProjector r
          (why24OneRoundDecoderPhysicalBasis r index))).toLinearMap) =
      (InnerProductSpace.rankOne Complex
        (why24OneRoundDecoderComplementProjector r
          (why24OneRoundDecoderPhysicalBasis r index))
        (why24OneRoundDecoderFallbackState r)).toLinearMap := by
    rw [LinearMap.adjoint_eq_toCLM_adjoint]
    change ((InnerProductSpace.rankOne Complex
      (why24OneRoundDecoderFallbackState r)
      (why24OneRoundDecoderComplementProjector r
        (why24OneRoundDecoderPhysicalBasis r index))).adjoint).toLinearMap = _
    rw [InnerProductSpace.adjoint_rankOne]
  apply LinearMap.ext
  intro psi
  simp only [why24OneRoundComplementDecoderBranch]
  rw [hadjoint]
  have hnormSq : (↑‖why24OneRoundDecoderFallbackState r‖ : Complex) ^ 2 = 1 := by
    norm_cast
    exact why24OneRoundDecoderFallbackState_normSq r
  simp [LinearMap.comp_apply, hnormSq]
theorem why24OneRound_sum_complementDecoderBranch_adjoint_comp
    (r : Nat) :
    ∑ index : Fin (Module.finrank Complex
        (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))),
      (LinearMap.adjoint (why24OneRoundComplementDecoderBranch r index)).comp
        (why24OneRoundComplementDecoderBranch r index) =
      why24OneRoundDecoderComplementProjector r := by
  simp_rw [why24OneRoundComplementDecoderBranch_adjoint_comp]
  calc
    (∑ index,
      (InnerProductSpace.rankOne Complex
        (why24OneRoundDecoderComplementProjector r
          (why24OneRoundDecoderPhysicalBasis r index))
        (why24OneRoundDecoderComplementProjector r
          (why24OneRoundDecoderPhysicalBasis r index))).toLinearMap) =
      (why24OneRoundDecoderComplementProjector r).comp
        (LinearMap.adjoint (why24OneRoundDecoderComplementProjector r)) := by
      apply LinearMap.ext
      intro psi
      simp only [LinearMap.sum_apply, LinearMap.comp_apply]
      rw [← (why24OneRoundDecoderPhysicalBasis r).sum_repr'
        (LinearMap.adjoint (why24OneRoundDecoderComplementProjector r) psi)]
      simp only [map_sum, map_smul]
      apply Finset.sum_congr rfl
      intro index _
      rw [LinearMap.adjoint_inner_right]
      rfl
    _ = (why24OneRoundDecoderComplementProjector r).comp
        (why24OneRoundDecoderComplementProjector r) := by
      rw [why24OneRoundDecoderComplementProjector_adjoint]
    _ = why24OneRoundDecoderComplementProjector r :=
      why24OneRoundDecoderComplementProjector_idempotent r
def why24OneRoundDecoderKrausFamily (r : Nat) :
    FiniteKrausFamily
      (Sum Unit (Fin (Module.finrank Complex
        (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r)))))
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))
      (ComputationalBasisRegister F1024 (f1024Why24OddLogical r)) where
  operator
    | .inl _ => why24OneRoundCodeDecoderBranch r
    | .inr index => why24OneRoundComplementDecoderBranch r index
theorem why24OneRoundDecoderKrausFamily_complete (r : Nat) :
    (why24OneRoundDecoderKrausFamily r).Complete := by
  rw [FiniteKrausFamily.Complete, Fintype.sum_sum_type]
  change (∑ _ : Unit, why24OneRoundDecoderCodeProjector r) +
      (∑ index : Fin (Module.finrank Complex
        (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))),
        (LinearMap.adjoint (why24OneRoundComplementDecoderBranch r index)).comp
          (why24OneRoundComplementDecoderBranch r index)) = 1
  rw [Fintype.sum_unique,
    why24OneRound_sum_complementDecoderBranch_adjoint_comp]
  simp [why24OneRoundDecoderComplementProjector]
noncomputable def why24OneRoundDecoderChannel (r : Nat) :
    QuantumChannel
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))
      (ComputationalBasisRegister F1024 (f1024Why24OddLogical r)) :=
  (why24OneRoundDecoderKrausFamily r).toQuantumChannel
    (why24OneRoundDecoderKrausFamily_complete r)
def why24OneRoundAccepts {r : Nat}
    (_ : Sigma (fun _ : f1024Why24OddZSyndrome r => PUnit)) : Bool :=
  true
def why24OneRoundInputCount (r : Nat) : Nat :=
  why24CCZToUOneSevenInputCount * f1024Why24OddLength r
def why24OneRoundOutputCount (r : Nat) : Nat :=
  f1024Why24OddDimension r
theorem why24OneRoundInputCount_eq (r : Nat) :
    why24OneRoundInputCount r = 70 * f1024Why24OddLength r := by
  rw [why24OneRoundInputCount, why24CCZToUOneSeven_inputCount_eq_seventy]
def why24OneRoundCCZLocationEquiv (r : Nat) :
    Fin (f1024Why24OddLength r) × Fin 70 ≃
      Fin (why24OneRoundInputCount r) :=
  finProdFinEquiv.trans (finCongr (by
    rw [why24OneRoundInputCount_eq]
    omega))
noncomputable def why24OneRoundPhysicalSiteEquiv (r : Nat) :
    f1024Why24OddPhysicalSite r ≃ Fin (f1024Why24OddLength r) :=
  Fintype.equivFin _
noncomputable def why24OneRoundLogicalPlusKet (r : Nat) :
    ComputationalBasisRegister F1024 (f1024Why24OddLogical r) :=
  why24OneRoundCharacterKet
    (0 : Why24Word (f1024Why24OddLogical r))
theorem why24OneRoundLogicalPlusKet_normSq (r : Nat) :
    ‖why24OneRoundLogicalPlusKet r‖ ^ 2 = 1 := by
  have hinner : inner Complex (why24OneRoundLogicalPlusKet r)
      (why24OneRoundLogicalPlusKet r) = 1 := by
    have h := why24OneRoundCharacterKet_inner
      (Site := f1024Why24OddLogical r)
      (0 : Why24Word (f1024Why24OddLogical r))
      (0 : Why24Word (f1024Why24OddLogical r))
    simp only [if_pos] at h
    convert h using 1
    simp only [why24OneRoundLogicalPlusKet, PiLp.inner_apply]
    apply Finset.sum_congr
    · ext label
      simp
    · intro label _
      rfl
  calc
    ‖why24OneRoundLogicalPlusKet r‖ ^ 2 =
        (inner Complex (why24OneRoundLogicalPlusKet r)
          (why24OneRoundLogicalPlusKet r)).re :=
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex)
        (why24OneRoundLogicalPlusKet r)
    _ = 1 := by rw [hinner]; norm_num
noncomputable def why24OneRoundLogicalIdealKet (r : Nat) :
    ComputationalBasisRegister F1024 (f1024Why24OddLogical r) :=
  (f1024Why24OddWeightedMatrix r).logicalUOneSeven
    (why24OneRoundLogicalPlusKet r)
theorem why24OneRoundLogicalIdealKet_normSq (r : Nat) :
    ‖why24OneRoundLogicalIdealKet r‖ ^ 2 = 1 := by
  change ‖(f1024Why24OddWeightedMatrix r).logicalUOneSeven.toLinearIsometryEquiv
    (why24OneRoundLogicalPlusKet r)‖ ^ 2 = 1
  rw [(f1024Why24OddWeightedMatrix r).logicalUOneSeven.toLinearIsometryEquiv.norm_map]
  exact why24OneRoundLogicalPlusKet_normSq r
noncomputable def why24OneRoundEncodedIdealKet (r : Nat) :
    ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r) :=
  why24OneRoundAmbientEncodingIsometry r
    (why24OneRoundLogicalIdealKet r)
theorem why24OneRoundEncodedIdealKet_normSq (r : Nat) :
    ‖why24OneRoundEncodedIdealKet r‖ ^ 2 = 1 := by
  rw [why24OneRoundEncodedIdealKet,
    (why24OneRoundAmbientEncodingIsometry r).norm_map]
  exact why24OneRoundLogicalIdealKet_normSq r
noncomputable def why24OneRoundErrorKet (r : Nat)
    (error : Why24Word (f1024Why24OddPhysicalSite r)) :
    ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r) :=
  wordZTransport error (why24OneRoundEncodedIdealKet r)
theorem why24OneRoundErrorKet_normSq (r : Nat)
    (error : Why24Word (f1024Why24OddPhysicalSite r)) :
    ‖why24OneRoundErrorKet r error‖ ^ 2 = 1 := by
  change ‖(wordZTransport error).toLinearIsometryEquiv
    (why24OneRoundEncodedIdealKet r)‖ ^ 2 = 1
  rw [(wordZTransport error).toLinearIsometryEquiv.norm_map]
  exact why24OneRoundEncodedIdealKet_normSq r
noncomputable def why24OneRoundErrorDensity (r : Nat)
    (error : Why24Word (f1024Why24OddPhysicalSite r)) :
    DensityOperator
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r)) :=
  DensityOperator.pureDensity (why24OneRoundErrorKet r error)
    (why24OneRoundErrorKet_normSq r error)
def why24OneRoundAppendixErrorWord (r : Nat)
    (error : Fin (why24OneRoundInputCount r) ->
      Qubit.Bitstring (Fin 3)) :
    Why24Word (f1024Why24OddPhysicalSite r) :=
  fun site =>
    why24ComputationalLabelEquiv.symm
      (why24CCZToUOneSevenErrorWord fun gate =>
        error (why24OneRoundCCZLocationEquiv r
          (why24OneRoundPhysicalSiteEquiv r site, gate)))
noncomputable def why24OneRoundFrontEndKraus (r : Nat) :
    FiniteKrausFamily
      (Fin (why24OneRoundInputCount r) -> Qubit.Bitstring (Fin 3))
      (Why24CCZRegister (Fin (why24OneRoundInputCount r)))
      (ComputationalBasisRegister F1024
        (f1024Why24OddPhysicalSite r)) where
  operator error :=
    (InnerProductSpace.rankOne Complex
      (why24OneRoundErrorKet r (why24OneRoundAppendixErrorWord r error))
      (why24JointCCZMagicBasisKet (why24OneRoundInputCount r) error)).toLinearMap
theorem why24OneRoundFrontEndKraus_adjoint_comp (r : Nat)
    (error : Fin (why24OneRoundInputCount r) -> Qubit.Bitstring (Fin 3)) :
    (LinearMap.adjoint (why24OneRoundFrontEndKraus r |>.operator error)).comp
        (why24OneRoundFrontEndKraus r |>.operator error) =
      (InnerProductSpace.rankOne Complex
        (why24JointCCZMagicBasisKet (why24OneRoundInputCount r) error)
        (why24JointCCZMagicBasisKet
          (why24OneRoundInputCount r) error)).toLinearMap := by
  have hadjoint : LinearMap.adjoint
      ((InnerProductSpace.rankOne Complex
        (why24OneRoundErrorKet r (why24OneRoundAppendixErrorWord r error))
        (why24JointCCZMagicBasisKet
          (why24OneRoundInputCount r) error)).toLinearMap) =
      (InnerProductSpace.rankOne Complex
        (why24JointCCZMagicBasisKet (why24OneRoundInputCount r) error)
        (why24OneRoundErrorKet r
          (why24OneRoundAppendixErrorWord r error))).toLinearMap := by
    rw [LinearMap.adjoint_eq_toCLM_adjoint]
    change ((InnerProductSpace.rankOne Complex
      (why24OneRoundErrorKet r (why24OneRoundAppendixErrorWord r error))
      (why24JointCCZMagicBasisKet
        (why24OneRoundInputCount r) error)).adjoint).toLinearMap = _
    rw [InnerProductSpace.adjoint_rankOne]
  ext psi
  simp only [why24OneRoundFrontEndKraus]
  rw [hadjoint]
  have hnormSq :
      (↑‖why24OneRoundErrorKet r
        (why24OneRoundAppendixErrorWord r error)‖ : Complex) ^ 2 = 1 := by
    norm_cast
    exact why24OneRoundErrorKet_normSq r
      (why24OneRoundAppendixErrorWord r error)
  simp [LinearMap.comp_apply, hnormSq]
theorem why24OneRoundFrontEndInstrument_complete (r : Nat) :
    (why24OneRoundFrontEndKraus r).Complete := by
  rw [FiniteKrausFamily.Complete]
  simp_rw [why24OneRoundFrontEndKraus_adjoint_comp]
  have hport := congrArg ContinuousLinearMap.toLinearMap
    (OrthonormalBasis.sum_rankOne_eq_id
      (why24JointCCZMagicBasis (why24OneRoundInputCount r)))
  simp [why24JointCCZMagicBasisKet] at hport ⊢
  exact hport
noncomputable def why24OneRoundFrontEndInstrument (r : Nat) :
    FiniteInstrument
      (Fin (why24OneRoundInputCount r) -> Qubit.Bitstring (Fin 3))
      (Fin (why24OneRoundInputCount r) -> Qubit.Bitstring (Fin 3))
      (Why24CCZRegister (Fin (why24OneRoundInputCount r)))
      (ComputationalBasisRegister F1024
        (f1024Why24OddPhysicalSite r)) where
  kraus := why24OneRoundFrontEndKraus r
  observe := id
noncomputable def why24OneRoundFrontEndChannel (r : Nat) :
    QuantumChannel
      (Why24CCZRegister (Fin (why24OneRoundInputCount r)))
      (ComputationalBasisRegister F1024
        (f1024Why24OddPhysicalSite r)) :=
  (why24OneRoundFrontEndKraus r).toQuantumChannel
    (why24OneRoundFrontEndInstrument_complete r)
noncomputable def why24OneRoundJointBornWeight (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (fault : Finset (Fin (why24OneRoundInputCount r)))
    (error : Fin (why24OneRoundInputCount r) -> Qubit.Bitstring (Fin 3)) :
    Real :=
  (inner Complex
    (why24JointCCZMagicBasisKet (why24OneRoundInputCount r) error)
    ((preparation.branchDensity fault).toOperator
      (why24JointCCZMagicBasisKet
        (why24OneRoundInputCount r) error))).re
theorem why24OneRoundBranchDensity_toOperator (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (fault : Finset (Fin (why24OneRoundInputCount r))) :
    (preparation.branchDensity fault).toOperator =
      ∑ index : Fin (preparation.faultOperation fault).krausCount,
        (InnerProductSpace.rankOne Complex
          ((preparation.faultOperation fault).kraus.operator index
            (why24JointCCZMagicBasisKet (why24OneRoundInputCount r) 0))
          ((preparation.faultOperation fault).kraus.operator index
            (why24JointCCZMagicBasisKet
              (why24OneRoundInputCount r) 0))).toLinearMap := by
  rw [Why24LocalStochasticPreparation.branchDensity,
    QuantumChannel.mapDensity_toOperator,
    Why24CCZFaultOperation.channel,
    FiniteKrausFamily.toQuantumChannel_apply_sum,
    why24IdealCCZRegisterDensity_toOperator]
  simp_rw [why24LinearMap_comp_rankOne_comp_adjoint]
theorem why24OneRoundJointBornWeight_nonneg (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (fault : Finset (Fin (why24OneRoundInputCount r)))
    (error : Fin (why24OneRoundInputCount r) -> Qubit.Bitstring (Fin 3)) :
    0 <= why24OneRoundJointBornWeight r preparation fault error := by
  exact (preparation.branchDensity fault).positive.re_inner_nonneg_right _
theorem why24OneRoundJointBornWeight_sum (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (fault : Finset (Fin (why24OneRoundInputCount r))) :
    (∑ error, why24OneRoundJointBornWeight r preparation fault error) = 1 := by
  have htrace := (preparation.branchDensity fault).trace_one
  rw [LinearMap.trace_eq_sum_inner
    (preparation.branchDensity fault).toOperator
    (why24JointCCZMagicBasis (why24OneRoundInputCount r))] at htrace
  have hre := congrArg Complex.re htrace
  simp [why24OneRoundJointBornWeight, why24JointCCZMagicBasisKet,
    Complex.re_sum] at hre ⊢
  exact hre
theorem why24OneRoundJointBornWeight_eq_zero_of_outside
    (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (fault : Finset (Fin (why24OneRoundInputCount r)))
    (error : Fin (why24OneRoundInputCount r) -> Qubit.Bitstring (Fin 3))
    (site : Fin (why24OneRoundInputCount r))
    (hsite : site ∉ fault) (herror : error site ≠ 0) :
    why24OneRoundJointBornWeight r preparation fault error = 0 := by
  unfold why24OneRoundJointBornWeight
  have hinner :
      inner Complex
        (why24JointCCZMagicBasisKet (why24OneRoundInputCount r) error)
        ((preparation.branchDensity fault).toOperator
          (why24JointCCZMagicBasisKet
            (why24OneRoundInputCount r) error)) = 0 := by
    rw [why24OneRoundBranchDensity_toOperator,
      LinearMap.sum_apply, inner_sum]
    apply Finset.sum_eq_zero
    intro index _
    have hamplitude := why24SupportedOperator_magicAmplitude_eq_zero
      fault
      ((preparation.faultOperation fault).kraus.operator index)
      ((preparation.faultOperation fault).supported index)
      error site hsite herror
    simp [InnerProductSpace.rankOne_apply, hamplitude]
  rw [hinner]
  rfl
theorem why24OneRoundAppendixErrorWord_exists_gate
    (r : Nat)
    (error : Fin (why24OneRoundInputCount r) -> Qubit.Bitstring (Fin 3))
    (site : f1024Why24OddPhysicalSite r)
    (herror : why24OneRoundAppendixErrorWord r error site ≠ 0) :
    ∃ gate : Fin 70,
      error (why24OneRoundCCZLocationEquiv r
        (why24OneRoundPhysicalSiteEquiv r site, gate)) ≠ 0 := by
  by_contra hgate
  have hgateZero : ∀ gate : Fin 70,
      error (why24OneRoundCCZLocationEquiv r
        (why24OneRoundPhysicalSiteEquiv r site, gate)) = 0 := by
    intro gate
    by_contra hne
    exact hgate ⟨gate, hne⟩
  apply herror
  have hzero :
      (fun gate : Fin 70 =>
        error (why24OneRoundCCZLocationEquiv r
          (why24OneRoundPhysicalSiteEquiv r site, gate))) = 0 := by
    funext gate
    exact hgateZero gate
  rw [why24OneRoundAppendixErrorWord, hzero,
    why24CCZToUOneSevenErrorWord_zero]
  apply f1024SelectedCoordinates.injective
  rw [f1024SelectedCoordinates_label_symm]
  change (0 : Fin 10 → ZMod 2) = f1024SelectedCoordinates 0
  exact (map_zero f1024SelectedCoordinates).symm
noncomputable def why24OneRoundDerivedBranchMass (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (fault : Finset (Fin (why24OneRoundInputCount r)))
    (fieldError : Why24Word (f1024Why24OddPhysicalSite r)) : Real :=
  ∑ jointError :
      Fin (why24OneRoundInputCount r) -> Qubit.Bitstring (Fin 3),
    if fieldError = why24OneRoundAppendixErrorWord r jointError then
      preparation.faultMass fault *
        why24OneRoundJointBornWeight r preparation fault jointError
    else 0
theorem why24OneRoundDerivedBranchMass_nonneg (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (fault : Finset (Fin (why24OneRoundInputCount r)))
    (fieldError : Why24Word (f1024Why24OddPhysicalSite r)) :
    0 <= why24OneRoundDerivedBranchMass r preparation fault fieldError := by
  exact Finset.sum_nonneg fun jointError _ => by
    split_ifs
    · exact mul_nonneg (preparation.faultMass_nonneg fault)
        (why24OneRoundJointBornWeight_nonneg r preparation fault jointError)
    · exact le_rfl
theorem why24OneRoundDerivedBranchMass_sum (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (fault : Finset (Fin (why24OneRoundInputCount r))) :
    (∑ fieldError,
      why24OneRoundDerivedBranchMass r preparation fault fieldError) =
        preparation.faultMass fault := by
  unfold why24OneRoundDerivedBranchMass
  rw [Finset.sum_comm]
  calc
    (∑ jointError :
        Fin (why24OneRoundInputCount r) -> Qubit.Bitstring (Fin 3),
      ∑ fieldError : Why24Word (f1024Why24OddPhysicalSite r),
        if fieldError = why24OneRoundAppendixErrorWord r jointError then
          preparation.faultMass fault *
            why24OneRoundJointBornWeight r preparation fault jointError
        else 0) =
      ∑ jointError :
          Fin (why24OneRoundInputCount r) -> Qubit.Bitstring (Fin 3),
        preparation.faultMass fault *
          why24OneRoundJointBornWeight r preparation fault jointError := by
      apply Finset.sum_congr rfl
      intro jointError _
      rw [Finset.sum_eq_single
        (why24OneRoundAppendixErrorWord r jointError)]
      · rw [if_pos rfl]
      · intro fieldError _ hne
        rw [if_neg hne]
      · simp
    _ = preparation.faultMass fault *
        ∑ jointError :
          Fin (why24OneRoundInputCount r) -> Qubit.Bitstring (Fin 3),
          why24OneRoundJointBornWeight r preparation fault jointError := by
      rw [Finset.mul_sum]
    _ = preparation.faultMass fault := by
      rw [why24OneRoundJointBornWeight_sum, mul_one]
theorem why24OneRoundDerivedBranchMass_error_supported (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (fault : Finset (Fin (why24OneRoundInputCount r)))
    (fieldError : Why24Word (f1024Why24OddPhysicalSite r))
    (hmass : why24OneRoundDerivedBranchMass r preparation fault fieldError ≠ 0)
    (site : f1024Why24OddPhysicalSite r) (herror : fieldError site ≠ 0) :
    ∃ gate : Fin 70,
      why24OneRoundCCZLocationEquiv r
        (why24OneRoundPhysicalSiteEquiv r site, gate) ∈ fault := by
  obtain ⟨jointError, _, hjointMass⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hmass
  have hfield :
      fieldError = why24OneRoundAppendixErrorWord r jointError := by
    by_contra hne
    rw [if_neg hne] at hjointMass
    exact hjointMass rfl
  obtain ⟨gate, hgateError⟩ :=
    why24OneRoundAppendixErrorWord_exists_gate r jointError site
      (hfield ▸ herror)
  refine ⟨gate, ?_⟩
  by_contra hnotmem
  have hbornZero := why24OneRoundJointBornWeight_eq_zero_of_outside
    r preparation fault jointError
      (why24OneRoundCCZLocationEquiv r
        (why24OneRoundPhysicalSiteEquiv r site, gate))
      hnotmem hgateError
  rw [if_pos hfield, hbornZero, mul_zero] at hjointMass
  exact hjointMass rfl
structure Why24OneRoundTwirledConversionLaw (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) where
  branchMass :
    Finset (Fin (why24OneRoundInputCount r)) →
      Why24Word (f1024Why24OddPhysicalSite r) → Real
  branchMass_nonneg : ∀ fault error, 0 ≤ branchMass fault error
  branchMass_sum : ∀ fault,
    (∑ error, branchMass fault error) = preparation.faultMass fault
  error_supported : ∀ fault error,
    branchMass fault error ≠ 0 →
      ∀ site, error site ≠ 0 →
        ∃ gate : Fin 70,
          why24OneRoundCCZLocationEquiv r
            (why24OneRoundPhysicalSiteEquiv r site, gate) ∈ fault
noncomputable def why24OneRoundDerivedTwirledConversionLaw (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    Why24OneRoundTwirledConversionLaw r preparation where
  branchMass := why24OneRoundDerivedBranchMass r preparation
  branchMass_nonneg := why24OneRoundDerivedBranchMass_nonneg r preparation
  branchMass_sum := why24OneRoundDerivedBranchMass_sum r preparation
  error_supported :=
    why24OneRoundDerivedBranchMass_error_supported r preparation
namespace Why24OneRoundTwirledConversionLaw
variable {r : Nat}
variable {preparation : Why24LocalStochasticPreparation
  (Fin (why24OneRoundInputCount r))
  (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))}
noncomputable def errorMass
    (law : Why24OneRoundTwirledConversionLaw r preparation)
    (error : Why24Word (f1024Why24OddPhysicalSite r)) : Real :=
  ∑ fault : Finset (Fin (why24OneRoundInputCount r)),
    law.branchMass fault error
theorem errorMass_nonneg
    (law : Why24OneRoundTwirledConversionLaw r preparation)
    (error : Why24Word (f1024Why24OddPhysicalSite r)) :
    0 ≤ law.errorMass error := by
  exact Finset.sum_nonneg (fun _ _ => law.branchMass_nonneg _ _)
theorem errorMass_sum
    (law : Why24OneRoundTwirledConversionLaw r preparation) :
    ∑ error, law.errorMass error = 1 := by
  simp only [errorMass]
  rw [Finset.sum_comm]
  simp_rw [law.branchMass_sum]
  exact preparation.faultMass_sum
end Why24OneRoundTwirledConversionLaw
noncomputable def why24OneRoundPreparedPhysicalDensityForLaw (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (law : Why24OneRoundTwirledConversionLaw r preparation) :
    DensityOperator
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r)) :=
  DensityOperator.convexCombination Finset.univ law.errorMass
    (why24OneRoundErrorDensity r)
    (by intro error _; exact law.errorMass_nonneg error)
    (by simpa using law.errorMass_sum)
noncomputable def why24OneRoundPreparedPhysicalDensity (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    DensityOperator
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r)) :=
  why24OneRoundPreparedPhysicalDensityForLaw r preparation
    (why24OneRoundDerivedTwirledConversionLaw r preparation)
noncomputable def why24OneRoundIdealPhysicalDensity (r : Nat) :
    DensityOperator
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r)) :=
  why24OneRoundErrorDensity r 0
noncomputable def why24CorrelatedPrepareInput (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (inputs : ResourceInput (why24OneRoundInputCount r) Why24CCZSpace) :
    DensityOperator
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r)) :=
  if inputs = why24LocalStochasticResourceInputs preparation then
    why24OneRoundPreparedPhysicalDensity r preparation
  else why24OneRoundIdealPhysicalDensity r
noncomputable def why24OneRoundRunBeforeDecode (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    DistillationRun Why24CCZSpace
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r)) :=
  FiniteInstrument.binaryDistillationRun
    (Resource := Why24CCZSpace)
    (H := ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))
    (K := ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))
    (why24OneRoundInstrument.{0} r) why24OneRoundAccepts.{0}
    (why24OneRoundInstrument_complete.{0} r)
    (why24OneRoundInputCount r)
    (why24LocalStochasticResourceInputs preparation)
    (why24CorrelatedPrepareInput r preparation)
    (why24OneRoundIdealPhysicalDensity r)
noncomputable def why24OneRoundRun (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    DistillationRun Why24CCZSpace
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))
      (ComputationalBasisRegister F1024 (f1024Why24OddLogical r)) :=
  (why24OneRoundRunBeforeDecode r preparation).postprocess (why24OneRoundDecoderChannel r)
noncomputable def why24OneRoundFailureMassForLaw (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (law : Why24OneRoundTwirledConversionLaw r preparation) : Real :=
  ∑ fault : Finset (Fin (why24OneRoundInputCount r)),
    ∑ error : Why24Word (f1024Why24OddPhysicalSite r),
      if f1024Why24OddDecodingRadius r < HammingWeight error then
        law.branchMass fault error
      else 0
def why24OneRoundFaultFails (r : Nat)
    {preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))}
    (law : Why24OneRoundTwirledConversionLaw r preparation)
    (fault : Finset (Fin (why24OneRoundInputCount r))) : Prop :=
  ∃ error : Why24Word (f1024Why24OddPhysicalSite r),
    f1024Why24OddDecodingRadius r < HammingWeight error ∧
      law.branchMass fault error ≠ 0
noncomputable def why24OneRoundWitnessLocations (r : Nat)
    (sites : Finset (f1024Why24OddPhysicalSite r))
    (gate : {site // site ∈ sites} → Fin 70) :
    Finset (Fin (why24OneRoundInputCount r)) :=
  sites.attach.image fun site =>
    why24OneRoundCCZLocationEquiv r
      (why24OneRoundPhysicalSiteEquiv r site.1, gate site)
noncomputable def why24OneRoundWitnessFaultMass (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (sites : Finset (f1024Why24OddPhysicalSite r))
    (gate : {site // site ∈ sites} → Fin 70) : Real :=
  ∑ fault : Finset (Fin (why24OneRoundInputCount r)),
    if why24OneRoundWitnessLocations r sites gate ⊆ fault then
      preparation.faultMass fault
    else 0
noncomputable def why24OneRoundFailureMass (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) : Real :=
  why24OneRoundFailureMassForLaw r preparation
    (why24OneRoundDerivedTwirledConversionLaw r preparation)
noncomputable def why24OneRoundLogicalIdealDensity (r : Nat) :
    DensityOperator
      (ComputationalBasisRegister F1024 (f1024Why24OddLogical r)) :=
  DensityOperator.pureDensity (why24OneRoundLogicalIdealKet r)
    (why24OneRoundLogicalIdealKet_normSq r)
noncomputable def why24OneRoundCorrectedErrorKet (r : Nat)
    (error : Why24Word (f1024Why24OddPhysicalSite r)) :
    ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r) :=
  why24OneRoundCorrection r (f1024Why24OddZSyndromeMap r error)
    (why24OneRoundSyndromeProjector r
      (f1024Why24OddZSyndromeMap r error)
      (why24OneRoundErrorKet r error))
noncomputable def why24OneRoundPhysicalChannel (r : Nat) :
    QuantumChannel
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))
      (ComputationalBasisRegister F1024 (f1024Why24OddLogical r)) :=
  QuantumChannel.comp (why24OneRoundDecoderChannel r)
    ((why24OneRoundInstrument.{0} r).kraus.toQuantumChannel
      (why24OneRoundInstrument_complete.{0} r))
noncomputable def why24OneRoundDecodedErrorDensity (r : Nat)
    (error : Why24Word (f1024Why24OddPhysicalSite r)) :
    DensityOperator
      (ComputationalBasisRegister F1024 (f1024Why24OddLogical r)) :=
  (why24OneRoundPhysicalChannel r).mapDensity
    (why24OneRoundErrorDensity r error)
noncomputable def why24OneRoundDecodedResidual (r : Nat)
    {preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))}
    (law : Why24OneRoundTwirledConversionLaw r preparation) :
    Operator (ComputationalBasisRegister F1024
      (f1024Why24OddLogical r)) :=
  ∑ error : Why24Word (f1024Why24OddPhysicalSite r),
    if f1024Why24OddDecodingRadius r < HammingWeight error then
      (law.errorMass error : Complex) •
        ((why24OneRoundDecodedErrorDensity r error).toOperator -
          (why24OneRoundLogicalIdealDensity r).toOperator)
    else 0
noncomputable def why24OneRoundTraceDistance {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
    (rho sigma : DensityOperator H) : Real :=
  (2 : Real)⁻¹ * traceNorm (rho.toOperator - sigma.toOperator)
noncomputable def why24OneRoundOutputError (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) : Real :=
  why24OneRoundTraceDistance
    (why24OneRoundRun r preparation).rawOutput
    (why24OneRoundLogicalIdealDensity r)
noncomputable def why24OneRoundMagicStateDistillationProtocol (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    MagicStateDistillationProtocol Why24CCZSpace
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))
      (ComputationalBasisRegister F1024 (f1024Why24OddLogical r)) where
  run := why24OneRoundRun r preparation
  inputErrorModel := InputErrorModel.localStochastic
    (why24LocalStochasticInputErrorModel preparation)
  inputPermitted := why24LocalStochasticInputErrorModel_permits preparation
  behavior := .activeCorrection (QuantumChannel.id _)
  idealOutput := why24OneRoundLogicalIdealDensity r
  outputError := why24OneRoundTraceDistance
  outputError_nonneg := by
    intro rho sigma
    exact mul_nonneg (by norm_num) (traceNorm_nonneg _)
end QEC.Distillation.Why24OneRoundProtocol


