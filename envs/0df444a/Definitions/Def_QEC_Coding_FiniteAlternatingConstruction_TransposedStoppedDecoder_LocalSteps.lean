-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_LocalSteps
-- name    : QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_LocalSteps
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T14:30:39.605097+00:00
-- url     : https://prove2.me/theorems/15901f9b-d875-4b2d-a113-17e83cbb2388
-- title:
--   Local Steps
-- statement:
--   Definitions and structural lemmas for Local Steps, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/LocalSteps.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_LevelTwoHistory
import Theorems.Thm_P2M_QEC_Coding_wordLinearMapTranspose_toLin__apply_6aba8976cbc7
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_correctionRegion_mem
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_syndromeRegion_mem
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_presentationOutput_coarse
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_presentationOutput_components
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_presentationOutput_correction
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qCorrectionEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qRepresentative_value
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qSyndromeEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_regionExtension_apply
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_transpose_wordEquiv_symm
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xCorrectionEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xLift_other
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xLift_same
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xSyndromeEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_zPairEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_zSyndromeEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalWordPush_single
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_presentationOutput_coarse
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_presentationOutput_components
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_presentationOutput_correction
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzFace_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzQ_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzX_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzZ_card
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_map2Coord_canonicalBasis
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary0_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary1_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_fiberPart_apply
import Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rxQOutgoing_nonincident
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0DoubleCylinderEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0DoubleCylinderVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0StarEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0StarVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0SubdivisionEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0SubdivisionVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4DoubleCylinderEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4DoubleCylinderVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4StarEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4StarVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4SubdivisionEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4SubdivisionVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_qDoubleCylinderEndRestriction_apply
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rxDualFace_left_inverse
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rxDualFace_right_inverse
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rxDual_coboundary0
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rxDual_coboundary1
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rzDualFace_left_inverse
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rzDualFace_right_inverse
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rzDual_coboundary0
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rzDual_coboundary1
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_transpose_transpose
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_copiedQ_image_copy
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_copiedQ_image_vertical
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_verticalZ_image_copy
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_verticalZ_image_vertical
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_coarseSyndrome_coe
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_historicalZeroSyndromeInput_supportFitsRadiusTwo
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionLength_sym2_mk
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_diag_not_mem_fixedGeneratorInteractions
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorOperator_adjoint_eq_self
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorSupport_eq_support
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_term_adjoint_eq_self
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridCellQubits_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridOccupiedCells_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_qubitsInRectangle_iff
import Theorems.Thm_QEC_Locality_centeredRectangleClippedGrowthRadius_zero
import Theorems.Thm_QEC_Locality_mem_centeredRectangleQubits_iff
import Theorems.Thm_QEC_Locality_mem_longInteractionEndpointQubits_iff
import Theorems.Thm_QEC_Locality_mem_longNeighborsOf_iff
import Theorems.Thm_QEC_Locality_mem_squareQubits_iff
import Theorems.Thm_QEC_Locality_squareGrowthRadius_succ_sub
import Theorems.Thm_QEC_Locality_squareGrowthRadius_zero
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
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.BDL26DecodingGraph.correctionRegion_mem
attribute [local simp] QEC.Coding.BDL26DecodingGraph.syndromeRegion_mem
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.alternatingCarrier_zero
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_target_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_target_val
attribute [local simp] QEC.Coding.BDL26FiniteTannerSquare.doubleCylinderEndInclusion_apply
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.presentationOutput_coarse
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.presentationOutput_components
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.presentationOutput_correction
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.qCorrectionEquiv_val
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.qRepresentative_value
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.qSyndromeEquiv_val
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.regionExtension_apply
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.transpose_wordEquiv_symm
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.xCorrectionEquiv_val
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.xLift_other
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.xLift_same
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.xSyndromeEquiv_val
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.zPairEquiv_val
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.zSyndromeEquiv_val
attribute [local simp] QEC.Coding.BDL26RXLocalReplacement.xLocalWordPush_single
attribute [local simp] QEC.Coding.BDL26RZDecoderAdapter.presentationOutput_coarse
attribute [local simp] QEC.Coding.BDL26RZDecoderAdapter.presentationOutput_components
attribute [local simp] QEC.Coding.BDL26RZDecoderAdapter.presentationOutput_correction
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzFace_card
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzQ_card
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzX_card
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzZ_card
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.map2Coord_canonicalBasis
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary0_canonicalBasis_apply
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1_canonicalBasis_apply
attribute [local simp] QEC.Coding.BDL26ReplacementSupport.fiberPart_apply
attribute [local simp] QEC.Coding.BDL26ReplacementSupport.rxQOutgoing_nonincident
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ0DoubleCylinderEdge_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ0DoubleCylinderVertex_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ0StarEdge_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ0StarVertex_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ0SubdivisionEdge_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ0SubdivisionVertex_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ4DoubleCylinderEdge_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ4DoubleCylinderVertex_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ4StarEdge_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ4StarVertex_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ4SubdivisionEdge_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ4SubdivisionVertex_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.qDoubleCylinderEndRestriction_apply
attribute [local simp] QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rxDualFace_left_inverse
attribute [local simp] QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rxDualFace_right_inverse
attribute [local simp] QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rzDualFace_left_inverse
attribute [local simp] QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rzDualFace_right_inverse
attribute [local simp] QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.transpose_transpose
attribute [local simp] QEC.Coding.BDL26XLocalConnectingWeight.copiedQ_image_copy
attribute [local simp] QEC.Coding.BDL26XLocalConnectingWeight.copiedQ_image_vertical
attribute [local simp] QEC.Coding.BDL26XLocalConnectingWeight.verticalZ_image_copy
attribute [local simp] QEC.Coding.BDL26XLocalConnectingWeight.verticalZ_image_vertical
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.originalBoundary_single
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.MultiscaleDecoder.RZCoarseGraining.coarseSyndrome_coe
attribute [local simp] QEC.Coding.MultiscaleDecoder.historicalZeroSyndromeInput_supportFitsRadiusTwo
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.interactionLength_sym2_mk
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_diag_not_mem_fixedGeneratorInteractions
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorOperator_adjoint_eq_self
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorSupport_eq_support
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.term_adjoint_eq_self
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
attribute [local simp] QEC.Locality.MarkedSeparatorSpine.exposedSide_stop
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_gridCellQubits_iff
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_gridOccupiedCells_iff
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff
attribute [local simp] QEC.Locality.centeredRectangleClippedGrowthRadius_zero
attribute [local simp] QEC.Locality.mem_centeredRectangleQubits_iff
attribute [local simp] QEC.Locality.mem_longInteractionEndpointQubits_iff
attribute [local simp] QEC.Locality.mem_longNeighborsOf_iff
attribute [local simp] QEC.Locality.mem_squareQubits_iff
attribute [local simp] QEC.Locality.squareGrowthRadius_succ_sub
attribute [local simp] QEC.Locality.squareGrowthRadius_zero
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
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
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
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26TransposedStoppedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26ReplacementCochainMaps
open BDL26RZMap1CoordinateBridge BDL26RXDecoderAdapter
open MultiscaleDecoder Coordinates
open scoped Classical BigOperators
def dualPresentation (S : OddScale) (n : Nat) : TannerSquarePresentation :=
  transposePresentation (state S n).presentation
abbrev DualX (S : OddScale) (depth : Nat) (i : LevelIndex depth) := (dualPresentation S i.val).X
abbrev DualQ (S : OddScale) (depth : Nat) (i : LevelIndex depth) := (dualPresentation S i.val).Q
abbrev DualZ (S : OddScale) (depth : Nat) (i : LevelIndex depth) := (dualPresentation S i.val).Z
def dualFamily (S : OddScale) (depth : Nat) :
    BDL26CochainFamily depth (DualX S depth) (DualQ S depth) (DualZ S depth) where
  complex := fun i => BDL26LevelTwoDecoder.presentationComplex (dualPresentation S i.val)
theorem dualFamily_coboundary0 (S : OddScale) (depth : Nat) (i : LevelIndex depth) :
    (dualFamily S depth).coboundary0 i = tannerCoboundary0 (dualPresentation S i.val) := by
  apply LinearMap.ext
  intro e
  funext q
  exact wordLinearMapTranspose_toLin'_apply _ e q
theorem dualFamily_coboundary1 (S : OddScale) (depth : Nat) (i : LevelIndex depth) :
    (dualFamily S depth).coboundary1 i = tannerCoboundary1 (dualPresentation S i.val) := by
  apply LinearMap.ext
  intro e
  funext z
  exact wordLinearMapTranspose_toLin'_apply _ e z
theorem conjugate_commutes
    {A B C D E F : Type} [Fintype A] [Fintype B] [Fintype C]
    [Fintype D] [Fintype E] [Fintype F]
    (d : Word BDL26Field A →ₗ[BDL26Field] Word BDL26Field B)
    (d' : Word BDL26Field C →ₗ[BDL26Field] Word BDL26Field D)
    (dt : Word BDL26Field E →ₗ[BDL26Field] Word BDL26Field F)
    (e : E ≃ C) (f : F ≃ D)
    (h : ∀ w, d' (wordEquiv e w) = wordEquiv f (dt w))
    (m : Word BDL26Field A →ₗ[BDL26Field] Word BDL26Field C)
    (n : Word BDL26Field B →ₗ[BDL26Field] Word BDL26Field D)
    (hm : d'.comp m = n.comp d) :
    dt.comp ((wordEquiv e).symm.toLinearMap.comp m) =
      ((wordEquiv f).symm.toLinearMap.comp n).comp d := by
  apply LinearMap.ext
  intro w
  apply (wordEquiv f).injective
  change wordEquiv f (dt ((wordEquiv e).symm (m w))) =
    wordEquiv f ((wordEquiv f).symm (n (d w)))
  rw [← h,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  exact LinearMap.congr_fun hm w
def dualRXMap0 (S : OddScale) (C : ConstructionState) :
    Word BDL26Field (transposePresentation C.presentation).X →ₗ[BDL26Field]
      Word BDL26Field (transposePresentation (rxState S C).presentation).X :=
  (wordEquiv (rxDualX C.presentation S)).symm.toLinearMap.comp
    (BDL26RZDecoderAdapter.presentationMap (transposePresentation C.presentation)
      (transposeTannerSquareAdmissibleV4 C.presentation C.admissible) S).map0
def dualRXMap1 (S : OddScale) (C : ConstructionState) :
    Word BDL26Field (transposePresentation C.presentation).Q →ₗ[BDL26Field]
      Word BDL26Field (transposePresentation (rxState S C).presentation).Q :=
  (wordEquiv (rxDualQ C.presentation S)).symm.toLinearMap.comp
    (BDL26RZDecoderAdapter.presentationMap (transposePresentation C.presentation)
      (transposeTannerSquareAdmissibleV4 C.presentation C.admissible) S).map1
def dualRXMap2 (S : OddScale) (C : ConstructionState) :
    Word BDL26Field (transposePresentation C.presentation).Z →ₗ[BDL26Field]
      Word BDL26Field (transposePresentation (rxState S C).presentation).Z :=
  (wordEquiv (rxDualZ C.presentation S)).symm.toLinearMap.comp
    (BDL26RZDecoderAdapter.presentationMap (transposePresentation C.presentation)
      (transposeTannerSquareAdmissibleV4 C.presentation C.admissible) S).map2
theorem dualRXMap_commutes0 (S : OddScale) (C : ConstructionState) :
    (tannerCoboundary0 (transposePresentation (rxState S C).presentation)).comp (dualRXMap0 S C) =
      (dualRXMap1 S C).comp (tannerCoboundary0 (transposePresentation C.presentation)) := by
  have hc := (BDL26RZDecoderAdapter.presentationMap (transposePresentation C.presentation)
      (transposeTannerSquareAdmissibleV4 C.presentation C.admissible) S).commutes_coboundary0
  rw [BDL26RZDecoderAdapter.presentationFamily_coboundary0,
    BDL26RZDecoderAdapter.presentationFamily_coboundary0] at hc
  exact conjugate_commutes _ _ _ (rxDualX C.presentation S)
    (rxDualQ C.presentation S)
    (rxDual_coboundary0 C.presentation C.admissible C.regular S) _ _ hc
theorem dualRXMap_commutes1 (S : OddScale) (C : ConstructionState) :
    (tannerCoboundary1 (transposePresentation (rxState S C).presentation)).comp (dualRXMap1 S C) =
      (dualRXMap2 S C).comp (tannerCoboundary1 (transposePresentation C.presentation)) := by
  have hc := (BDL26RZDecoderAdapter.presentationMap (transposePresentation C.presentation)
      (transposeTannerSquareAdmissibleV4 C.presentation C.admissible) S).commutes_coboundary1
  rw [BDL26RZDecoderAdapter.presentationFamily_coboundary1,
    BDL26RZDecoderAdapter.presentationFamily_coboundary1] at hc
  exact conjugate_commutes _ _ _ (rxDualQ C.presentation S)
    (rxDualZ C.presentation S)
    (rxDual_coboundary1 C.presentation C.admissible C.regular S) _ _ hc
def dualRZMap0 (S : OddScale) (C : ConstructionState) :
    Word BDL26Field (transposePresentation C.presentation).X →ₗ[BDL26Field]
      Word BDL26Field (transposePresentation (rzState S C).presentation).X :=
  (wordEquiv (rzDualX C.presentation S)).symm.toLinearMap.comp
    (BDL26RXDecoderAdapter.presentationMap (transposePresentation C.presentation)
      (transposeTannerSquareAdmissibleV4 C.presentation C.admissible) (transposeTannerSquareCellularRegular C.presentation C.regular) S).map0
def dualRZMap1 (S : OddScale) (C : ConstructionState) :
    Word BDL26Field (transposePresentation C.presentation).Q →ₗ[BDL26Field]
      Word BDL26Field (transposePresentation (rzState S C).presentation).Q :=
  (wordEquiv (rzDualQ C.presentation S)).symm.toLinearMap.comp
    (BDL26RXDecoderAdapter.presentationMap (transposePresentation C.presentation)
      (transposeTannerSquareAdmissibleV4 C.presentation C.admissible) (transposeTannerSquareCellularRegular C.presentation C.regular) S).map1
def dualRZMap2 (S : OddScale) (C : ConstructionState) :
    Word BDL26Field (transposePresentation C.presentation).Z →ₗ[BDL26Field]
      Word BDL26Field (transposePresentation (rzState S C).presentation).Z :=
  (wordEquiv (rzDualZ C.presentation S)).symm.toLinearMap.comp
    (BDL26RXDecoderAdapter.presentationMap (transposePresentation C.presentation)
      (transposeTannerSquareAdmissibleV4 C.presentation C.admissible) (transposeTannerSquareCellularRegular C.presentation C.regular) S).map2
theorem dualRZMap_commutes0 (S : OddScale) (C : ConstructionState) :
    (tannerCoboundary0 (transposePresentation (rzState S C).presentation)).comp (dualRZMap0 S C) =
      (dualRZMap1 S C).comp (tannerCoboundary0 (transposePresentation C.presentation)) := by
  have hc := (BDL26RXDecoderAdapter.presentationMap (transposePresentation C.presentation)
      (transposeTannerSquareAdmissibleV4 C.presentation C.admissible) (transposeTannerSquareCellularRegular C.presentation C.regular) S).commutes_coboundary0
  rw [BDL26RXDecoderAdapter.presentationFamily_coboundary0,
    BDL26RXDecoderAdapter.presentationFamily_coboundary0] at hc
  exact conjugate_commutes _ _ _ (rzDualX C.presentation S)
    (rzDualQ C.presentation S)
    (rzDual_coboundary0 C.presentation C.admissible C.regular S) _ _ hc
theorem dualRZMap_commutes1 (S : OddScale) (C : ConstructionState) :
    (tannerCoboundary1 (transposePresentation (rzState S C).presentation)).comp (dualRZMap1 S C) =
      (dualRZMap2 S C).comp (tannerCoboundary1 (transposePresentation C.presentation)) := by
  have hc := (BDL26RXDecoderAdapter.presentationMap (transposePresentation C.presentation)
      (transposeTannerSquareAdmissibleV4 C.presentation C.admissible) (transposeTannerSquareCellularRegular C.presentation C.regular) S).commutes_coboundary1
  rw [BDL26RXDecoderAdapter.presentationFamily_coboundary1,
    BDL26RXDecoderAdapter.presentationFamily_coboundary1] at hc
  exact conjugate_commutes _ _ _ (rzDualQ C.presentation S)
    (rzDualZ C.presentation S)
    (rzDual_coboundary1 C.presentation C.admissible C.regular S) _ _ hc
def dualNextMap0 (S : OddScale) (n : Nat) (C : ConstructionState) :
    Word BDL26Field (transposePresentation C.presentation).X →ₗ[BDL26Field]
      Word BDL26Field (transposePresentation (nextState S n C).presentation).X := by
  by_cases h : n % 2 = 0
  · exact Eq.mpr (congrArg (fun D : ConstructionState =>
      Word BDL26Field (transposePresentation C.presentation).X →ₗ[BDL26Field]
        Word BDL26Field (transposePresentation D.presentation).X)
        (show nextState S n C = rxState S C from if_pos h)) (dualRXMap0 S C)
  · exact Eq.mpr (congrArg (fun D : ConstructionState =>
      Word BDL26Field (transposePresentation C.presentation).X →ₗ[BDL26Field]
        Word BDL26Field (transposePresentation D.presentation).X)
        (show nextState S n C = rzState S C from if_neg h)) (dualRZMap0 S C)
def dualNextMap1 (S : OddScale) (n : Nat) (C : ConstructionState) :
    Word BDL26Field (transposePresentation C.presentation).Q →ₗ[BDL26Field]
      Word BDL26Field (transposePresentation (nextState S n C).presentation).Q := by
  by_cases h : n % 2 = 0
  · exact Eq.mpr (congrArg (fun D : ConstructionState =>
      Word BDL26Field (transposePresentation C.presentation).Q →ₗ[BDL26Field]
        Word BDL26Field (transposePresentation D.presentation).Q)
        (show nextState S n C = rxState S C from if_pos h)) (dualRXMap1 S C)
  · exact Eq.mpr (congrArg (fun D : ConstructionState =>
      Word BDL26Field (transposePresentation C.presentation).Q →ₗ[BDL26Field]
        Word BDL26Field (transposePresentation D.presentation).Q)
        (show nextState S n C = rzState S C from if_neg h)) (dualRZMap1 S C)
def dualNextMap2 (S : OddScale) (n : Nat) (C : ConstructionState) :
    Word BDL26Field (transposePresentation C.presentation).Z →ₗ[BDL26Field]
      Word BDL26Field (transposePresentation (nextState S n C).presentation).Z := by
  by_cases h : n % 2 = 0
  · exact Eq.mpr (congrArg (fun D : ConstructionState =>
      Word BDL26Field (transposePresentation C.presentation).Z →ₗ[BDL26Field]
        Word BDL26Field (transposePresentation D.presentation).Z)
        (show nextState S n C = rxState S C from if_pos h)) (dualRXMap2 S C)
  · exact Eq.mpr (congrArg (fun D : ConstructionState =>
      Word BDL26Field (transposePresentation C.presentation).Z →ₗ[BDL26Field]
        Word BDL26Field (transposePresentation D.presentation).Z)
        (show nextState S n C = rzState S C from if_neg h)) (dualRZMap2 S C)
theorem transport_commutes0 (C D E : ConstructionState) (h : D = E)
    (m : Word BDL26Field (transposePresentation C.presentation).X →ₗ[BDL26Field]
      Word BDL26Field (transposePresentation E.presentation).X)
    (n : Word BDL26Field (transposePresentation C.presentation).Q →ₗ[BDL26Field]
      Word BDL26Field (transposePresentation E.presentation).Q)
    (hc : (tannerCoboundary0 (transposePresentation E.presentation)).comp m =
      n.comp (tannerCoboundary0 (transposePresentation C.presentation))) :
    (tannerCoboundary0 (transposePresentation D.presentation)).comp
      (Eq.mpr (congrArg (fun B : ConstructionState =>
        Word BDL26Field (transposePresentation C.presentation).X →ₗ[BDL26Field]
          Word BDL26Field (transposePresentation B.presentation).X) h) m) =
      (Eq.mpr (congrArg (fun B : ConstructionState =>
        Word BDL26Field (transposePresentation C.presentation).Q →ₗ[BDL26Field]
          Word BDL26Field (transposePresentation B.presentation).Q) h) n).comp
        (tannerCoboundary0 (transposePresentation C.presentation)) := by
  cases h
  exact hc
theorem dualNextMap_commutes0 (S : OddScale) (n : Nat) (C : ConstructionState) :
    (tannerCoboundary0 (transposePresentation (nextState S n C).presentation)).comp
      (dualNextMap0 S n C) =
    (dualNextMap1 S n C).comp (tannerCoboundary0 (transposePresentation C.presentation)) := by
  by_cases h : n % 2 = 0
  · have ht := transport_commutes0 C (nextState S n C) (rxState S C)
      (show nextState S n C = rxState S C from if_pos h) _ _ (dualRXMap_commutes0 S C)
    simpa only [dualNextMap0,dualNextMap1,dif_pos h] using ht
  · have ht := transport_commutes0 C (nextState S n C) (rzState S C)
      (show nextState S n C = rzState S C from if_neg h) _ _ (dualRZMap_commutes0 S C)
    simpa only [dualNextMap0,dualNextMap1,dif_neg h] using ht
theorem transport_commutes1 (C D E : ConstructionState) (h : D = E)
    (m : Word BDL26Field (transposePresentation C.presentation).Q →ₗ[BDL26Field]
      Word BDL26Field (transposePresentation E.presentation).Q)
    (n : Word BDL26Field (transposePresentation C.presentation).Z →ₗ[BDL26Field]
      Word BDL26Field (transposePresentation E.presentation).Z)
    (hc : (tannerCoboundary1 (transposePresentation E.presentation)).comp m =
      n.comp (tannerCoboundary1 (transposePresentation C.presentation))) :
    (tannerCoboundary1 (transposePresentation D.presentation)).comp
      (Eq.mpr (congrArg (fun B : ConstructionState =>
        Word BDL26Field (transposePresentation C.presentation).Q →ₗ[BDL26Field]
          Word BDL26Field (transposePresentation B.presentation).Q) h) m) =
      (Eq.mpr (congrArg (fun B : ConstructionState =>
        Word BDL26Field (transposePresentation C.presentation).Z →ₗ[BDL26Field]
          Word BDL26Field (transposePresentation B.presentation).Z) h) n).comp
        (tannerCoboundary1 (transposePresentation C.presentation)) := by
  cases h
  exact hc
theorem dualNextMap_commutes1 (S : OddScale) (n : Nat) (C : ConstructionState) :
    (tannerCoboundary1 (transposePresentation (nextState S n C).presentation)).comp
      (dualNextMap1 S n C) =
    (dualNextMap2 S n C).comp (tannerCoboundary1 (transposePresentation C.presentation)) := by
  by_cases h : n % 2 = 0
  · have ht := transport_commutes1 C (nextState S n C) (rxState S C)
      (show nextState S n C = rxState S C from if_pos h) _ _ (dualRXMap_commutes1 S C)
    simpa only [dualNextMap1,dualNextMap2,dif_pos h] using ht
  · have ht := transport_commutes1 C (nextState S n C) (rzState S C)
      (show nextState S n C = rzState S C from if_neg h) _ _ (dualRZMap_commutes1 S C)
    simpa only [dualNextMap1,dualNextMap2,dif_neg h] using ht
def dualEdgeMap (S : OddScale) (depth : Nat) (i : StepIndex depth) :
    BDL26CochainMap (dualFamily S depth) i where
  map0 := dualNextMap0 S i.val (state S i.val)
  map1 := dualNextMap1 S i.val (state S i.val)
  map2 := dualNextMap2 S i.val (state S i.val)
  commutes_coboundary0 := by
    rw [dualFamily_coboundary0,dualFamily_coboundary0]
    exact dualNextMap_commutes0 S i.val (state S i.val)
  commutes_coboundary1 := by
    rw [dualFamily_coboundary1,dualFamily_coboundary1]
    exact dualNextMap_commutes1 S i.val (state S i.val)
def dualDecoderData (S : OddScale) (depth : Nat) :
    BDL26DecoderData depth (DualX S depth) (DualQ S depth) (DualZ S depth) where
  family := dualFamily S depth
  rxMap := dualEdgeMap S depth
  rzMap := dualEdgeMap S depth
@[simp] theorem dualDecoderData_selectedMap (S : OddScale) (depth : Nat)
    (i : StepIndex depth) :
    (dualDecoderData S depth).selectedMap i = dualEdgeMap S depth i := by
  unfold BDL26DecoderData.selectedMap
  split <;> rfl
theorem inverse_intertwines {A B C D : Type}
    (e : A ≃ B) (f : C ≃ D)
    (d : Word BDL26Field A →ₗ[BDL26Field] Word BDL26Field C)
    (d' : Word BDL26Field B →ₗ[BDL26Field] Word BDL26Field D)
    (h : ∀ w, d' (wordEquiv e w) = wordEquiv f (d w))
    (w : Word BDL26Field B) :
    d ((wordEquiv e).symm w) = (wordEquiv f).symm (d' w) := by
  apply (wordEquiv f).injective
  rw [← h,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
section CoordinateOutput
variable {d e : Nat}
variable {A0 A1 A2 : LevelIndex d → Type} {B0 B1 B2 : LevelIndex e → Type}
variable [∀ i, Fintype (A0 i)] [∀ i, Fintype (A1 i)] [∀ i, Fintype (A2 i)]
variable [∀ i, Fintype (B0 i)] [∀ i, Fintype (B1 i)] [∀ i, Fintype (B2 i)]
def coordinateOutput
    (D : BDL26DecoderData d A0 A1 A2) (E : BDL26DecoderData e B0 B1 B2)
    (i : StepIndex d) (j : StepIndex e)
    (q : A1 i.succ ≃ B1 j.succ) (z : A2 i.succ ≃ B2 j.succ)
    (bq : A1 i.castSucc ≃ B1 j.castSucc) (bz : A2 i.castSucc ≃ B2 j.castSucc)
    (ht : ∀ w, E.family.coboundary1 j.succ (wordEquiv q w) =
      wordEquiv z (D.family.coboundary1 i.succ w))
    (hb : ∀ w, E.family.coboundary1 j.castSucc (wordEquiv bq w) =
      wordEquiv bz (D.family.coboundary1 i.castSucc w))
    (hm : ∀ w, (E.selectedMap j).map2 (wordEquiv bz w) =
      wordEquiv z ((D.selectedMap i).map2 w))
    (O : AssemblyStepOutput D i) : AssemblyStepOutput E j := by
  let input : E.family.Syndrome j.succ := ⟨wordEquiv z O.input.val,by
    obtain ⟨w,hw⟩ := O.input.property
    exact ⟨wordEquiv q w,by rw [ht,hw]⟩⟩
  let coarse : E.family.Syndrome j.castSucc := ⟨wordEquiv bz O.coarse.val,by
    obtain ⟨w,hw⟩ := O.coarse.property
    exact ⟨wordEquiv bq w,by rw [hb,hw]⟩⟩
  apply AssemblyStepOutput.ofComponents input coarse (wordEquiv q O.correction)
    (O.localComponents.map (wordEquiv q))
  · change wordEquiv z O.input.val = _
    rw [ht,hm,← map_add,O.relation]
  · rw [O.correction_decomposition]
    have hsum (l : List (D.family.Correction i.succ)) :
        wordEquiv q l.sum = (l.map (wordEquiv q)).sum := by
      induction l with
      | nil => simp
      | cons a l ih => simp only [List.sum_cons,List.map_cons,map_add,ih]
    exact hsum _
end CoordinateOutput
theorem cast_tanner_coboundary1 (P R : TannerSquarePresentation) (h : P = R)
    (w : Word BDL26Field R.Q) :
    tannerCoboundary1 P (wordEquiv (Equiv.cast (congrArg TannerSquarePresentation.Q h).symm) w) =
      wordEquiv (Equiv.cast (congrArg TannerSquarePresentation.Z h).symm)
        (tannerCoboundary1 R w) := by
  cases h
  rfl
theorem transport_map_apply (C D E : ConstructionState) (h : D = E)
    (m : Word BDL26Field (transposePresentation C.presentation).Z →ₗ[BDL26Field]
      Word BDL26Field (transposePresentation E.presentation).Z)
    (w : Word BDL26Field (transposePresentation C.presentation).Z) :
    (Eq.mpr (congrArg (fun B : ConstructionState =>
      Word BDL26Field (transposePresentation C.presentation).Z →ₗ[BDL26Field]
        Word BDL26Field (transposePresentation B.presentation).Z) h) m) w =
      wordEquiv (Equiv.cast (congrArg (fun B : ConstructionState =>
        (transposePresentation B.presentation).Z) h).symm) (m w) := by
  cases h
  rfl
theorem dualNextMap2_rx_apply (S : OddScale) (n : Nat)
    (C : ConstructionState) (h : n % 2 = 0)
    (w : Word BDL26Field (transposePresentation C.presentation).Z) :
    dualNextMap2 S n C w =
      wordEquiv (Equiv.cast (congrArg (fun D : ConstructionState =>
        (transposePresentation D.presentation).Z)
        (show nextState S n C = rxState S C from if_pos h)).symm) (dualRXMap2 S C w) := by
  unfold dualNextMap2
  split
  · exact transport_map_apply C (nextState S n C) (rxState S C)
      (show nextState S n C = rxState S C from if_pos h) (dualRXMap2 S C) w
  · contradiction
theorem dualNextMap2_rz_apply (S : OddScale) (n : Nat)
    (C : ConstructionState) (h : ¬n % 2 = 0)
    (w : Word BDL26Field (transposePresentation C.presentation).Z) :
    dualNextMap2 S n C w =
      wordEquiv (Equiv.cast (congrArg (fun D : ConstructionState =>
        (transposePresentation D.presentation).Z)
        (show nextState S n C = rzState S C from if_neg h)).symm) (dualRZMap2 S C w) := by
  unfold dualNextMap2
  split
  · contradiction
  · exact transport_map_apply C (nextState S n C) (rzState S C)
      (show nextState S n C = rzState S C from if_neg h) (dualRZMap2 S C) w
theorem dualStateSuccRX (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) : state S (i.val + 1) = rxState S (state S i.val) := by
  change nextState S i.val (state S i.val) = _
  exact if_pos h
def dualRXTopQ (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) :
    (BDL26RZDecoderAdapter.presentationAt (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S (1 : LevelIndex 1)).Q ≃
      (dualPresentation S i.succ.val).Q :=
  (rxDualQ (state S i.val).presentation S).symm.trans
    (Equiv.cast (congrArg (fun C : ConstructionState =>
      (transposePresentation C.presentation).Q) (dualStateSuccRX S depth i h)).symm)
def dualRXTopZ (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) :
    (BDL26RZDecoderAdapter.presentationAt (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S (1 : LevelIndex 1)).Z ≃
      (dualPresentation S i.succ.val).Z :=
  (rxDualZ (state S i.val).presentation S).symm.trans
    (Equiv.cast (congrArg (fun C : ConstructionState =>
      (transposePresentation C.presentation).Z) (dualStateSuccRX S depth i h)).symm)
theorem dualRXTop_coboundary1 (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (h : i.val % 2 = 0)
    (w : (BDL26RZDecoderAdapter.presentationFamily (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S).Correction (1 : LevelIndex 1)) :
    (dualFamily S depth).coboundary1 i.succ (wordEquiv (dualRXTopQ S depth i h) w) =
      wordEquiv (dualRXTopZ S depth i h)
        ((BDL26RZDecoderAdapter.presentationFamily (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S).coboundary1 (1 : LevelIndex 1) w) := by
  have hleft := LinearMap.congr_fun (dualFamily_coboundary1 S depth i.succ)
    (wordEquiv (dualRXTopQ S depth i h) w)
  have hright := congrArg (wordEquiv (dualRXTopZ S depth i h))
    (LinearMap.congr_fun (BDL26RZDecoderAdapter.presentationFamily_coboundary1 (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S
      (1 : LevelIndex 1)) w)
  refine hleft.trans ?_
  refine Eq.trans ?_ hright.symm
  have hc := inverse_intertwines (rxDualQ (state S i.val).presentation S)
    (rxDualZ (state S i.val).presentation S) _ _
    (rxDual_coboundary1 (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S) w
  let ht := congrArg (fun C : ConstructionState => transposePresentation C.presentation)
    (dualStateSuccRX S depth i h)
  change tannerCoboundary1 (dualPresentation S i.succ.val)
      (wordEquiv (Equiv.cast (congrArg TannerSquarePresentation.Q ht).symm)
        ((wordEquiv (rxDualQ (state S i.val).presentation S)).symm w)) =
    wordEquiv (Equiv.cast (congrArg TannerSquarePresentation.Z ht).symm)
      ((wordEquiv (rxDualZ (state S i.val).presentation S)).symm
        (tannerCoboundary1 _ w))
  exact (cast_tanner_coboundary1 _ _ ht
    ((wordEquiv (rxDualQ (state S i.val).presentation S)).symm w)).trans
      (congrArg (wordEquiv (Equiv.cast (congrArg TannerSquarePresentation.Z ht).symm)) hc)
theorem dualRXTop_map2 (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (h : i.val % 2 = 0)
    (w : Word BDL26Field (dualPresentation S i.val).Z) :
    ((dualDecoderData S depth).selectedMap i).map2 w =
      wordEquiv (dualRXTopZ S depth i h)
        (((BDL26RZDecoderAdapter.presentationDecoderData (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S).selectedMap (0 : StepIndex 1)).map2 w) := by
  have hselected := congrArg
    (fun M : BDL26CochainMap (dualFamily S depth) i => M.map2 w)
    (dualDecoderData_selectedMap S depth i)
  refine hselected.trans ?_
  change dualNextMap2 S i.val (state S i.val) w =
    wordEquiv (dualRXTopZ S depth i h)
      ((BDL26RZDecoderAdapter.presentationMap (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S).map2 w)
  exact (dualNextMap2_rx_apply S i.val (state S i.val) h w).trans (by rfl)
def dualRXMaterializedInput (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (sigma : (dualFamily S depth).Syndrome i.succ) :
    (BDL26RZDecoderAdapter.presentationFamily (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S).Syndrome (1 : LevelIndex 1) := by
  exact ⟨(wordEquiv (dualRXTopZ S depth i h)).symm sigma.val,by
      obtain ⟨w,hw⟩ := sigma.property
      refine ⟨(wordEquiv (dualRXTopQ S depth i h)).symm w,?_⟩
      apply (wordEquiv (dualRXTopZ S depth i h)).injective
      rw [← dualRXTop_coboundary1,LinearEquiv.apply_symm_apply,hw,
        LinearEquiv.apply_symm_apply]⟩
def dualRXStepOutput (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (sigma : (dualFamily S depth).Syndrome i.succ) :
    AssemblyStepOutput (dualDecoderData S depth) i := by
  let localInput := dualRXMaterializedInput S depth i h sigma
  let O := BDL26RZDecoderAdapter.presentationOutput (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S localInput
  exact coordinateOutput (BDL26RZDecoderAdapter.presentationDecoderData (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S)
    (dualDecoderData S depth) (0 : StepIndex 1) i
    (dualRXTopQ S depth i h) (dualRXTopZ S depth i h) (Equiv.refl _) (Equiv.refl _)
    (dualRXTop_coboundary1 S depth i h)
    (by
      intro w
      change (dualFamily S depth).coboundary1 i.castSucc w =
        (BDL26RZDecoderAdapter.presentationFamily (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S).coboundary1
          (0 : LevelIndex 1) w
      exact (LinearMap.congr_fun (dualFamily_coboundary1 S depth i.castSucc) w).trans
        (LinearMap.congr_fun (BDL26RZDecoderAdapter.presentationFamily_coboundary1 (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S
          (0 : LevelIndex 1)) w).symm)
    (by intro w; exact dualRXTop_map2 S depth i h w) O
@[simp] theorem dualRXStepOutput_input (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (h : i.val % 2 = 0) (sigma : (dualFamily S depth).Syndrome i.succ) :
    (dualRXStepOutput S depth i h sigma).input = sigma := by
  apply Subtype.ext
  change wordEquiv (dualRXTopZ S depth i h)
    ((wordEquiv (dualRXTopZ S depth i h)).symm sigma.val) = sigma.val
  exact LinearEquiv.apply_symm_apply _ _
theorem dualStateSuccRZ (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : ¬i.val % 2 = 0) : state S (i.val + 1) = rzState S (state S i.val) := by
  change nextState S i.val (state S i.val) = _
  exact if_neg h
def dualRZTopQ (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : ¬i.val % 2 = 0) :
    (BDL26RXDecoderAdapter.presentationAt (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S (1 : LevelIndex 1)).Q ≃
      (dualPresentation S i.succ.val).Q :=
  (rzDualQ (state S i.val).presentation S).symm.trans
    (Equiv.cast (congrArg (fun C : ConstructionState =>
      (transposePresentation C.presentation).Q) (dualStateSuccRZ S depth i h)).symm)
def dualRZTopZ (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : ¬i.val % 2 = 0) :
    (BDL26RXDecoderAdapter.presentationAt (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S (1 : LevelIndex 1)).Z ≃
      (dualPresentation S i.succ.val).Z :=
  (rzDualZ (state S i.val).presentation S).symm.trans
    (Equiv.cast (congrArg (fun C : ConstructionState =>
      (transposePresentation C.presentation).Z) (dualStateSuccRZ S depth i h)).symm)
theorem dualRZTop_coboundary1 (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (h : ¬i.val % 2 = 0)
    (w : (BDL26RXDecoderAdapter.presentationFamily (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S).Correction (1 : LevelIndex 1)) :
    (dualFamily S depth).coboundary1 i.succ (wordEquiv (dualRZTopQ S depth i h) w) =
      wordEquiv (dualRZTopZ S depth i h)
        ((BDL26RXDecoderAdapter.presentationFamily (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S).coboundary1 (1 : LevelIndex 1) w) := by
  have hleft := LinearMap.congr_fun (dualFamily_coboundary1 S depth i.succ)
    (wordEquiv (dualRZTopQ S depth i h) w)
  have hright := congrArg (wordEquiv (dualRZTopZ S depth i h))
    (LinearMap.congr_fun (BDL26RXDecoderAdapter.presentationFamily_coboundary1 (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S
      (1 : LevelIndex 1)) w)
  refine hleft.trans ?_
  refine Eq.trans ?_ hright.symm
  have hc := inverse_intertwines (rzDualQ (state S i.val).presentation S)
    (rzDualZ (state S i.val).presentation S) _ _
    (rzDual_coboundary1 (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S) w
  let ht := congrArg (fun C : ConstructionState => transposePresentation C.presentation)
    (dualStateSuccRZ S depth i h)
  change tannerCoboundary1 (dualPresentation S i.succ.val)
      (wordEquiv (Equiv.cast (congrArg TannerSquarePresentation.Q ht).symm)
        ((wordEquiv (rzDualQ (state S i.val).presentation S)).symm w)) =
    wordEquiv (Equiv.cast (congrArg TannerSquarePresentation.Z ht).symm)
      ((wordEquiv (rzDualZ (state S i.val).presentation S)).symm
        (tannerCoboundary1 _ w))
  exact (cast_tanner_coboundary1 _ _ ht
    ((wordEquiv (rzDualQ (state S i.val).presentation S)).symm w)).trans
      (congrArg (wordEquiv (Equiv.cast (congrArg TannerSquarePresentation.Z ht).symm)) hc)
theorem dualRZTop_map2 (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (h : ¬i.val % 2 = 0)
    (w : Word BDL26Field (dualPresentation S i.val).Z) :
    ((dualDecoderData S depth).selectedMap i).map2 w =
      wordEquiv (dualRZTopZ S depth i h)
        (((BDL26RXDecoderAdapter.presentationDecoderData (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S).selectedMap (0 : StepIndex 1)).map2 w) := by
  have hselected := congrArg
    (fun M : BDL26CochainMap (dualFamily S depth) i => M.map2 w)
    (dualDecoderData_selectedMap S depth i)
  refine hselected.trans ?_
  change dualNextMap2 S i.val (state S i.val) w =
    wordEquiv (dualRZTopZ S depth i h)
      ((BDL26RXDecoderAdapter.presentationMap (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S).map2 w)
  exact (dualNextMap2_rz_apply S i.val (state S i.val) h w).trans (by rfl)
def dualRZMaterializedInput (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : ¬i.val % 2 = 0) (sigma : (dualFamily S depth).Syndrome i.succ) :
    (BDL26RXDecoderAdapter.presentationFamily (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S).Syndrome (1 : LevelIndex 1) := by
  exact ⟨(wordEquiv (dualRZTopZ S depth i h)).symm sigma.val,by
      obtain ⟨w,hw⟩ := sigma.property
      refine ⟨(wordEquiv (dualRZTopQ S depth i h)).symm w,?_⟩
      apply (wordEquiv (dualRZTopZ S depth i h)).injective
      rw [← dualRZTop_coboundary1,LinearEquiv.apply_symm_apply,hw,
        LinearEquiv.apply_symm_apply]⟩
def dualRZStepOutput (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : ¬i.val % 2 = 0) (sigma : (dualFamily S depth).Syndrome i.succ) :
    AssemblyStepOutput (dualDecoderData S depth) i := by
  let localInput := dualRZMaterializedInput S depth i h sigma
  let O := BDL26RXDecoderAdapter.presentationOutput (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S localInput
  exact coordinateOutput (BDL26RXDecoderAdapter.presentationDecoderData (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S)
    (dualDecoderData S depth) (0 : StepIndex 1) i
    (dualRZTopQ S depth i h) (dualRZTopZ S depth i h) (Equiv.refl _) (Equiv.refl _)
    (dualRZTop_coboundary1 S depth i h)
    (by
      intro w
      change (dualFamily S depth).coboundary1 i.castSucc w =
        (BDL26RXDecoderAdapter.presentationFamily (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S).coboundary1
          (0 : LevelIndex 1) w
      exact (LinearMap.congr_fun (dualFamily_coboundary1 S depth i.castSucc) w).trans
        (LinearMap.congr_fun (BDL26RXDecoderAdapter.presentationFamily_coboundary1 (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S
          (0 : LevelIndex 1)) w).symm)
    (by intro w; exact dualRZTop_map2 S depth i h w) O
@[simp] theorem dualRZStepOutput_input (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (h : ¬i.val % 2 = 0) (sigma : (dualFamily S depth).Syndrome i.succ) :
    (dualRZStepOutput S depth i h sigma).input = sigma := by
  apply Subtype.ext
  change wordEquiv (dualRZTopZ S depth i h)
    ((wordEquiv (dualRZTopZ S depth i h)).symm sigma.val) = sigma.val
  exact LinearEquiv.apply_symm_apply _ _
def dualStepOutput (S : OddScale) (depth : Nat) (i : StepIndex depth) :
    AssemblyStep (dualDecoderData S depth) i := fun sigma =>
  if h : i.val % 2 = 0 then dualRXStepOutput S depth i h sigma
  else dualRZStepOutput S depth i h sigma
theorem dualStepOutput_relation (S : OddScale) (depth : Nat) (i : StepIndex depth) :
    AssemblyStepRelation (dualDecoderData S depth) i (dualStepOutput S depth i) where
  input_eq := by
    intro sigma
    change (dualStepOutput S depth i sigma).input = sigma
    unfold dualStepOutput
    split
    · exact dualRXStepOutput_input S depth i _ sigma
    · exact dualRZStepOutput_input S depth i _ sigma
  relation := fun sigma => (dualStepOutput S depth i sigma).relation
def dualAboveTwoSteps (S : OddScale) (n : Nat) :
    LevelTwoHistory.AboveTwoSteps (dualDecoderData S (n + 2)) where
  step := fun i _ => dualStepOutput S (n + 2) i
  relation := fun i _ => dualStepOutput_relation S (n + 2) i
end QEC.Coding.BDL26TransposedStoppedDecoder
end


