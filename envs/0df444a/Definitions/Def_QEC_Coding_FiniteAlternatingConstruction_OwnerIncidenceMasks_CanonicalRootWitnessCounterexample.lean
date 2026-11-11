-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
-- name    : QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T04:57:30.445636+00:00
-- url     : https://prove2.me/theorems/4451ac46-868f-478f-a31e-3eb62290c7b6
-- title:
--   Canonical Root Witness Counterexample
-- statement:
--   Definitions and structural lemmas for Canonical Root Witness Counterexample, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_physicalMarks_base
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_physicalMarks_step
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_correctionRegion_mem
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_syndromeRegion_mem
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
import Theorems.Thm_QEC_Coding_BDL26IndexedDecoder_selectedMap_eq
import Theorems.Thm_QEC_Coding_BDL26OwnerParentObstruction_rzMap2_apply
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_map2_diagonal
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
import Theorems.Thm_QEC_Coding_BDL26TopOwnerIsolation_markedAdjacent_iff
import Theorems.Thm_QEC_Coding_BDL26UniformTopOwnerIsolation_markedAdjacent_iff
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.BDL26CanonicalHistoryMarks.physicalMarks_base
attribute [local simp] QEC.Coding.BDL26CanonicalHistoryMarks.physicalMarks_step
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
attribute [local simp] QEC.Coding.BDL26TopOwnerIsolation.markedAdjacent_iff
attribute [local simp] QEC.Coding.BDL26UniformTopOwnerIsolation.markedAdjacent_iff
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
attribute [local irreducible] QEC.Coding.BDL26CanonicalHistoryMarks.rootComponent
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26ReplacementSupport
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable section
abbrev CF (S : OddScale) := (indexedDecoderData S 4).family
abbrev level3 : LevelIndex 4 := (2 : StepIndex 4).succ
abbrev level4 : LevelIndex 4 := (3 : StepIndex 4).succ
def zVertex (S : OddScale) (n : Nat) (z : (state S n).presentation.Z) :
    GraphVertex S (n+1) := @Vertex.z (state S n).presentation z
def actualTopNode (S : OddScale) (v : GraphVertex S 4) :
    BDL26CanonicalHistoryMarks.Node S 2 := ⟨(4 : LevelIndex 4),v⟩
def actualMidNode (S : OddScale) (v : GraphVertex S 3) :
    BDL26CanonicalHistoryMarks.Node S 2 := ⟨(3 : LevelIndex 4),v⟩
def actualBaseNode (S : OddScale) (v : GraphVertex S 2) :
    BDL26CanonicalHistoryMarks.Node S 2 := ⟨(2 : LevelIndex 4),v⟩
abbrev Word3 (S : OddScale) := (CF S).Cochain2 level3
abbrev Correction3 (S : OddScale) := (CF S).Cochain1 level3
noncomputable abbrev A (S : OddScale) := rxData S 4 (2 : StepIndex 4) (by decide)
noncomputable abbrev LX (S : OddScale) := rxLx S 4 (2 : StepIndex 4) (by decide)
noncomputable abbrev LQ (S : OddScale) := rxLq S 4 (2 : StepIndex 4) (by decide)
noncomputable abbrev d3 (S : OddScale) := (CF S).coboundary1 level3
theorem CF_coboundary1 (S : OddScale) (i : LevelIndex 4) :
    (CF S).coboundary1 i = BDL26RZMap1CoordinateBridge.tannerCoboundary1 (state S i.val).presentation :=
  indexedFamily_coboundary1 S 4 i
theorem sum_single_value {I : Type} [Fintype I] [DecidableEq I]
    (f : I → BDL26Field) (a : I) (hz : ∀ b, b ≠ a → f b = 0) :
    (∑ b, f b) = f a := by
  exact Finset.sum_eq_single a (fun b _hb hba => hz b hba) (by simp)
noncomputable def selectedWord {I : Type} (P : I → Prop) [DecidablePred P]
    (word : I → BDL26Field) : I → BDL26Field :=
  fun p => if P p then word p else 0
abbrev LocalQWord (S : OddScale) (q : (state S 2).presentation.Q) :=
  Word BDL26Field (LocalRegionIndex ((LQ S).correctionRegion q))
abbrev LocalQSyndrome (S : OddScale) (q : (state S 2).presentation.Q) :=
  Word BDL26Field (LocalRegionIndex ((LQ S).syndromeRegion q))
noncomputable def terminalVertex (S : OddScale) (q : (state S 2).presentation.Q)
    (z : (state S 2).presentation.Z) (hqz : (state S 2).presentation.qz q z = true)
    (b : Fin 2) : LocalRegionIndex ((LQ S).correctionRegion q) :=
  rxQVertexEquiv S 4 (2 : StepIndex 4) (by decide) q
    (b, Sum.inl (Sum.inr ⟨z,hqz⟩))
noncomputable def terminalIndicator (S : OddScale) (q : (state S 2).presentation.Q)
    (z : (state S 2).presentation.Z) (hqz : (state S 2).presentation.qz q z = true) :
    LocalQWord S q :=
  fun v => if v = terminalVertex S q z hqz 0 then 1 else 0
noncomputable def terminalSyndrome (S : OddScale) (q : (state S 2).presentation.Q)
    (z : (state S 2).presentation.Z) (hqz : (state S 2).presentation.qz q z = true) :
    LocalQSyndrome S q :=
  (A S).contract.rx_local_complexes.cqDelta1 q (terminalIndicator S q z hqz)
noncomputable def actualQSection (S : OddScale) (q : (state S 2).presentation.Q)
    (t : LocalQSyndrome S q)
    (ht : t ∈ LinearMap.range ((A S).contract.rx_local_complexes.cqDelta1 q)) :
    LocalQWord S q :=
  Classical.choose ((A S).contract.local_boundary_weight_budgets.cq q t ht)
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
abbrev seedQ (S : OddScale) : FamilyQ S 4 (0 : LevelIndex 4) := baseFaceQ 0 0
abbrev seedZ (S : OddScale) : FamilyZ S 4 (0 : LevelIndex 4) := baseFaceZ 0
noncomputable def seedError (S : OddScale) :
    (CF S).Correction (0 : LevelIndex 4) :=
  fun q => if q = seedQ S then 1 else 0
noncomputable def nu0 (S : OddScale) :
    (CF S).Syndrome (0 : LevelIndex 4) :=
  ⟨(CF S).coboundary1 0 (seedError S), ⟨seedError S,rfl⟩⟩
noncomputable def nu1 (S : OddScale) :
    (CF S).Syndrome (1 : LevelIndex 4) :=
  ((indexedDecoderData S 4).selectedMap (0 : StepIndex 4)).mapSyndrome (nu0 S)
noncomputable def gamma2 (S : OddScale) :
    (BDL26CanonicalHistoryMarks.Data S 2).family.Syndrome (0 : LevelIndex 2) :=
  BDL26RZDecoderAdapter.embeddedSyndrome S 4 (1 : StepIndex 4) (nu1 S)
noncomputable def baseRetainedZ (S : OddScale) : FamilyZ S 4 (1 : LevelIndex 4) :=
  (rxData S 4 (0 : StepIndex 4) (by decide)).induced.zPairEquiv (seedZ S,0) |>.val
noncomputable def r2 (S : OddScale) : FamilyZ S 4 (2 : LevelIndex 4) :=
  ⟨baseRetainedZ S,
    rzMap1ZRoot (state S 1).presentation (state S 1).admissible (baseRetainedZ S) S⟩
noncomputable def E2 (S : OddScale) := actualBaseDecode S 2 (gamma2 S)
theorem nu0_at_seed (S : OddScale) : (nu0 S).val (seedZ S) = 1 := by
  classical
  have hi : (state S 0).presentation.qz (seedQ S) (seedZ S) = true :=
    baseTannerSquarePresentation.data.faceQ_qz (0 : BaseFace) 0
  change (CF S).coboundary1 0 (seedError S) (seedZ S) = 1
  rw [CF_coboundary1]
  change (∑ q : FamilyQ S 4 (0 : LevelIndex 4),
    seedError S q * if (state S 0).presentation.qz q (seedZ S) = true then 1 else 0) = 1
  have hs := sum_single_value
    (fun q : FamilyQ S 4 (0 : LevelIndex 4) =>
      seedError S q * if (state S 0).presentation.qz q (seedZ S) = true then 1 else 0)
    (seedQ S) (by intro q hq; simp [seedError,hq])
  exact hs.trans (by simp [seedError,hi])
theorem nu1_at_retained (S : OddScale) : (nu1 S).val (baseRetainedZ S) = 1 := by
  change ((indexedDecoderData S 4).selectedMap (0 : StepIndex 4)).map2
    (nu0 S).val ((rxData S 4 0 (by decide)).induced.zPairEquiv (seedZ S,0)).val = 1
  rw [selectedMap_eq]
  exact ((rxData S 4 (0 : StepIndex 4) (by decide)).induced.map2_diagonal
    (nu0 S).val (seedZ S) 0).trans (nu0_at_seed S)
theorem gamma2_at_r2 (S : OddScale) : (gamma2 S).val (r2 S) = 1 := by
  change BDL26RZMap1CoordinateBridge.map2Coord (state S 1).presentation
    (state S 1).admissible S (nu1 S).val
      ⟨baseRetainedZ S,rzMap1ZRoot (state S 1).presentation
        (state S 1).admissible (baseRetainedZ S) S⟩ = 1
  rw [BDL26OwnerParentObstruction.rzMap2_apply]
  simpa using nu1_at_retained S
theorem actual_base_neighbor_exists (S : OddScale) :
    ∃ q : (state S 2).presentation.Q,
      (state S 2).presentation.qz q (r2 S) = true ∧ E2 S q ≠ 0 := by
  classical
  have hb : (CF S).coboundary1 (2 : LevelIndex 4) (E2 S) = (gamma2 S).val :=
    actualBaseDecode_rightInverse S 2 (gamma2 S)
  have he := congrFun hb (r2 S)
  rw [CF_coboundary1,gamma2_at_r2] at he
  change (∑ q : (state S 2).presentation.Q,
    E2 S q * if (state S 2).presentation.qz q (r2 S) = true then 1 else 0) = 1 at he
  by_contra hn
  push Not at hn
  have hz : (∑ q : (state S 2).presentation.Q,
      E2 S q * if (state S 2).presentation.qz q (r2 S) = true then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    by_cases hq : (state S 2).presentation.qz q (r2 S) = true
    · simp only [if_pos hq, hn q hq, zero_mul]
    · simp only [if_neg hq, mul_zero]
  exact zero_ne_one (hz.symm.trans he)
noncomputable def q2 (S : OddScale) : (state S 2).presentation.Q :=
  Classical.choose (actual_base_neighbor_exists S)
theorem q2_incidence (S : OddScale) : (state S 2).presentation.qz (q2 S) (r2 S) = true :=
  (Classical.choose_spec (actual_base_neighbor_exists S)).1
noncomputable def localSeed (S : OddScale) (q : (state S 2).presentation.Q) :
    LocalQWord S q :=
  if h : q2 S = q then h ▸ terminalIndicator S (q2 S) (r2 S) (q2_incidence S) else 0
noncomputable def localQuery (S : OddScale) (q : (state S 2).presentation.Q) :
    LocalQSyndrome S q := (A S).contract.rx_local_complexes.cqDelta1 q (localSeed S q)
theorem localQuery_range (S : OddScale) (q : (state S 2).presentation.Q) :
    localQuery S q ∈ LinearMap.range ((A S).contract.rx_local_complexes.cqDelta1 q) :=
  ⟨localSeed S q,rfl⟩
noncomputable def localW (S : OddScale) (q : (state S 2).presentation.Q) : LocalQWord S q :=
  actualQSection S q (localQuery S q) (localQuery_range S q)
noncomputable def G (S : OddScale) : Correction3 S :=
  ∑ q, extendWordLinear ((LQ S).correctionRegion q) (localW S q)
noncomputable def lower3 (S : OddScale) :
    (CF S).Syndrome level3 := by
  let lifted : (CF S).Syndrome level3 :=
    ((indexedDecoderData S 4).selectedMap (2 : StepIndex 4)).mapSyndrome (gamma2 S)
  refine ⟨lifted.val + d3 S (G S), ?_⟩
  obtain ⟨e,he⟩ := lifted.property
  exact ⟨e+G S, by rw [map_add,he]⟩
noncomputable def upper4 (S : OddScale) : BDL26CanonicalHistoryMarks.Input S 2 :=
  BDL26RZDecoderAdapter.embeddedSyndrome S 4 (3 : StepIndex 4) (lower3 S)
open BDL26RXLocalReplacement BDL26RXStagedRestriction
noncomputable def topWitness (S : OddScale) (sigma : BDL26CanonicalHistoryMarks.Input S 2) :
    (CF S).Cochain2 level4 :=
  maskWord (Finset.univ.filter (fun p =>
    actualTopNode S
      (BDL26CanonicalHistoryMarks.syndromeOwner S 2 (1 : StepIndex 2) p) ∈
        BDL26CanonicalHistoryMarks.rootComponent S 2 sigma)) sigma.val
noncomputable def topOut (S : OddScale) := actualStep S 4 (3 : StepIndex 4) (upper4 S)
noncomputable def nextOut (S : OddScale) := actualStep S 4 (2 : StepIndex 4) (topOut S).coarse
noncomputable def storedBase (S : OddScale) :
    RecursiveBaseLevelCorrection (LevelTwoHistory.suffixData (indexedDecoderData S 4)) where
  input := (nextOut S).coarse
  correction := (actualBase S 2).decode (nextOut S).coarse
  relation := ((actualBase S 2).rightInverse (nextOut S).coarse).symm
noncomputable def eta (S : OddScale) : Word3 S :=
  selectedWord (fun z : FamilyZ S 4 level3 => actualTopNode S (zVertex S 3 z) ∈
    BDL26CanonicalHistoryMarks.rootComponent S 2 (upper4 S)) (lower3 S).val
abbrev xFace3 (S : OddScale) (x : (state S 2).presentation.X)
    (f : DoubleCylinderFace (state S 2).presentation x S) : FamilyZ S 4 level3 :=
  Sum.inl (Sum.inl ⟨x,f⟩)
abbrev qEdge3 (S : OddScale) (q : (state S 2).presentation.Q)
    (e : QDoubleCylinderEdge (state S 2).presentation q S) : FamilyZ S 4 level3 :=
  Sum.inl (Sum.inr ⟨q,e⟩)
structure MarkedRootPath {N : Type} (M : N → Prop) (R : N → N → Prop)
    (root w : N) : Prop where
  root_marked : M root
  marked : M w
  path : Relation.ReflTransGen R w root
inductive OriginalRootPath (S : OddScale) (n : Nat)
    (sigma : BDL26CanonicalHistoryMarks.Input S n) :
    BDL26CanonicalHistoryMarks.Node S n → Prop where
  | rooted
      (hroot : BDL26CanonicalHistoryMarks.root S n ∈
        BDL26CanonicalHistoryMarks.marks S n sigma) :
      OriginalRootPath S n sigma (BDL26CanonicalHistoryMarks.root S n)
  | prepend {u v : BDL26CanonicalHistoryMarks.Node S n}
      (hedge : BDL26CanonicalHistoryMarks.markedAdjacent S n sigma u v)
      (hpath : OriginalRootPath S n sigma v) :
      OriginalRootPath S n sigma u
end
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26ReplacementSupport
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable section
noncomputable def rootMaskMidRegion (S : OddScale) :
    Finset (FamilyZ S 4 level3) :=
  Finset.univ.filter (fun p =>
    actualMidNode S (BDL26CanonicalHistoryMarks.syndromeOwner S 2 (0 : StepIndex 2) p) ∈
      BDL26CanonicalHistoryMarks.rootComponent S 2 (upper4 S))
noncomputable def rootMaskMidWord (S : OddScale) : Word3 S :=
  maskWord (rootMaskMidRegion S) (lower3 S).val
end
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample


