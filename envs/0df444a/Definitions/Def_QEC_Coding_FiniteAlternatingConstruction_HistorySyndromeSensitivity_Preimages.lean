-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Preimages
-- name    : QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Preimages
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T10:50:56.676877+00:00
-- url     : https://prove2.me/theorems/470dc27e-35e4-42e4-9497-ec45cd5b5405
-- title:
--   Preimages
-- statement:
--   Definitions and structural lemmas for Preimages, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Preimages.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_correctionRegion_mem
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_syndromeRegion_mem
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_finiteH1Equiv_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_generator_value
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_prefixCocycle_value
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_prefixCocycle_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
import Theorems.Thm_QEC_Coding_BDL26RXCohomology_equiv_mk
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
import Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_one_run
import Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_errorInfluence_zero
import Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_sigmaPlusError_zero
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalWordPush_single
import Theorems.Thm_QEC_Coding_BDL26RZCohomology_backward_mk
import Theorems.Thm_QEC_Coding_BDL26RZCohomology_equiv_mk
import Theorems.Thm_QEC_Coding_BDL26RZCohomology_equiv_symm_mk
import Theorems.Thm_QEC_Coding_BDL26RZCohomology_forward_mk
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_presentationOutput_coarse
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_presentationOutput_components
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_presentationOutput_correction
import Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_one_run
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzFace_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzQ_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzX_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzZ_card
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_map2Coord_canonicalBasis
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary0_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary1_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_fiberPart_apply
import Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rxQOutgoing_nonincident
import Theorems.Thm_QEC_Coding_BDL26SeedCohomology_equivalence_classOf
import Theorems.Thm_QEC_Coding_BDL26SeedCohomology_equivalence_symm_apply
import Theorems.Thm_QEC_Coding_BDL26SeedCohomology_stateZeroEquivalence_classOf
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
attribute [local simp] QEC.Coding.BDL26DecodingGraph.correctionRegion_mem
attribute [local simp] QEC.Coding.BDL26DecodingGraph.syndromeRegion_mem
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.alternatingCarrier_zero
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_target_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_target_val
attribute [local simp] QEC.Coding.BDL26FiniteCohomology.finiteH1Equiv_zero
attribute [local simp] QEC.Coding.BDL26FiniteCohomology.generator_value
attribute [local simp] QEC.Coding.BDL26FiniteCohomology.prefixCocycle_value
attribute [local simp] QEC.Coding.BDL26FiniteCohomology.prefixCocycle_zero
attribute [local simp] QEC.Coding.BDL26FiniteTannerSquare.doubleCylinderEndInclusion_apply
attribute [local simp] QEC.Coding.BDL26RXCohomology.equiv_mk
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
attribute [local simp] QEC.Coding.BDL26RXInfluenceBounds.errorInfluence_zero
attribute [local simp] QEC.Coding.BDL26RXInfluenceBounds.sigmaPlusError_zero
attribute [local simp] QEC.Coding.BDL26RXLocalReplacement.xLocalWordPush_single
attribute [local simp] QEC.Coding.BDL26RZCohomology.backward_mk
attribute [local simp] QEC.Coding.BDL26RZCohomology.equiv_mk
attribute [local simp] QEC.Coding.BDL26RZCohomology.equiv_symm_mk
attribute [local simp] QEC.Coding.BDL26RZCohomology.forward_mk
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
attribute [local simp] QEC.Coding.BDL26SeedCohomology.equivalence_classOf
attribute [local simp] QEC.Coding.BDL26SeedCohomology.equivalence_symm_apply
attribute [local simp] QEC.Coding.BDL26SeedCohomology.stateZeroEquivalence_classOf
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
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical
def errorInput (S : OddScale) (d : Nat) (i : StepIndex d)
    (e : (indexedFamily S d).Cochain1 i.succ) : (indexedFamily S d).Syndrome i.succ :=
  ⟨(indexedFamily S d).coboundary1 i.succ e,⟨e,rfl⟩⟩
theorem actual_pullback (S : OddScale) (d : Nat) (i : StepIndex d) (hi : 2 ≤ i.val)
    (e : (indexedFamily S d).Cochain1 i.succ) :
    ∃ (l : (indexedFamily S d).Cochain1 i.castSucc)
      (p : (indexedFamily S d).Cochain0 i.succ),
      ((indexedDecoderData S d).selectedMap i).map1 l =
        e + (actualStep S d i (errorInput S d i e)).correction +
          (indexedFamily S d).coboundary0 i.succ p ∧
      (indexedFamily S d).coboundary1 i.castSucc l =
        (actualStep S d i (errorInput S d i e)).coarse.val ∧
      (indexedFamily S d).coboundary1 i.succ
        ((indexedFamily S d).coboundary0 i.succ p) = 0 := by
  by_cases h : i.val % 2 = 0
  · obtain ⟨l,p,hl,hd,_,hp⟩ := BDL26RXErrorPullback.one_run S d i hi h e
    have hr : BDL26RXErrorPullback.run S d i h e = actualStep S d i (errorInput S d i e) := by
      rw [BDL26RXErrorPullback.run, actualStep_rx S d i h]
      rfl
    exact ⟨l,p,by simpa only [hr] using hl,by simpa only [hr] using hd,hp⟩
  · obtain ⟨l,p,hl,hd,_,hp⟩ := BDL26RZErrorPullback.one_run S d i hi h e
    have hr : BDL26RZErrorPullback.run S d i h e = actualStep S d i (errorInput S d i e) := by
      rw [BDL26RZErrorPullback.run, actualStep_rz S d i h]
      rfl
    exact ⟨l,p,by simpa only [hr] using hl,by simpa only [hr] using hd,hp⟩
def lowerRepresentative (S : OddScale) (d : Nat) (i : StepIndex d) (hi : 2 ≤ i.val)
    (e : (indexedFamily S d).Cochain1 i.succ) : (indexedFamily S d).Cochain1 i.castSucc :=
  Classical.choose (actual_pullback S d i hi e)
def fullPotential (S : OddScale) (d : Nat) (i : StepIndex d) (hi : 2 ≤ i.val)
    (e : (indexedFamily S d).Cochain1 i.succ) : (indexedFamily S d).Cochain0 i.succ :=
  Classical.choose (Classical.choose_spec (actual_pullback S d i hi e))
variable (S : OddScale) (n : Nat)
def physicalUpperError (i : StepIndex n)
    (e : (SuffixData S n).family.Cochain1 i.succ) :
    (indexedFamily S (n+2)).Cochain1 (LevelTwoHistory.physicalStep i).succ := e
def errorDown (b : Nat) (hb : b ≤ n)
    (e : (SuffixData S n).family.Cochain1 ⟨b,Nat.lt_succ_of_le hb⟩)
    (a : LevelIndex n) (ha : a.val ≤ b) : (SuffixData S n).family.Cochain1 a := by
  cases b with
  | zero =>
      exact (show (⟨0,Nat.lt_succ_of_le hb⟩ : LevelIndex n) = a from
        Fin.ext (by change 0 = a.val; omega)) ▸ e
  | succ b =>
      if h : a.val = b+1 then
        exact (show (⟨b+1,Nat.lt_succ_of_le hb⟩ : LevelIndex n) = a from
          Fin.ext h.symm) ▸ e
      else
        exact errorDown b (by omega)
          (lowerRepresentative S (n+2) (LevelTwoHistory.physicalStep ⟨b,by omega⟩)
            (by simp only [LevelTwoHistory.physicalStep_val]; omega) e) a (by omega)
termination_by b
end QEC.Coding.BDL26HistorySyndromeSensitivity


