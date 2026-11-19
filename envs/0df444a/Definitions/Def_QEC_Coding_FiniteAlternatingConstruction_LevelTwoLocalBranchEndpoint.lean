-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoLocalBranchEndpoint
-- name    : QEC_Coding_FiniteAlternatingConstruction_LevelTwoLocalBranchEndpoint
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:42:14.365549+00:00
-- url     : https://prove2.me/theorems/87b5a3f2-0b5d-4703-8dd7-38bd5c203c42
-- title:
--   Level Two Local Branch Endpoint
-- statement:
--   Definitions and structural lemmas for Level Two Local Branch Endpoint, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoLocalBranchEndpoint.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
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
import Theorems.Thm_QEC_Coding_BDL26LevelTwoCode_levelTwoState_eq_pair
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_decode_zero
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_executableLocal_iff
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_executableSyndrome_eq
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_search_sound
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_toExecutableSyndrome_injective
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_levelOne_two_support_cocycle_zero
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_levelTwoLocalError_iff_owner
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_qCoordinateOfOwner_of_eq
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rzLocal_cycle_of_cocycle_q_zero
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rzQEdge_coboundary_apply_q
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rzQParity_cocycle
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rzQParity_zero_has_qFillings
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rzQParity_zero_of_other_owner
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rzWord_eq_sum_local_of_q_zero
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_sum_extendRZQVertexWord_apply
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_tannerCoboundary_squared
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_zCylinder_cycle_has_filling
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
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_lower_self
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_lower_singleton_x
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_neighbors_empty
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_phi_empty
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_phi_self
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_phi_singleton
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_remainder_empty
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_remainder_self
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_remainder_singleton
import Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_errorInfluence_zero
import Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_sigmaPlusError_zero
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalWordPush_single
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_block_star_parent
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_boundaryCenter_parent
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_lower_self
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_mem_physicalXStar
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_neighbors_parent
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_phi_self
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_remainder_self
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_lowerWord_self
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_potential_delta_delta_zero
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_potential_delta_zero
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_potential_eq_zero
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_rootCoefficient_self
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_localPotential_self
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_lowerWord_self
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_mem_incidentQ
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_mem_starQ
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_potential_self
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_remainder_self
import Theorems.Thm_QEC_Coding_BDL26RZCohomology_backward_mk
import Theorems.Thm_QEC_Coding_BDL26RZCohomology_equiv_mk
import Theorems.Thm_QEC_Coding_BDL26RZCohomology_equiv_symm_mk
import Theorems.Thm_QEC_Coding_BDL26RZCohomology_forward_mk
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
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_coord1_upperQChart
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_coord2_upperZChart
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_mem_physicalZStar
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_qCentre_parentZ
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_upperQChart_coord1
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_upperZChart_coord2
import Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_extendRZLocalEdgeWord_eq
import Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzCoboundary0_extendRZFaceWord
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
attribute [local simp] QEC.Coding.BDL26RXFiniteBlockTransport.lower_self
attribute [local simp] QEC.Coding.BDL26RXFiniteBlockTransport.lower_singleton_x
attribute [local simp] QEC.Coding.BDL26RXFiniteBlockTransport.neighbors_empty
attribute [local simp] QEC.Coding.BDL26RXFiniteBlockTransport.phi_empty
attribute [local simp] QEC.Coding.BDL26RXFiniteBlockTransport.phi_self
attribute [local simp] QEC.Coding.BDL26RXFiniteBlockTransport.phi_singleton
attribute [local simp] QEC.Coding.BDL26RXFiniteBlockTransport.remainder_empty
attribute [local simp] QEC.Coding.BDL26RXFiniteBlockTransport.remainder_self
attribute [local simp] QEC.Coding.BDL26RXFiniteBlockTransport.remainder_singleton
attribute [local simp] QEC.Coding.BDL26RXInfluenceBounds.errorInfluence_zero
attribute [local simp] QEC.Coding.BDL26RXInfluenceBounds.sigmaPlusError_zero
attribute [local simp] QEC.Coding.BDL26RXLocalReplacement.xLocalWordPush_single
attribute [local simp] QEC.Coding.BDL26RXPhysicalStarTransport.block_star_parent
attribute [local simp] QEC.Coding.BDL26RXPhysicalStarTransport.boundaryCenter_parent
attribute [local simp] QEC.Coding.BDL26RXPhysicalStarTransport.lower_self
attribute [local simp] QEC.Coding.BDL26RXPhysicalStarTransport.mem_physicalXStar
attribute [local simp] QEC.Coding.BDL26RXPhysicalStarTransport.neighbors_parent
attribute [local simp] QEC.Coding.BDL26RXPhysicalStarTransport.phi_self
attribute [local simp] QEC.Coding.BDL26RXPhysicalStarTransport.remainder_self
attribute [local simp] QEC.Coding.BDL26RXQBlockTransport.lowerWord_self
attribute [local simp] QEC.Coding.BDL26RXQBlockTransport.potential_delta_delta_zero
attribute [local simp] QEC.Coding.BDL26RXQBlockTransport.potential_delta_zero
attribute [local simp] QEC.Coding.BDL26RXQBlockTransport.potential_eq_zero
attribute [local simp] QEC.Coding.BDL26RXQBlockTransport.rootCoefficient_self
attribute [local simp] QEC.Coding.BDL26RXXStarTransport.localPotential_self
attribute [local simp] QEC.Coding.BDL26RXXStarTransport.lowerWord_self
attribute [local simp] QEC.Coding.BDL26RXXStarTransport.mem_incidentQ
attribute [local simp] QEC.Coding.BDL26RXXStarTransport.mem_starQ
attribute [local simp] QEC.Coding.BDL26RXXStarTransport.potential_self
attribute [local simp] QEC.Coding.BDL26RXXStarTransport.remainder_self
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
attribute [local simp] QEC.Coding.BDL26RZPhysicalStarTransport.coord1_upperQChart
attribute [local simp] QEC.Coding.BDL26RZPhysicalStarTransport.coord2_upperZChart
attribute [local simp] QEC.Coding.BDL26RZPhysicalStarTransport.mem_physicalZStar
attribute [local simp] QEC.Coding.BDL26RZPhysicalStarTransport.qCentre_parentZ
attribute [local simp] QEC.Coding.BDL26RZPhysicalStarTransport.upperQChart_coord1
attribute [local simp] QEC.Coding.BDL26RZPhysicalStarTransport.upperZChart_coord2
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
namespace QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26LevelTwoCode
open BDL26LevelTwoDistance BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open scoped BigOperators
abbrev Bit := BDL26FiniteTannerSquare.Field
abbrev P (S : OddScale) := (rxState S baseState).presentation
abbrev C (S : OddScale) := (rzState S (rxState S baseState)).presentation
abbrev A (S : OddScale) : TannerSquareAdmissibleV4 (P S) :=
  (rxState S baseState).admissible
abbrev Error (S : OddScale) := Word Bit (C S).Q
abbrev Syndrome (S : OddScale) := Word Bit (C S).Z
abbrev Potential (S : OddScale) := Word Bit (C S).X
abbrev D (S : OddScale) : Syndrome S → Error S := BDL26LevelTwoDecoder.decode S
abbrev delta (S : OddScale) : Error S →ₗ[Bit] Syndrome S := tannerCoboundary1 (C S)
abbrev boundary (S : OddScale) : Potential S →ₗ[Bit] Error S := tannerCoboundary0 (C S)
abbrev parity (S : OddScale) := rzQParity (P S) S
def localSearch (S : OddScale) (t : Syndrome S) :
    Option (Word Bit (BDL26LevelTwoDecoder.ExecutableQ S)) :=
  BDL26LevelTwoDecoder.search
    (fun w => BDL26LevelTwoDecoder.executableLocal S w &&
      decide (BDL26LevelTwoDecoder.executableSyndrome S w=
        BDL26LevelTwoDecoder.toExecutableSyndrome S t))
    (BDL26LevelTwoDecoder.allWords (BDL26LevelTwoDecoder.ExecutableQ S))
def globalSearch (S : OddScale) (t : Syndrome S) :
    Option (Word Bit (BDL26LevelTwoDecoder.ExecutableQ S)) :=
  BDL26LevelTwoDecoder.search
    (fun w => decide (BDL26LevelTwoDecoder.executableSyndrome S w=
      BDL26LevelTwoDecoder.toExecutableSyndrome S t))
    (BDL26LevelTwoDecoder.allWords (BDL26LevelTwoDecoder.ExecutableQ S))
def localSuccess (S : OddScale) (t : Syndrome S) : Prop :=
  ∃ w, localSearch S t=some w
open scoped Classical
theorem actual_presentation (S : OddScale) :
    levelTwoPresentation S=C S :=
  congrArg ConstructionState.presentation (levelTwoState_eq_pair S)
theorem coboundary1_heq {U V : TannerSquarePresentation} (h : U=V) :
    HEq (tannerCoboundary1 U) (tannerCoboundary1 V) := by
  cases h
  rfl
theorem actual_delta (S : OddScale) :
    (tannerCoboundary1 (levelTwoPresentation S) : Error S →ₗ[Bit] Syndrome S)=delta S := by
  exact eq_of_heq (coboundary1_heq (actual_presentation S))
theorem encoded_delta (S : OddScale) (e : Error S) :
    BDL26LevelTwoDecoder.executableSyndrome S (BDL26LevelTwoDecoder.toExecutableError S e)=
      BDL26LevelTwoDecoder.toExecutableSyndrome S (delta S e) := by
  have he := congrArg (fun F : Error S →ₗ[Bit] Syndrome S => F e) (actual_delta S)
  exact (BDL26LevelTwoDecoder.executableSyndrome_eq S e).trans
    (congrArg (BDL26LevelTwoDecoder.toExecutableSyndrome S) he)
theorem raw_owner_iff (S : OddScale) (e : Error S) :
    levelTwoLocalError S e ↔ ∃ owner : Vertex (P S), ∀ q : RZQ (P S) S,
      e q≠0 → BDL26ReplacementSupport.rzCorrectionOwner (P S) S q=owner := by
  exact levelTwoLocalError_iff_owner S e
theorem twice {I : Type} (w : Word Bit I) : w+w=0 := by
  funext i
  exact ZModModule.add_self (w i)
theorem parity_add (S : OddScale) (first second : Error S) :
    parity S (first+second)=parity S first+parity S second := by
  exact (rzQParity (P S) S).map_add first second
theorem returned_word (S : OddScale) (t : Syndrome S)
    (w : Word Bit (BDL26LevelTwoDecoder.ExecutableQ S))
    (hw : localSearch S t=some w) :
    D S t=BDL26LevelTwoDecoder.toActualError S w := by
  unfold localSearch at hw
  unfold D BDL26LevelTwoDecoder.decode BDL26LevelTwoDecoder.executableDecode
    BDL26LevelTwoDecoder.lookup
  rw [hw]
theorem returned_local_and_syndrome (S : OddScale) (t : Syndrome S)
    (w : Word Bit (BDL26LevelTwoDecoder.ExecutableQ S))
    (hw : localSearch S t=some w) :
    levelTwoLocalError S (D S t) ∧ delta S (D S t)=t := by
  have hp := (BDL26LevelTwoDecoder.search_sound _ _ _ hw).2
  have hl := ((Bool.and_eq_true_eq_eq_true_and_eq_true _ _).mp hp).1
  have hs := ((Bool.and_eq_true_eq_eq_true_and_eq_true _ _).mp hp).2
  rw [returned_word S t w hw]
  constructor
  · apply (BDL26LevelTwoDecoder.executableLocal_iff S _).1
    simpa only [BDL26LevelTwoDecoder.toExecutableError_toActualError] using hl
  · apply BDL26LevelTwoDecoder.toExecutableSyndrome_injective S
    have h := encoded_delta S (BDL26LevelTwoDecoder.toActualError S w)
    have he : BDL26LevelTwoDecoder.toExecutableError S
        (BDL26LevelTwoDecoder.toActualError S w)=w :=
      BDL26LevelTwoDecoder.toExecutableError_toActualError S w
    have h' : BDL26LevelTwoDecoder.executableSyndrome S w=
        BDL26LevelTwoDecoder.toExecutableSyndrome S
          (delta S (BDL26LevelTwoDecoder.toActualError S w)) :=
      (congrArg (BDL26LevelTwoDecoder.executableSyndrome S) he).symm.trans h
    exact h'.symm.trans (of_decide_eq_true hs)
theorem decode_zero (S : OddScale) : D S 0=0 :=
  BDL26LevelTwoDecoder.decode_zero S
def star (S : OddScale) (u : RZX (P S) S) : Finset (RZQ (P S) S) :=
  BDL26RXPhysicalStarTransport.physicalXStar (C S) u
def supported (S : OddScale) (u : RZX (P S) S) (h : Error S) : Prop :=
  hammingSupport h ⊆ star S u
theorem parity_local_label (S : OddScale) (c : Error S)
    (hc : levelTwoLocalError S c) (default : (P S).Q) :
    ∃ a : (P S).Q, ∀ q, q≠a → parity S c q=0 := by
  obtain ⟨owner,ho⟩ := (raw_owner_iff S c).1 hc
  refine ⟨qCoordinateOfOwner (P S) default owner,?_⟩
  intro q hq
  apply rzQParity_zero_of_other_owner (P S) S c owner ho q
  intro heq
  exact hq (qCoordinateOfOwner_of_eq (P S) default q owner heq)
theorem raw_full_filling (P0 : TannerSquarePresentation)
    (A0 : TannerSquareAdmissibleV4 P0) (R0 : TannerSquareCellularRegular P0) (S : OddScale)
    (r : Word Bit (RZQ P0 S))
    (hc : rzCoboundary1 P0 A0 S r=0) (hp : rzQParity P0 S r=0) :
    ∃ pQ pZ : Word Bit (RZX P0 S),
      (∀ q v, rzCoboundary0 P0 A0 S pQ (.inr ⟨q,v⟩)=r (.inr ⟨q,v⟩)) ∧
      (∀ q v, (r+rzCoboundary0 P0 A0 S pQ) (.inr ⟨q,v⟩)=0) ∧
      rzCoboundary0 P0 A0 S pZ=r+rzCoboundary0 P0 A0 S pQ ∧
      rzCoboundary0 P0 A0 S (pZ+pQ)=r := by
  obtain ⟨edges,hedges⟩ := Classical.skolem.mp
    (rzQParity_zero_has_qFillings P0 A0.toTannerSquareAdmissible S r hp)
  let pQ : Word Bit (RZX P0 S) := ∑ q : P0.Q, extendRZQEdgeWord P0 S q (edges q)
  have hqp : ∀ q v, rzCoboundary0 P0 A0 S pQ (.inr ⟨q,v⟩)=r (.inr ⟨q,v⟩) := by
    intro q v
    dsimp only [pQ]
    rw [map_sum,Finset.sum_apply]
    simp only [rzQEdge_coboundary_apply_q,hedges]
    simpa only [Finset.sum_apply] using sum_extendRZQVertexWord_apply P0 S r q v
  let rem : Word Bit (RZQ P0 S) := r+rzCoboundary0 P0 A0 S pQ
  have hq : ∀ q v, rem (.inr ⟨q,v⟩)=0 := by
    intro q v
    change r _+rzCoboundary0 P0 A0 S pQ _=0
    rw [hqp]
    exact ZModModule.add_self _
  have hrem : rzCoboundary1 P0 A0 S rem=0 := by
    dsimp only [rem]
    rw [map_add,hc,zero_add]
    exact LinearMap.congr_fun (tannerCoboundary_squared (rzReplacementPresentation P0 A0.toTannerSquareAdmissible S)) pQ
  have hf : ∀ z : P0.Z, ∃ faces : Word Bit (ZDoubleCylinderFace P0 z S),
      doubleCylinderBoundary2 (transposePresentation P0) z S faces=
        fun e => rem (.inl ⟨z,e⟩) := by
    intro z
    exact zCylinder_cycle_has_filling P0 A0.toTannerSquareAdmissibleV3
      R0 z S _
      (rzLocal_cycle_of_cocycle_q_zero P0 A0 S rem hrem hq z)
  choose faces hfaces using hf
  let pZ : Word Bit (RZX P0 S) := ∑ z : P0.Z, extendRZFaceWord P0 S z (faces z)
  have hz : rzCoboundary0 P0 A0 S pZ=rem := by
    dsimp only [pZ]
    rw [map_sum]
    simp only [rzCoboundary0_extendRZFaceWord,extendRZLocalEdgeWord_eq,hfaces]
    exact (rzWord_eq_sum_local_of_q_zero P0 S rem hq).symm
  refine ⟨pQ,pZ,hqp,hq,hz,?_⟩
  calc
    rzCoboundary0 P0 A0 S (pZ+pQ)=rzCoboundary0 P0 A0 S pZ+rzCoboundary0 P0 A0 S pQ := (rzCoboundary0 P0 A0 S).map_add pZ pQ
    _ = (r+rzCoboundary0 P0 A0 S pQ)+rzCoboundary0 P0 A0 S pQ := by rw [hz]
    _ = r := by rw [add_assoc,twice,add_zero]
theorem full_filling (S : OddScale) (r : Error S)
    (hc : delta S r=0) (hp : parity S r=0) :
    ∃ pQ pZ : Potential S,
      (∀ q v, boundary S pQ (.inr ⟨q,v⟩)=r (.inr ⟨q,v⟩)) ∧
      (∀ q v, (r+boundary S pQ) (.inr ⟨q,v⟩)=0) ∧
      boundary S pZ=r+boundary S pQ ∧ boundary S (pZ+pQ)=r := by
  exact raw_full_filling (P S) (A S) (rxState S baseState).regular S r hc hp
theorem two_parity_endpoint (S : OddScale) (r : Error S)
    (hc : delta S r=0) (a b : (P S).Q)
    (hs : ∀ q, parity S r q≠0 → q=a ∨ q=b) :
    ∃ p : Potential S, boundary S p=r := by
  have hproj := rzQParity_cocycle (P S) (A S) S r hc
  have hp := levelOne_two_support_cocycle_zero S (parity S r) hproj a b hs
  obtain ⟨pQ,pZ,_,_,_,hpz⟩ := full_filling S r hc hp
  exact ⟨pZ+pQ,hpz⟩
theorem one_parity_endpoint (S : OddScale) (h : Error S) (a : (P S).Q)
    (ha : ∀ q, q≠a → parity S h q=0) (hb : localSuccess S (delta S h)) :
    ∃ p : Potential S, boundary S p=h+D S 0+D S (delta S h) := by
  obtain ⟨w,hw⟩ := hb
  obtain ⟨hc,hs⟩ := returned_local_and_syndrome S (delta S h) w hw
  obtain ⟨b,hb⟩ := parity_local_label S (D S (delta S h)) hc a
  have hcycle : delta S (h+D S (delta S h))=0 := by
    rw [map_add,hs]
    exact twice _
  have hsupp : ∀ q, parity S (h+D S (delta S h)) q≠0 → q=a ∨ q=b := by
    intro q hq
    by_contra hn
    have hqa : q≠a := fun heq => hn (Or.inl heq)
    have hqb : q≠b := fun heq => hn (Or.inr heq)
    apply hq
    calc
      parity S (h+D S (delta S h)) q=
          parity S h q+parity S (D S (delta S h)) q :=
        congrFun (parity_add S h (D S (delta S h))) q
      _ = 0 := by rw [ha q hqa,hb q hqb,zero_add]
  obtain ⟨p,hp⟩ := two_parity_endpoint S (h+D S (delta S h)) hcycle a b hsupp
  refine ⟨p,?_⟩
  simpa only [decode_zero,add_zero] using hp
def endpointPotential (S : OddScale) (h : Error S) (a : (P S).Q)
    (ha : ∀ q, q≠a → parity S h q=0) (hb : localSuccess S (delta S h)) : Potential S :=
  Classical.choose (one_parity_endpoint S h a ha hb)
end QEC.Coding.BDL26LevelTwoLocalBranchEndpoint


