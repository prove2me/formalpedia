-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
-- name    : QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T17:53:30.079855+00:00
-- url     : https://prove2.me/theorems/99efd557-8d9a-41fa-9639-8e39c3ef73b5
-- title:
--   Localized History Error Descent
-- statement:
--   Definitions and structural lemmas for Localized History Error Descent, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
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
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualInputs_step
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualInputs_top
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_perturbTop_difference
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
import Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_two_run
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_lower_self
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_lower_singleton_x
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_neighbors_empty
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_phi_empty
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_phi_self
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_phi_singleton
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_remainder_empty
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_remainder_self
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_remainder_singleton
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_two_run
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
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_two_run
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_lowerWord_self
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_potential_delta_delta_zero
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_potential_delta_zero
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_potential_eq_zero
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_rootCoefficient_self
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_two_run
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_localPotential_self
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_lowerWord_self
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_mem_incidentQ
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_mem_starQ
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_potential_self
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_remainder_self
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_two_run
import Theorems.Thm_QEC_Coding_BDL26RZCohomology_backward_mk
import Theorems.Thm_QEC_Coding_BDL26RZCohomology_equiv_mk
import Theorems.Thm_QEC_Coding_BDL26RZCohomology_equiv_symm_mk
import Theorems.Thm_QEC_Coding_BDL26RZCohomology_forward_mk
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_presentationOutput_coarse
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_presentationOutput_components
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_presentationOutput_correction
import Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_two_run
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_two_run
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
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_two_run
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_upperQChart_coord1
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_upperZChart_coord2
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_lower_physical_supported
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_two_run
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
namespace QEC.Coding.BDL26LocalizedHistoryErrorDescent
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open scoped Classical BigOperators
theorem twice {I : Type} (w : Word BDL26Field I) : w+w=0 := by
  funext q
  exact ZModModule.add_self (w q)
theorem cancel_pair {I : Type} (a b : Word BDL26Field I) : a+(a+b)=b := by
  rw [← add_assoc,twice,zero_add]
abbrev Data (S : OddScale) (n : Nat) := SuffixData S n
abbrev Edge (n : Nat) (i : StepIndex n) := LevelTwoHistory.physicalStep i
def star (S : OddScale) (n : Nat) (a : LevelIndex n)
    (x : (state S (a.val+2)).presentation.X) :
    Finset (state S (a.val+2)).presentation.Q :=
  BDL26RXPhysicalStarTransport.physicalXStar (state S (a.val+2)).presentation x
variable (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
structure LocalizedWord (a : LevelIndex n) where
  word : (Data S n).family.Cochain1 a
  center : (state S (a.val+2)).presentation.X
  supported : hammingSupport word ⊆ star S n a center
  syndrome : (Data S n).family.coboundary1 a word =
    (actualInputs S n sigma a).val+(actualInputs S n tau a).val
def originalOutput (i : StepIndex n) :
    AssemblyStepOutput (indexedDecoderData S (n+2)) (Edge n i) :=
  actualStep S (n+2) (Edge n i) (actualInputs S n sigma i.succ)
theorem originalOutput_correction (i : StepIndex n) :
    (originalOutput S n sigma i).correction=(actualOutput S n sigma i).correction := rfl
theorem originalOutput_coarse (i : StepIndex n) :
    (originalOutput S n sigma i).coarse=actualInputs S n sigma i.castSucc :=
  (actualInputs_step S n sigma i).symm
def first (i : StepIndex n) : (Data S n).family.Cochain1 i.succ :=
  Classical.choose (actualInputs S n sigma i.succ).property
theorem first_spec (i : StepIndex n) :
    (Data S n).family.coboundary1 i.succ (first S n sigma i)=
      (actualInputs S n sigma i.succ).val :=
  Classical.choose_spec (actualInputs S n sigma i.succ).property
def second (i : StepIndex n) (u : LocalizedWord S n sigma tau i.succ) :
    (Data S n).family.Cochain1 i.succ := first S n sigma i+u.word
theorem second_spec (i : StepIndex n) (u : LocalizedWord S n sigma tau i.succ) :
    (Data S n).family.coboundary1 i.succ (second S n sigma tau i u)=
      (actualInputs S n tau i.succ).val := by
  rw [second,map_add,first_spec,u.syndrome]
  exact cancel_pair _ _
theorem representatives_difference (i : StepIndex n)
    (u : LocalizedWord S n sigma tau i.succ) :
    first S n sigma i+second S n sigma tau i u=u.word := cancel_pair _ _
theorem rx_first (i : StepIndex n) (h : (Edge n i).val%2=0) :
    BDL26RXErrorPullback.run S (n+2) (Edge n i) h (first S n sigma i)=
      originalOutput S n sigma i := by
  have hi : BDL26RXErrorPullback.errorSyndrome S (n+2) (Edge n i) (first S n sigma i)=
      actualInputs S n sigma i.succ := Subtype.ext (first_spec S n sigma i)
  rw [BDL26RXErrorPullback.run,hi,originalOutput,actualStep_rx S (n+2) (Edge n i) h]
theorem rx_second (i : StepIndex n) (h : (Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) :
    BDL26RXErrorPullback.run S (n+2) (Edge n i) h (second S n sigma tau i u)=
      originalOutput S n tau i := by
  have hi : BDL26RXErrorPullback.errorSyndrome S (n+2) (Edge n i) (second S n sigma tau i u)=
      actualInputs S n tau i.succ := Subtype.ext (second_spec S n sigma tau i u)
  rw [BDL26RXErrorPullback.run,hi,originalOutput,actualStep_rx S (n+2) (Edge n i) h]
theorem rz_first (i : StepIndex n) (h : ¬(Edge n i).val%2=0) :
    BDL26RZErrorPullback.run S (n+2) (Edge n i) h (first S n sigma i)=
      originalOutput S n sigma i := by
  have hi : BDL26RZErrorPullback.errorSyndrome S (n+2) (Edge n i) (first S n sigma i)=
      actualInputs S n sigma i.succ := Subtype.ext (first_spec S n sigma i)
  rw [BDL26RZErrorPullback.run,hi,originalOutput,actualStep_rz S (n+2) (Edge n i) h]
theorem rz_second (i : StepIndex n) (h : ¬(Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) :
    BDL26RZErrorPullback.run S (n+2) (Edge n i) h (second S n sigma tau i u)=
      originalOutput S n tau i := by
  have hi : BDL26RZErrorPullback.errorSyndrome S (n+2) (Edge n i) (second S n sigma tau i u)=
      actualInputs S n tau i.succ := Subtype.ext (second_spec S n sigma tau i u)
  rw [BDL26RZErrorPullback.run,hi,originalOutput,actualStep_rz S (n+2) (Edge n i) h]
structure StepResult (i : StepIndex n) (u : LocalizedWord S n sigma tau i.succ) where
  lower : LocalizedWord S n sigma tau i.castSucc
  potential : (Data S n).family.Cochain0 i.succ
  equation : ((Data S n).selectedMap i).map1 lower.word=
    u.word+(actualOutput S n sigma i).correction+(actualOutput S n tau i).correction+
      (Data S n).family.coboundary0 i.succ potential
theorem rx_localized (i : StepIndex n) (h : (Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) :
    BDL26RXPhysicalStarTransport.Localized S (n+2) (Edge n i) u.center
      (first S n sigma i) (second S n sigma tau i u) := by
  change hammingSupport (first S n sigma i+second S n sigma tau i u) ⊆ _
  rw [representatives_difference]
  exact u.supported
theorem rz_localized (i : StepIndex n) (h : ¬(Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) :
    BDL26RZPhysicalXStarTransport.Localized S (n+2) (Edge n i) u.center
      (first S n sigma i) (second S n sigma tau i u) := by
  change hammingSupport (first S n sigma i+second S n sigma tau i u) ⊆ _
  rw [representatives_difference]
  exact u.supported
def rxResult (i : StepIndex n) (h : (Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) : StepResult S n sigma tau i u := by
  let A := first S n sigma i
  let B := second S n sigma tau i u
  have hr := BDL26RXPhysicalStarTransport.two_run S (n+2) (Edge n i) h u.center A B
    (rx_localized S n sigma tau i h u)
  dsimp only [A,B] at hr
  refine {
    lower := {
      word := BDL26RXPhysicalStarTransport.L S (n+2) (Edge n i) h u.center A B
      center := BDL26RXPhysicalStarTransport.parentX S (n+2) (Edge n i) h u.center
      supported := hr.2.2.2.2.2.1
      syndrome := ?_ }
    potential := BDL26RXPhysicalStarTransport.Phi S (n+2) (Edge n i) h u.center A B
    equation := ?_ }
  · dsimp only [A,B]
    have hs := hr.2.2.1
    change (indexedFamily S (n+2)).coboundary1 (Edge n i).castSucc
      (BDL26RXPhysicalStarTransport.L S (n+2) (Edge n i) h u.center
        (first S n sigma i) (second S n sigma tau i u))=
      (BDL26RXErrorPullback.run S (n+2) (Edge n i) h (first S n sigma i)).coarse.val+
        (BDL26RXErrorPullback.run S (n+2) (Edge n i) h
          (second S n sigma tau i u)).coarse.val at hs
    rw [rx_first S n sigma i h,rx_second S n sigma tau i h u,
      originalOutput_coarse S n sigma i,originalOutput_coarse S n tau i] at hs
    rw [indexedFamily_coboundary1] at hs
    rw [LevelTwoHistory.suffix_coboundary1]
    change (indexedFamily S (n+2)).coboundary1
      (LevelTwoHistory.physicalLevel i.castSucc)
      (BDL26RXPhysicalStarTransport.L S (n+2) (Edge n i) h u.center
        (first S n sigma i) (second S n sigma tau i u))=_
    rw [indexedFamily_coboundary1]
    funext z
    have hz := congrFun hs z
    change (BDL26RZMap1CoordinateBridge.tannerCoboundary1 (state S (i.val+2)).presentation
      (BDL26RXPhysicalStarTransport.L S (n+2) (Edge n i) h u.center
        (first S n sigma i) (second S n sigma tau i u))) z=
      (actualInputs S n sigma i.castSucc).val z+(actualInputs S n tau i.castSucc).val z at hz ⊢
    exact hz
  · dsimp only [A,B]
    rw [LevelTwoHistory.suffix_selected_map1,LevelTwoHistory.suffix_coboundary0]
    change ((indexedDecoderData S (n+2)).selectedMap (Edge n i)).map1
      (BDL26RXPhysicalStarTransport.L S (n+2) (Edge n i) h u.center
        (first S n sigma i) (second S n sigma tau i u))=
      u.word+(actualOutput S n sigma i).correction+(actualOutput S n tau i).correction+
        (indexedFamily S (n+2)).coboundary0 (LevelTwoHistory.physicalLevel i.succ)
          (BDL26RXPhysicalStarTransport.Phi S (n+2) (Edge n i) h u.center
            (first S n sigma i) (second S n sigma tau i u))
    rw [indexedFamily_coboundary0]
    have he := hr.2.1
    rw [BDL26RXErrorPullback.updated,rx_first,rx_second,originalOutput_correction S n sigma i,
      originalOutput_correction S n tau i,indexedFamily_coboundary0] at he
    funext q
    have hq := congrFun he q
    change (((indexedDecoderData S (n+2)).selectedMap (Edge n i)).map1
      (BDL26RXPhysicalStarTransport.L S (n+2) (Edge n i) h u.center
        (first S n sigma i) (second S n sigma tau i u))) q=
      ((first S n sigma i) q+(second S n sigma tau i u) q)+
        (actualOutput S n sigma i).correction q+(actualOutput S n tau i).correction q+
        (BDL26RZMap1CoordinateBridge.tannerCoboundary0 (state S (i.val+3)).presentation
          (BDL26RXPhysicalStarTransport.Phi S (n+2) (Edge n i) h u.center
            (first S n sigma i) (second S n sigma tau i u))) q at hq
    have hab := congrFun (representatives_difference S n sigma tau i u) q
    change (first S n sigma i) q+(second S n sigma tau i u) q=u.word q at hab
    rw [hab] at hq
    change (((indexedDecoderData S (n+2)).selectedMap (Edge n i)).map1
      (BDL26RXPhysicalStarTransport.L S (n+2) (Edge n i) h u.center
        (first S n sigma i) (second S n sigma tau i u))) q=
      u.word q+(actualOutput S n sigma i).correction q+(actualOutput S n tau i).correction q+
        (BDL26RZMap1CoordinateBridge.tannerCoboundary0 (state S (i.val+3)).presentation
          (BDL26RXPhysicalStarTransport.Phi S (n+2) (Edge n i) h u.center
            (first S n sigma i) (second S n sigma tau i u))) q
    exact hq
def rzPotential (i : StepIndex n) (h : ¬(Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) : (Data S n).family.Cochain0 i.succ :=
  Classical.choose (BDL26RZPhysicalXStarTransport.two_run S (n+2) (Edge n i) h
    (by change 3 ≤ i.val+2; simp only [Edge,LevelTwoHistory.physicalStep_val] at h; omega)
    u.center (first S n sigma i) (second S n sigma tau i u)
    (rz_localized S n sigma tau i h u))
theorem rzPotential_full (i : StepIndex n) (h : ¬(Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) :
    BDL26RZFiniteBlockTransport.Pullback S (n+2) (Edge n i) h
      (BDL26RZPhysicalXStarTransport.Q0 S (n+2) (Edge n i) h u.center)
      (BDL26RZPhysicalXStarTransport.Z0 S (n+2) (Edge n i) h u.center)
      (first S n sigma i) (second S n sigma tau i u) (rzPotential S n sigma tau i h u) :=
  (Classical.choose_spec (BDL26RZPhysicalXStarTransport.two_run S (n+2) (Edge n i) h
    (by change 3 ≤ i.val+2; simp only [Edge,LevelTwoHistory.physicalStep_val] at h; omega)
    u.center (first S n sigma i) (second S n sigma tau i u)
    (rz_localized S n sigma tau i h u))).1
def rzResult (i : StepIndex n) (h : ¬(Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) : StepResult S n sigma tau i u := by
  have hp := rzPotential_full S n sigma tau i h u
  have above : 3 ≤ (Edge n i).val := by
    change 3 ≤ i.val+2
    simp only [Edge,LevelTwoHistory.physicalStep_val] at h
    omega
  refine {
    lower := {
      word := BDL26RZFiniteBlockTransport.lowerError S (n+2) (Edge n i) h
        (first S n sigma i) (second S n sigma tau i u)
      center := BDL26RZPhysicalXStarTransport.downX S (n+2) (Edge n i) h u.center
      supported := BDL26RZPhysicalXStarTransport.lower_physical_supported S (n+2) (Edge n i) h
        above u.center _ _ (rz_localized S n sigma tau i h u)
      syndrome := ?_ }
    potential := rzPotential S n sigma tau i h u
    equation := ?_ }
  · have hs := hp.2.1
    rw [rz_first,rz_second,originalOutput_coarse S n sigma i,
      originalOutput_coarse S n tau i,indexedFamily_coboundary1] at hs
    rw [LevelTwoHistory.suffix_coboundary1]
    change (indexedFamily S (n+2)).coboundary1
      (LevelTwoHistory.physicalLevel i.castSucc)
      (BDL26RZFiniteBlockTransport.lowerError S (n+2) (Edge n i) h
        (first S n sigma i) (second S n sigma tau i u))=_
    rw [indexedFamily_coboundary1]
    funext z
    have hz := congrFun hs z
    change (BDL26RZMap1CoordinateBridge.tannerCoboundary1 (state S (i.val+2)).presentation
      (BDL26RZFiniteBlockTransport.lowerError S (n+2) (Edge n i) h
        (first S n sigma i) (second S n sigma tau i u))) z=
      (actualInputs S n sigma i.castSucc).val z+(actualInputs S n tau i.castSucc).val z at hz ⊢
    exact hz
  · rw [LevelTwoHistory.suffix_selected_map1,LevelTwoHistory.suffix_coboundary0]
    change ((indexedDecoderData S (n+2)).selectedMap (Edge n i)).map1
      (BDL26RZFiniteBlockTransport.lowerError S (n+2) (Edge n i) h
        (first S n sigma i) (second S n sigma tau i u))=
      u.word+(actualOutput S n sigma i).correction+(actualOutput S n tau i).correction+
        (indexedFamily S (n+2)).coboundary0 (LevelTwoHistory.physicalLevel i.succ)
          (rzPotential S n sigma tau i h u)
    rw [indexedFamily_coboundary0]
    have he := hp.1
    rw [BDL26RZErrorPullback.updated,rz_first,rz_second,originalOutput_correction S n sigma i,
      originalOutput_correction S n tau i,indexedFamily_coboundary0] at he
    funext q
    have hq := congrFun he q
    change (((indexedDecoderData S (n+2)).selectedMap (Edge n i)).map1
      (BDL26RZFiniteBlockTransport.lowerError S (n+2) (Edge n i) h
        (first S n sigma i) (second S n sigma tau i u))) q=
      ((first S n sigma i) q+(second S n sigma tau i u) q)+
        (actualOutput S n sigma i).correction q+(actualOutput S n tau i).correction q+
        (BDL26RZMap1CoordinateBridge.tannerCoboundary0 (state S (i.val+3)).presentation (rzPotential S n sigma tau i h u)) q at hq
    have hab := congrFun (representatives_difference S n sigma tau i u) q
    change (first S n sigma i) q+(second S n sigma tau i u) q=u.word q at hab
    rw [hab] at hq
    change (((indexedDecoderData S (n+2)).selectedMap (Edge n i)).map1
      (BDL26RZFiniteBlockTransport.lowerError S (n+2) (Edge n i) h
        (first S n sigma i) (second S n sigma tau i u))) q=
      u.word q+(actualOutput S n sigma i).correction q+(actualOutput S n tau i).correction q+
        (BDL26RZMap1CoordinateBridge.tannerCoboundary0 (state S (i.val+3)).presentation (rzPotential S n sigma tau i h u)) q
    exact hq
def step (i : StepIndex n) (u : LocalizedWord S n sigma tau i.succ) : StepResult S n sigma tau i u :=
  if h : (Edge n i).val%2=0 then rxResult S n sigma tau i h u
  else rzResult S n sigma tau i h u
def down (b : Nat) (hb : b ≤ n)
    (u : LocalizedWord S n sigma tau ⟨b,Nat.lt_succ_of_le hb⟩)
    (a : LevelIndex n) (ha : a.val ≤ b) : LocalizedWord S n sigma tau a := by
  cases b with
  | zero =>
      have he : (⟨0,Nat.lt_succ_of_le hb⟩ : LevelIndex n)=a := Fin.ext (by change 0 = a.val; omega)
      exact he ▸ u
  | succ b =>
      if h : a.val=b+1 then
        exact (show (⟨b+1,Nat.lt_succ_of_le hb⟩ : LevelIndex n)=a from Fin.ext h.symm) ▸ u
      else
        exact down b (by omega) (step S n sigma tau ⟨b,by omega⟩ u).lower a (by omega)
termination_by b
variable (top : LocalizedWord S n sigma tau (TopIndex n))
def path (a : LevelIndex n) : LocalizedWord S n sigma tau a :=
  down S n sigma tau n (Nat.le_refl _) top a (Nat.le_of_lt_succ a.isLt)
def edgePotential (i : StepIndex n) : (Data S n).family.Cochain0 i.succ :=
  (step S n sigma tau i (path S n sigma tau top i.succ)).potential
def potentialTerm (a b : LevelIndex n) (i : StepIndex n) : (Data S n).family.Cochain0 b :=
  if h : a.val< (i.succ).val ∧ (i.succ).val≤b.val then
    intervalMap0 (Data S n) i.succ b h.2 (edgePotential S n sigma tau top i)
  else 0
def intervalPotential (a b : LevelIndex n) : (Data S n).family.Cochain0 b :=
  ∑ i : StepIndex n, potentialTerm S n sigma tau top a b i
section PhysicalEndpoint
variable (e : (Data S n).family.Cochain1 (TopIndex n))
variable (x : (state S (n+2)).presentation.X) (he : hammingSupport e ⊆ star S n (TopIndex n) x)
def initial : LocalizedWord S n sigma (perturbTop S n sigma e) (TopIndex n) where
  word := e
  center := x
  supported := he
  syndrome := by
    rw [actualInputs_top,actualInputs_top]
    exact (perturbTop_difference S n sigma e).symm
def actualDescent (a : LevelIndex n) : LocalizedWord S n sigma (perturbTop S n sigma e) a :=
  path S n sigma (perturbTop S n sigma e) (initial S n sigma e x he) a
def actualPotential (a b : LevelIndex n) : (Data S n).family.Cochain0 b :=
  intervalPotential S n sigma (perturbTop S n sigma e) (initial S n sigma e x he) a b
end PhysicalEndpoint
def elementaryCenter (S : OddScale) (n : Nat)
    (q : (state S (n+2)).presentation.Q) : (state S (n+2)).presentation.X :=
  ((state S (n+2)).admissible.toTannerSquareAdmissible.xqRoot q).1
theorem elementary_support (S : OddScale) (n : Nat) (q : (state S (n+2)).presentation.Q) :
    hammingSupport (canonicalBasisWord (F := BDL26Field) q) ⊆ star S n (TopIndex n) (elementaryCenter S n q) := by
  intro r hr
  have hrq : r=q := by
    by_contra hn
    have hz : canonicalBasisWord (F := BDL26Field) q r=0 := by simp [canonicalBasisWord,hn]
    exact (Finset.mem_filter.mp hr).2 hz
  subst r
  exact (BDL26RXPhysicalStarTransport.mem_physicalXStar _ _ _).mpr
    ((state S (n+2)).admissible.toTannerSquareAdmissible.xqRoot q).2
end QEC.Coding.BDL26LocalizedHistoryErrorDescent


