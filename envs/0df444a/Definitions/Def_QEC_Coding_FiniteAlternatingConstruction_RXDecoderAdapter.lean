-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
-- name    : QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T04:57:16.261212+00:00
-- url     : https://prove2.me/theorems/2472274f-d0ff-436d-a692-7d1b384486b6
-- title:
--   RXDecoder Adapter
-- statement:
--   Definitions and structural lemmas for RXDecoder Adapter, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Lifts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Representative
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Graph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Sectors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Induced
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Budgets
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_LocalComplexes
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Theorems.Thm_P2M_QEC_Coding_wordLinearMapTranspose_toLin__apply_6aba8976cbc7
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_correctionRegion_mem
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_syndromeRegion_mem
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
import Theorems.Thm_QEC_Coding_BDL26IndexedDecoder_indexedDecoderData_selected_rx
import Theorems.Thm_QEC_Coding_BDL26IndexedDecoder_selectedMap_eq
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_actualGQZ1_eq_diagonal
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_actualGXQ0_eq_adjacency
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_correction_sectors_cover
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_correction_sectors_disjoint
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_distance_one_comp
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCq_budget
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCq_decomposition
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCq_delta0_zero
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCq_finrank
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCq_global_restriction
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCx_budget
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCx_decomposition
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCx_exact
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCx_global_restriction
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCx_lift_restriction
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCx_lift_sum_restriction
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_map1_representative_decomposition
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_map2_auxiliary_zero
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_map2_diagonal
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qCorrectionEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qCorrectionSector_regions
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qFlow_at_q
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qFlow_at_x
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qFlow_radius_one
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qRepresentative_section
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qRepresentative_value
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qSector_regions
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qSyndromeEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_regionExtension_apply
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_region_restrict_extend
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_region_restrict_extend_disjoint
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_syndrome_sectors_cover
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_syndrome_sectors_disjoint
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_transpose_wordEquiv_symm
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xCorrectionEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xFlow_at_x
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xFlow_radius_one
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xLift_other
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xLift_same
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xSector_regions
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xSyndromeEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_zPairEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_zSector_regions
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_zSyndromeEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_z_correction_empty
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_coboundary0_eq
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_coboundary1_eq
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalWordPush_single
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzFace_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzQ_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzX_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzZ_card
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_map2Coord_canonicalBasis
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary0_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary1_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rxMap_commutes_coboundary0
import Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rxMap_commutes_coboundary1
import Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_fiberPart_apply
import Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_fiberRegion_disjoint
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
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_copiedQ_image_copy
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_copiedQ_image_vertical
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_verticalZ_image_copy
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_verticalZ_image_vertical
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_rx_coarse_graining_selected
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_rx_total_eq_components
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
namespace QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph BDL26AlternatingCochain MultiscaleDecoder RXCoarseGraining
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped Classical BigOperators
structure EndpointData (P U : TannerSquarePresentation) (S : OddScale) where
  lx : LocalComplexData P.X U.Z U.Q
  lq : LocalComplexData P.Q U.Z U.Q
  lz : LocalComplexData P.Z U.Z U.Q
  cx : ∀ x : P.X, ChainComplexData BDL26Field
    (Word BDL26Field (DoubleCylinderVertex P x S))
    (Word BDL26Field (LocalRegionIndex (lx.correctionRegion x)))
    (Word BDL26Field (LocalRegionIndex (lx.syndromeRegion x)))
  cq : ∀ q : P.Q, ChainComplexData BDL26Field (Word BDL26Field (Fin 0))
    (Word BDL26Field (LocalRegionIndex (lq.correctionRegion q)))
    (Word BDL26Field (LocalRegionIndex (lq.syndromeRegion q)))
  cxExact : ∀ x, LinearMap.ker (wordLinearMapTranspose (cx x).boundary2) =
    LinearMap.range (wordLinearMapTranspose (cx x).boundary1)
  cqFinrank : ∀ q, Module.finrank BDL26Field (cq q).middleCohomology = 1
  xFlow : ∀ x, Word BDL26Field (LocalRegionIndex (lx.correctionRegion x)) →ₗ[BDL26Field]
    Word BDL26Field U.Z
  qFlow : ∀ q, Word BDL26Field (LocalRegionIndex (lq.correctionRegion q)) →ₗ[BDL26Field]
    Word BDL26Field U.Z
  xLift : ∀ x, Word BDL26Field (DoubleCylinderVertex P x S) →ₗ[BDL26Field] Word BDL26Field U.X
  xRestriction : ∀ x e,
    restrictWordLinear (lx.syndromeRegion x) (tannerCoboundary1 U e) =
      wordLinearMapTranspose (cx x).boundary2 (restrictWordLinear (lx.correctionRegion x) e)
  qRestriction : ∀ q e, (∀ x, restrictWordLinear (lx.correctionRegion x) e = 0) →
    restrictWordLinear (lq.syndromeRegion q) (tannerCoboundary1 U e) =
      wordLinearMapTranspose (cq q).boundary2 (restrictWordLinear (lq.correctionRegion q) e)
  xLiftRestriction : ∀ x s,
    restrictWordLinear (lx.correctionRegion x) (tannerCoboundary0 U (xLift x s)) =
      wordLinearMapTranspose (cx x).boundary1 s
  xLiftSum : ∀ (s : ∀ x, Word BDL26Field (DoubleCylinderVertex P x S)) x,
    restrictWordLinear (lx.correctionRegion x) (tannerCoboundary0 U (∑ y, xLift y (s y))) =
      wordLinearMapTranspose (cx x).boundary1 (s x)
  qDelta0Zero : ∀ q, wordLinearMapTranspose (cq q).boundary1 = 0
  xDecomposition : ∀ x f,
    tannerCoboundary1 U (extendWordLinear (lx.correctionRegion x) f) =
      extendWordLinear (lx.syndromeRegion x) (wordLinearMapTranspose (cx x).boundary2 f) + xFlow x f
  qDecomposition : ∀ q f,
    tannerCoboundary1 U (extendWordLinear (lq.correctionRegion q) f) =
      extendWordLinear (lq.syndromeRegion q) (wordLinearMapTranspose (cq q).boundary2 f) + qFlow q f
  xBudget : ∀ x s, s ∈ LinearMap.range (wordLinearMapTranspose (cx x).boundary2) →
    ∃ f, wordLinearMapTranspose (cx x).boundary2 f = s ∧ HammingWeight (xFlow x f) ≤ HammingWeight s
  qBudget : ∀ q s, s ∈ LinearMap.range (wordLinearMapTranspose (cq q).boundary2) →
    ∃ f, wordLinearMapTranspose (cq q).boundary2 f = s ∧ HammingWeight (qFlow q f) ≤ HammingWeight s
  xs : Finset U.Z
  qs : Finset U.Z
  zs : Finset U.Z
  xsRegions : xs = rxRegionUnion lx
  qsRegions : qs = rxRegionUnion lq
  zsRegions : zs = rxRegionUnion lz
  sectorsDisjoint : Disjoint xs qs ∧ Disjoint xs zs ∧ Disjoint qs zs
  sectorsCover : xs ∪ qs ∪ zs = Finset.univ
  qcs : Finset U.Q
  qcsRegions : qcs = correctionRegionUnion lq
  correctionsCover : correctionRegionUnion lx ∪ qcs = Finset.univ
  correctionsDisjoint : Disjoint (correctionRegionUnion lx) qcs
  xFlowZeroX : ∀ x f p, p ∈ xs → xFlow x f p = 0
  qFlowZeroQ : ∀ q f p, p ∈ qs → qFlow q f p = 0
  qFlowZeroX : ∀ q f p, p ∈ xs → qFlow q f p = 0
  xSyndromeDisjoint : ∀ x y, x ≠ y → Disjoint (lx.syndromeRegion x) (lx.syndromeRegion y)
  qSyndromeDisjoint : ∀ q r, q ≠ r → Disjoint (lq.syndromeRegion q) (lq.syndromeRegion r)
  zSyndromeDisjoint : ∀ z w, z ≠ w → Disjoint (lz.syndromeRegion z) (lz.syndromeRegion w)
  xCorrectionDisjoint : ∀ x y, x ≠ y → Disjoint (lx.correctionRegion x) (lx.correctionRegion y)
  qCorrectionDisjoint : ∀ q r, q ≠ r → Disjoint (lq.correctionRegion q) (lq.correctionRegion r)
  xqCorrectionDisjoint : ∀ x q, Disjoint (lx.correctionRegion x) (lq.correctionRegion q)
  zCorrectionEmpty : ∀ z, lz.correctionRegion z = ∅
  representative : ∀ q, (cq q).middleCohomology →ₗ[BDL26Field] (cq q).middleCocycleCode.carrier
  representativeSection : ∀ q h, (cq q).middleCoboundaryInCocycles.mkQ (representative q h) = h
  representativeSupport : ∀ q h p, p.1 ∉ qcs → (representative q h).1 p = 0
  quotientEquiv : (∀ q, (cq q).middleCohomology) ≃ₗ[BDL26Field] Word BDL26Field P.Q
  map0 : Word BDL26Field P.X →ₗ[BDL26Field] Word BDL26Field U.X
  map1 : Word BDL26Field P.Q →ₗ[BDL26Field] Word BDL26Field U.Q
  map2 : Word BDL26Field P.Z →ₗ[BDL26Field] Word BDL26Field U.Z
  map1Representative : ∀ w, map1 w = ∑ q, extendWordLinear (lq.correctionRegion q)
    (representative q (quotientEquiv.symm w q)).1
  pairEquiv : (P.Z × Fin 2) ≃ LocalRegionIndex zs
  map2Diagonal : ∀ w z b, map2 w (pairEquiv (z,b)).1 = w z
  map2Auxiliary : ∀ w p, p ∉ zs → map2 w p = 0
  topCenter : U.Z → RXVertex P.X P.Q P.Z
  correctionOwner : U.Q → RXVertex P.X P.Q P.Z
  centerX : ∀ x p, p ∈ lx.syndromeRegion x ↔ topCenter p = .inl x
  centerQ : ∀ q p, p ∈ lq.syndromeRegion q ↔ topCenter p = .inr (.inl q)
  centerZ : ∀ z p, p ∈ lz.syndromeRegion z ↔ topCenter p = .inr (.inr z)
  ownerX : ∀ x p, p ∈ lx.correctionRegion x ↔ correctionOwner p = .inl x
  ownerQ : ∀ q p, p ∈ lq.correctionRegion q ↔ correctionOwner p = .inr (.inl q)
  ownerZ : ∀ z p, p ∈ lz.correctionRegion z ↔ correctionOwner p = .inr (.inr z)
  centerPair : ∀ z b, topCenter (pairEquiv (z,b)).1 = .inr (.inr z)
  xRadius : ∀ x f p, xFlow x f p ≠ 0 →
    DirectedGraph.distance (rxLevel P).graph (.inl x) (topCenter p) ≤ 1
  qRadius : ∀ q f p, qFlow q f p ≠ 0 →
    DirectedGraph.distance (rxLevel P).graph (.inr (.inl q)) (topCenter p) ≤ 1
theorem relabel_fiber_iff (P : TannerSquarePresentation)
    {C : Type} [Fintype C] [DecidableEq C] (owner : C → Vertex P)
    (v : RXVertex P.X P.Q P.Z) (p : C) :
    p ∈ fiberRegion owner (vertexEquiv P v) ↔ (vertexEquiv P).symm (owner p) = v := by
  constructor
  · intro hp
    have h := (Finset.mem_filter.mp hp).2
    rw [h, Equiv.symm_apply_apply]
  · intro hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ p, ?_⟩
    have h := congrArg (vertexEquiv P) hp
    simpa only [Equiv.apply_symm_apply] using h
theorem actualZ_decEq (P : TannerSquarePresentation) (S : OddScale) :
    (rxReplacementPresentation P S).data.zDecidableEq =
      (inferInstance : DecidableEq (RX2 P S)) := Subsingleton.elim _ _
theorem extendWordLinear_decEq {T : Type} [Fintype T]
    (d e : DecidableEq T) (Y : Finset T) (f : Word BDL26Field (LocalRegionIndex Y)) :
    @extendWordLinear BDL26Field _ T _ d Y f = @extendWordLinear BDL26Field _ T _ e Y f := by
  cases Subsingleton.elim d e
  rfl
noncomputable def actualEndpoint (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    EndpointData P (rxReplacementPresentation P S) S where
  lx := ⟨(localX P S).syndromeRegion, (localX P S).correctionRegion⟩
  lq := ⟨(localQ P S).syndromeRegion, (localQ P S).correctionRegion⟩
  lz := ⟨(localZ P S).syndromeRegion, (localZ P S).correctionRegion⟩
  cx := localCx P S
  cq := localCq P S
  cxExact := localCx_exact P A.toTannerSquareAdmissibleV3 R S
  cqFinrank := localCq_finrank P A.toTannerSquareAdmissible S
  xFlow := fun x => (xFlow P S x).comp (wordEquiv (xCorrectionEquiv P S x)).symm.toLinearMap
  qFlow := fun q => (qFlow P S q).comp (wordEquiv (qCorrectionEquiv P S q)).symm.toLinearMap
  xLift := xLift P S
  xRestriction := by
    intro x e
    rw [rxPresentation_coboundary1_eq P A R S]
    exact localCx_global_restriction P S e x
  qRestriction := by
    intro q e hx
    rw [rxPresentation_coboundary1_eq P A R S]
    exact localCq_global_restriction P S e hx q
  xLiftRestriction := by
    intro x w
    rw [rxPresentation_coboundary0_eq P A R S]
    exact localCx_lift_restriction P S x w
  xLiftSum := by
    intro w x
    rw [rxPresentation_coboundary0_eq P A R S]
    exact localCx_lift_sum_restriction P S w x
  qDelta0Zero := localCq_delta0_zero P S
  xDecomposition := by
    intro x f
    rw [rxPresentation_coboundary1_eq P A R S]
    exact (localCx_decomposition P S x f).trans
      (congrArg (fun w => w + xFlow P S x ((wordEquiv (xCorrectionEquiv P S x)).symm f))
        (extendWordLinear_decEq _ _ _ _))
  qDecomposition := by
    intro q f
    rw [rxPresentation_coboundary1_eq P A R S]
    exact (localCq_decomposition P S q f).trans
      (congrArg (fun w => w + qFlow P S q ((wordEquiv (qCorrectionEquiv P S q)).symm f))
        (extendWordLinear_decEq _ _ _ _))
  xBudget := localCx_budget P A R S
  qBudget := localCq_budget P S
  xs := xSector P S
  qs := qSector P S
  zs := zSector P S
  xsRegions := by
    rw [actualZ_decEq]
    exact xSector_regions P S
  qsRegions := by
    rw [actualZ_decEq]
    exact qSector_regions P S
  zsRegions := by
    rw [actualZ_decEq]
    exact zSector_regions P S
  sectorsDisjoint := syndrome_sectors_disjoint P S
  sectorsCover := by
    rw [actualZ_decEq]
    exact syndrome_sectors_cover P S
  qcs := qCorrectionSector P S
  qcsRegions := qCorrectionSector_regions P S
  correctionsCover := correction_sectors_cover P S
  correctionsDisjoint := correction_sectors_disjoint P S
  xFlowZeroX := by
    intro x f p hp
    obtain ⟨y,hy⟩ := (Finset.mem_filter.mp hp).2
    rcases p with (⟨z,a⟩ | ⟨q,e⟩) | ⟨z,c⟩
    · exact xFlow_at_x P S x z _ a
    · cases hy
    · cases hy
  qFlowZeroQ := by
    intro q f p hp
    obtain ⟨r,hr⟩ := (Finset.mem_filter.mp hp).2
    rcases p with (⟨x,a⟩ | ⟨s,e⟩) | ⟨z,c⟩
    · cases hr
    · exact qFlow_at_q P S q s _ e
    · cases hr
  qFlowZeroX := by
    intro q f p hp
    obtain ⟨y,hy⟩ := (Finset.mem_filter.mp hp).2
    rcases p with (⟨x,a⟩ | ⟨s,e⟩) | ⟨z,c⟩
    · exact qFlow_at_x P S q _ x a
    · cases hy
    · cases hy
  xSyndromeDisjoint := fun _ _ h => fiberRegion_disjoint _ (fun he => h (Vertex.x.inj he))
  qSyndromeDisjoint := fun _ _ h => fiberRegion_disjoint _ (fun he => h (Vertex.q.inj he))
  zSyndromeDisjoint := fun _ _ h => fiberRegion_disjoint _ (fun he => h (Vertex.z.inj he))
  xCorrectionDisjoint := fun _ _ h => fiberRegion_disjoint _ (fun he => h (Vertex.x.inj he))
  qCorrectionDisjoint := fun _ _ h => fiberRegion_disjoint _ (fun he => h (Vertex.q.inj he))
  xqCorrectionDisjoint := fun x q => fiberRegion_disjoint (rxCorrectionOwner P S)
    (first := Vertex.x x) (second := Vertex.q q) (by intro he; cases he)
  zCorrectionEmpty := z_correction_empty P S
  representative := qRepresentative P A.toTannerSquareAdmissible S
  representativeSection := qRepresentative_section P A.toTannerSquareAdmissible S
  representativeSupport := by
    intro q h p hp
    apply (hp ?_).elim
    apply Finset.mem_filter.mpr
    have ho := (relabel_fiber_iff P (rxCorrectionOwner P S) (.inr (.inl q)) p.1).mp p.2
    have he : rxCorrectionOwner P S p.1 = Vertex.q q := by
      apply (vertexEquiv P).symm.injective
      exact ho
    exact ⟨Finset.mem_univ _, q, he⟩
  quotientEquiv := qCohomologyEquiv P A.toTannerSquareAdmissible S
  map0 := rxMap0Coord P S
  map1 := rxMap1Coord P S
  map2 := rxMap2Coord P S
  map1Representative := map1_representative_decomposition P A.toTannerSquareAdmissible S
  pairEquiv := zPairEquiv P S
  map2Diagonal := map2_diagonal P S
  map2Auxiliary := map2_auxiliary_zero P S
  topCenter := topCenter P S
  correctionOwner := fun p => (vertexEquiv P).symm (rxCorrectionOwner P S p)
  centerX := fun x p => relabel_fiber_iff P (rxSyndromeOwner P S) (.inl x) p
  centerQ := fun q p => relabel_fiber_iff P (rxSyndromeOwner P S) (.inr (.inl q)) p
  centerZ := fun z p => relabel_fiber_iff P (rxSyndromeOwner P S) (.inr (.inr z)) p
  ownerX := fun x p => relabel_fiber_iff P (rxCorrectionOwner P S) (.inl x) p
  ownerQ := fun q p => relabel_fiber_iff P (rxCorrectionOwner P S) (.inr (.inl q)) p
  ownerZ := fun z p => relabel_fiber_iff P (rxCorrectionOwner P S) (.inr (.inr z)) p
  centerPair := fun _ _ => rfl
  xRadius := fun x f p hp => xFlow_radius_one P A.toTannerSquareAdmissible S x _ p hp
  qRadius := fun q f p hp => qFlow_radius_one P S q _ p hp
open BDL26IndexedDecoder BDL26AlternatingCochain
def transportEndpoint (P U V : TannerSquarePresentation) (S : OddScale)
    (h : U = V) (G : EndpointData P V S) : EndpointData P U S := h.symm ▸ G
theorem transportEndpoint_maps (P U V : TannerSquarePresentation) (S : OddScale)
    (h : U = V) (G : EndpointData P V S) :
    HEq (transportEndpoint P U V S h G).map0 G.map0 ∧
    HEq (transportEndpoint P U V S h G).map1 G.map1 ∧
    HEq (transportEndpoint P U V S h G).map2 G.map2 := by
  cases h
  exact ⟨HEq.rfl, HEq.rfl, HEq.rfl⟩
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
theorem stateSuccRX (h : i.val % 2 = 0) :
    state S (i.val + 1) = rxState S (state S i.val) := by
  change nextState S i.val (state S i.val) = _
  exact if_pos h
noncomputable def endpointAt (h : i.val % 2 = 0) :
    EndpointData (state S i.val).presentation (state S (i.val + 1)).presentation S :=
  transportEndpoint _ _ _ S (congrArg ConstructionState.presentation (stateSuccRX S depth i h))
    (actualEndpoint (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S)
theorem endpointAt_maps (h : i.val % 2 = 0) :
    (endpointAt S depth i h).map0 = (indexedEdgeMap S depth i).map0 ∧
    (endpointAt S depth i h).map1 = (indexedEdgeMap S depth i).map1 ∧
    (endpointAt S depth i h).map2 = (indexedEdgeMap S depth i).map2 := by
  have hf := transportEndpoint_maps _ _ _ S
    (congrArg ConstructionState.presentation (stateSuccRX S depth i h))
    (actualEndpoint (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S)
  have hm := indexedDecoderData_selected_rx S depth i h
  rw [selectedMap_eq] at hm
  exact ⟨eq_of_heq (hf.1.trans hm.1.symm),
    eq_of_heq (hf.2.1.trans hm.2.1.symm), eq_of_heq (hf.2.2.trans hm.2.2.symm)⟩
noncomputable def rxLx (h : i.val % 2 = 0) := (endpointAt S depth i h).lx
noncomputable def rxLq (h : i.val % 2 = 0) := (endpointAt S depth i h).lq
noncomputable def rxLz (h : i.val % 2 = 0) := (endpointAt S depth i h).lz
noncomputable def localComplexesAt (h : i.val % 2 = 0) :
    RXLocalComplexData
      (X0 := fun x => DoubleCylinderVertex (state S i.val).presentation x S)
      (Q0 := fun _ => Fin 0) (Z0 := fun _ => Fin 0)
      (Z1 := fun _ => Fin 0) (Z2 := fun _ => Fin 2)
      (indexedDecoderData S depth) i (rxLx S depth i h) (rxLq S depth i h) (rxLz S depth i h) where
  cx := (endpointAt S depth i h).cx
  cq := (endpointAt S depth i h).cq
  cz := rxCz (state S i.val).presentation
theorem decoder_coboundary0 (j : LevelIndex depth) :
    (indexedDecoderData S depth).family.coboundary0 j =
      tannerCoboundary0 (state S j.val).presentation := indexedFamily_coboundary0 S depth j
theorem decoder_coboundary1 (j : LevelIndex depth) :
    (indexedDecoderData S depth).family.coboundary1 j =
      tannerCoboundary1 (state S j.val).presentation := indexedFamily_coboundary1 S depth j
noncomputable def supportAt (h : i.val % 2 = 0) :
    RXSupportDecomposition (indexedDecoderData S depth) i (localComplexesAt S depth i h) := by
  let G := endpointAt S depth i h
  refine
    { cxFlow := G.xFlow
      cqFlow := G.qFlow
      cxLift0 := G.xLift
      cqLift0 := fun _ => 0
      cxDelta1_restriction := ?_
      cxDelta1_restriction_global := ?_
      cqDelta1_restriction := ?_
      cqDelta1_restriction_global := ?_
      cxDelta0_restriction := ?_
      cxDelta0_sum_decomposition := ?_
      cxDelta1_decomposition := ?_
      cqDelta1_decomposition := ?_
      cxFlow_outside_x_sector := ?_
      cqFlow_outside_q_sector := ?_
      cx_regions_pairwise_disjoint := G.xSyndromeDisjoint
      cq_regions_pairwise_disjoint := G.qSyndromeDisjoint }
  · intro x f
    have hr := G.xRestriction x (extendWordLinear (G.lx.correctionRegion x) f)
    exact (congrArg (fun d => restrictWordLinear (G.lx.syndromeRegion x)
      (d (extendWordLinear (G.lx.correctionRegion x) f)))
      (decoder_coboundary1 S depth i.succ)).trans
        (hr.trans (congrArg (wordLinearMapTranspose (G.cx x).boundary2)
          (region_restrict_extend (G.lx.correctionRegion x) f)))
  · intro x e
    rw [decoder_coboundary1]
    exact G.xRestriction x e
  · intro q f
    have hr := G.qRestriction q (extendWordLinear (G.lq.correctionRegion q) f)
      (fun x => region_restrict_extend_disjoint _ _ (G.xqCorrectionDisjoint x q).symm f)
    exact (congrArg (fun d => restrictWordLinear (G.lq.syndromeRegion q)
      (d (extendWordLinear (G.lq.correctionRegion q) f)))
      (decoder_coboundary1 S depth i.succ)).trans
        (hr.trans (congrArg (wordLinearMapTranspose (G.cq q).boundary2)
          (region_restrict_extend (G.lq.correctionRegion q) f)))
  · intro q e hx
    rw [decoder_coboundary1]
    exact G.qRestriction q e hx
  · intro x s
    rw [decoder_coboundary0]
    exact G.xLiftRestriction x s
  · intro s x
    rw [decoder_coboundary0]
    exact G.xLiftSum s x
  · intro x f
    rw [decoder_coboundary1]
    exact G.xDecomposition x f
  · intro q f
    rw [decoder_coboundary1]
    exact G.qDecomposition q f
  · intro x f p hp
    exact G.xFlowZeroX x f p (G.xsRegions.symm ▸ hp)
  · intro q f p hp
    exact G.qFlowZeroQ q f p (G.qsRegions.symm ▸ hp)
noncomputable def rxContract (h : i.val % 2 = 0) :
    RXConstructionContractSlice
      (X0 := fun x => DoubleCylinderVertex (state S i.val).presentation x S)
      (Q0 := fun _ => Fin 0) (Z0 := fun _ => Fin 0)
      (Z1 := fun _ => Fin 0) (Z2 := fun _ => Fin 2)
      (indexedDecoderData S depth) i (rxLx S depth i h) (rxLq S depth i h) (rxLz S depth i h) where
  rx_local_complexes := localComplexesAt S depth i h
  rx_local_cohomology :=
    { cx_h1_ker_eq_range := (endpointAt S depth i h).cxExact
      cq_h1_finrank := (endpointAt S depth i h).cqFinrank }
  support_decomposition := supportAt S depth i h
  local_boundary_weight_budgets :=
    { cx := (endpointAt S depth i h).xBudget
      cq := (endpointAt S depth i h).qBudget }
noncomputable def representativeAt (h : i.val % 2 = 0) (q : (state S i.val).presentation.Q) :
    ((rxContract S depth i h).rx_local_complexes.cq q).middleCohomology →ₗ[BDL26Field]
      ((rxContract S depth i h).rx_local_complexes.cq q).middleCocycleCode.carrier :=
  (endpointAt S depth i h).representative q
theorem representativeAt_section (h : i.val % 2 = 0)
    (q : (state S i.val).presentation.Q) (v) :
    ((rxContract S depth i h).rx_local_complexes.cq q).middleCoboundaryInCocycles.mkQ
      (representativeAt S depth i h q v) = v :=
  (endpointAt S depth i h).representativeSection q v
theorem representativeAt_support (h : i.val % 2 = 0)
    (q : (state S i.val).presentation.Q) (v)
    (p : LocalRegionIndex ((rxLq S depth i h).correctionRegion q))
    (hp : p.1 ∉ (endpointAt S depth i h).qcs) :
    (representativeAt S depth i h q v).1 p = 0 :=
  (endpointAt S depth i h).representativeSupport q v p hp
noncomputable def quotientEquivAt (h : i.val % 2 = 0) :
    (∀ q, ((rxContract S depth i h).rx_local_complexes.cq q).middleCohomology) ≃ₗ[BDL26Field]
      (indexedDecoderData S depth).family.Cochain1 i.castSucc :=
  (endpointAt S depth i h).quotientEquiv
noncomputable def rxData (h : i.val % 2 = 0) :
    RXCoarseGrainingData
      (X0 := fun x => DoubleCylinderVertex (state S i.val).presentation x S)
      (Q0 := fun _ => Fin 0) (Z0 := fun _ => Fin 0)
      (Z1 := fun _ => Fin 0) (Z2 := fun _ => Fin 2)
      (indexedDecoderData S depth) i (rxLx S depth i h) (rxLq S depth i h) (rxLz S depth i h) := by
  let P := (state S i.val).presentation
  let A := (state S i.val).admissible.toTannerSquareAdmissible
  let G := endpointAt S depth i h
  refine
    { induced :=
        { adjacencyMap := rxXQAdjacency P
          gXQ0 := actualGXQ0 P A S
          gXQ0_eq_adjacency := actualGXQ0_eq_adjacency P A S
          qzAdjacency := rxQZAdjacency P
          gQZ1 := actualGQZ1 P S
          gQZ1_eq_diagonal_comp := actualGQZ1_eq_diagonal P A S
          zSector := G.zs
          zPairEquiv := G.pairEquiv
          map2_diagonal := ?_
          map2_auxiliary_zero := ?_ }
      contract := rxContract S depth i h
      xSector := G.xs
      qSector := G.qs
      zSector := G.zs
      zSector_eq_induced := rfl
      xSector_eq_regions := G.xsRegions
      qSector_eq_regions := G.qsRegions
      sectors_pairwise_disjoint := G.sectorsDisjoint
      sectors_cover := G.sectorsCover
      qCorrectionSector := G.qcs
      qCorrectionSector_eq_regions := G.qcsRegions
      correction_sectors_cover := G.correctionsCover
      correction_sectors_disjoint := G.correctionsDisjoint
      qRepresentativeSector := G.qcs
      qRepresentativeSector_subset_qCorrectionSector := Finset.Subset.refl _
      cqRepresentative := representativeAt S depth i h
      cqRepresentative_mkQ := representativeAt_section S depth i h
      cqRepresentative_supported := representativeAt_support S depth i h
      qCohomologyEquiv := quotientEquivAt S depth i h
      rxMap1_eq_cqRepresentative := ?_
      cqDelta0_sum_decomposition := ?_
      cqFlow_outside_xSector := G.qFlowZeroX
      levelGraph := rxLevel P
      levelGraph_kind_x := fun _ => rfl
      levelGraph_kind_q := fun _ => rfl
      levelGraph_kind_z := fun _ => rfl
      topCenter := G.topCenter
      coarseCenter := fun z => .inr (.inr z)
      coarseCenter_is_z := fun z => ⟨z,rfl⟩
      topCenter_coarse_pair := G.centerPair
      topCenter_x_iff := G.centerX
      topCenter_q_iff := G.centerQ
      topCenter_z_iff := G.centerZ
      zSector_eq_regions := G.zsRegions
      lz_regions_pairwise_disjoint := G.zSyndromeDisjoint
      cx_correction_regions_pairwise_disjoint := G.xCorrectionDisjoint
      cq_correction_regions_pairwise_disjoint := G.qCorrectionDisjoint
      cxFlow_radius_one := G.xRadius
      cqFlow_radius_one := G.qRadius
      distance_one_comp := distance_one_comp _ }
  · intro w z b
    change (indexedEdgeMap S depth i).map2 w (G.pairEquiv (z,b)).1 = w z
    rw [← (endpointAt_maps S depth i h).2.2]
    exact G.map2Diagonal w z b
  · intro w p hp
    change (indexedEdgeMap S depth i).map2 w p = 0
    rw [← (endpointAt_maps S depth i h).2.2]
    exact G.map2Auxiliary w p hp
  · intro w
    change (indexedEdgeMap S depth i).map1 w = _
    rw [← (endpointAt_maps S depth i h).2.1]
    exact G.map1Representative w
  · intro s
    change (indexedFamily S depth).coboundary0 i.succ (∑ q, (0 : _ →ₗ[BDL26Field] _) (s q)) =
      ∑ q, extendWordLinear (G.lq.correctionRegion q) (wordLinearMapTranspose (G.cq q).boundary1 (s q))
    simp only [LinearMap.zero_apply, Finset.sum_const_zero, map_zero, G.qDelta0Zero]
open RXCoarseGrainingData
theorem upper_odd (h : i.val % 2 = 0) : i.succ.val % 2 = 1 := by
  change (i.val + 1) % 2 = 1
  omega
noncomputable def rxStepOutput (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ) :
    AssemblyStepOutput (indexedDecoderData S depth) i :=
  AuditedLeafAdapters.rxOutput (rxData S depth i h) (upper_odd depth i h) sigma
noncomputable def orderedOwners : List (Vertex (state S i.val).presentation) :=
  (Finset.univ : Finset (RXVertex (state S i.val).presentation.X
    (state S i.val).presentation.Q (state S i.val).presentation.Z)).toList.map
      (vertexEquiv (state S i.val).presentation)
theorem rxStepOutput_localComponents (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ) :
    (rxStepOutput S depth i h sigma).localComponents =
      (Finset.univ : Finset (RXVertex (state S i.val).presentation.X
        (state S i.val).presentation.Q (state S i.val).presentation.Z)).toList.map
          (fun v => (rxLocalComponents (rxData S depth i h)).component v sigma.val) := rfl
theorem orderedOwners_length (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ) :
    (orderedOwners S depth i).length = (rxStepOutput S depth i h sigma).localComponents.length := by
  simp only [orderedOwners, rxStepOutput_localComponents, List.length_map]
noncomputable def componentOwner (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (j : Fin (rxStepOutput S depth i h sigma).localComponents.length) :
    RXVertex (state S i.val).presentation.X (state S i.val).presentation.Q
      (state S i.val).presentation.Z :=
  (Finset.univ : Finset (RXVertex (state S i.val).presentation.X
    (state S i.val).presentation.Q (state S i.val).presentation.Z)).toList.get
      ⟨j.val, by simpa only [rxStepOutput_localComponents, List.length_map] using j.isLt⟩
noncomputable def rxStepOutput_ownerLabels (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ) :
    AssemblyOwnerLabels (V := Vertex (state S i.val).presentation)
      (indexedDecoderData S depth) i (rxStepOutput S depth i h sigma) :=
  AssemblyOwnerLabels.ofOwners _ (fun j => some
    (vertexEquiv (state S i.val).presentation (componentOwner S depth i h sigma j)))
noncomputable def correctionOwnerAt (h : i.val % 2 = 0) :=
  (endpointAt S depth i h).correctionOwner
abbrev EndpointQCoordinates {P U : TannerSquarePresentation} {S : OddScale}
    (G : EndpointData P U S) :=
  ∀ q : P.Q, QDoubleCylinderVertex P q S ≃ LocalRegionIndex (G.lq.correctionRegion q)
noncomputable def transportQCoordinates
    (P U V : TannerSquarePresentation) (S : OddScale) (h : U = V)
    (G : EndpointData P V S) (E : EndpointQCoordinates G) :
    EndpointQCoordinates (transportEndpoint P U V S h G) := by
  cases h
  exact E
def EndpointQKernel {P U : TannerSquarePresentation} {S : OddScale}
    (G : EndpointData P U S) (E : EndpointQCoordinates G) : Prop :=
  ∀ q (w : Word BDL26Field (LocalRegionIndex (G.lq.correctionRegion q))),
    wordLinearMapTranspose (G.cq q).boundary2 w = 0 →
    ∀ v, w (E q v) = w (E q (0, Sum.inl (Sum.inl ())))
noncomputable def rxQVertexEquiv (h : i.val % 2 = 0)
    (q : (state S i.val).presentation.Q) :
    QDoubleCylinderVertex (state S i.val).presentation q S ≃
      LocalRegionIndex ((rxLq S depth i h).correctionRegion q) :=
  transportQCoordinates _ _ _ S
    (congrArg ConstructionState.presentation (stateSuccRX S depth i h))
    (actualEndpoint (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S)
    (qCorrectionEquiv (state S i.val).presentation S) q
def EndpointConstantMap1 {P U : TannerSquarePresentation} {S : OddScale}
    (G : EndpointData P U S) : Prop :=
  ∀ c : Word BDL26Field P.Q, G.map1 c =
    ∑ q, extendWordLinear (G.lq.correctionRegion q) (fun _ => c q)
def EndpointXBoundaryZero {P U : TannerSquarePresentation} {S : OddScale}
    (G : EndpointData P U S) : Prop :=
  ∀ x f z b, tannerCoboundary1 U (extendWordLinear (G.lx.correctionRegion x) f)
    (G.pairEquiv (z,b)).val = 0
def EndpointQBoundaryFlow {P U : TannerSquarePresentation} {S : OddScale}
    (G : EndpointData P U S) : Prop :=
  ∀ q f z b, tannerCoboundary1 U (extendWordLinear (G.lq.correctionRegion q) f)
    (G.pairEquiv (z,b)).val = G.qFlow q f (G.pairEquiv (z,b)).val
end QEC.Coding.BDL26RXDecoderAdapter
noncomputable section
namespace QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph BDL26AlternatingCochain MultiscaleDecoder RXCoarseGraining
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped Classical BigOperators
def presentationAt (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) : LevelIndex 1 → TannerSquarePresentation :=
  Fin.cases P (fun _ => rxReplacementPresentation P S)
abbrev PresentationX (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (i : LevelIndex 1) := (presentationAt P A R S i).X
abbrev PresentationQ (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (i : LevelIndex 1) := (presentationAt P A R S i).Q
abbrev PresentationZ (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (i : LevelIndex 1) := (presentationAt P A R S i).Z
def presentationFamily (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) : BDL26CochainFamily 1
      (PresentationX P A R S) (PresentationQ P A R S) (PresentationZ P A R S) where
  complex := fun i => BDL26LevelTwoDecoder.presentationComplex (presentationAt P A R S i)
theorem presentationFamily_coboundary0 (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (i : LevelIndex 1) :
    (presentationFamily P A R S).coboundary0 i = tannerCoboundary0 (presentationAt P A R S i) := by
  apply LinearMap.ext
  intro e
  funext q
  exact wordLinearMapTranspose_toLin'_apply _ e q
theorem presentationFamily_coboundary1 (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (i : LevelIndex 1) :
    (presentationFamily P A R S).coboundary1 i = tannerCoboundary1 (presentationAt P A R S i) := by
  apply LinearMap.ext
  intro e
  funext z
  exact wordLinearMapTranspose_toLin'_apply _ e z
def presentationMap (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) : BDL26CochainMap (presentationFamily P A R S) (0 : StepIndex 1) where
  map0 := rxMap0Coord P S
  map1 := rxMap1Coord P S
  map2 := rxMap2Coord P S
  commutes_coboundary0 := by
    rw [presentationFamily_coboundary0,presentationFamily_coboundary0]
    exact by
      erw [rxPresentation_coboundary0_eq P A R S]
      exact rxMap_commutes_coboundary0 P A.toTannerSquareAdmissible S
  commutes_coboundary1 := by
    rw [presentationFamily_coboundary1,presentationFamily_coboundary1]
    exact by
      erw [rxPresentation_coboundary1_eq P A R S]
      exact rxMap_commutes_coboundary1 P S
def presentationDecoderData (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) : BDL26DecoderData 1
      (PresentationX P A R S) (PresentationQ P A R S) (PresentationZ P A R S) where
  family := presentationFamily P A R S
  rxMap := fun i => Fin.cases (presentationMap P A R S) (fun j => Fin.elim0 j) i
  rzMap := fun i => Fin.cases (presentationMap P A R S) (fun j => Fin.elim0 j) i
@[simp] theorem presentationDecoderData_selectedMap (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) :
    (presentationDecoderData P A R S).selectedMap (0 : StepIndex 1) =
      presentationMap P A R S := rfl
theorem presentationEndpoint_maps (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) :
    (actualEndpoint P A R S).map0 = (presentationMap P A R S).map0 ∧
    (actualEndpoint P A R S).map1 = (presentationMap P A R S).map1 ∧
    (actualEndpoint P A R S).map2 = (presentationMap P A R S).map2 :=
  ⟨rfl,rfl,rfl⟩
noncomputable def presentationLx (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) := (actualEndpoint P A R S).lx
noncomputable def presentationLq (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) := (actualEndpoint P A R S).lq
noncomputable def presentationLz (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) := (actualEndpoint P A R S).lz
noncomputable def presentationLocalComplexes (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) :
    RXLocalComplexData
      (X0 := fun x => DoubleCylinderVertex P x S)
      (Q0 := fun _ => Fin 0) (Z0 := fun _ => Fin 0)
      (Z1 := fun _ => Fin 0) (Z2 := fun _ => Fin 2)
      (presentationDecoderData P A R S) (0 : StepIndex 1) (presentationLx P A R S) (presentationLq P A R S) (presentationLz P A R S) where
  cx := (actualEndpoint P A R S).cx
  cq := (actualEndpoint P A R S).cq
  cz := rxCz P
noncomputable def presentationSupport (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) :
    RXSupportDecomposition (presentationDecoderData P A R S) (0 : StepIndex 1) (presentationLocalComplexes P A R S) := by
  let G := actualEndpoint P A R S
  refine
    { cxFlow := G.xFlow
      cqFlow := G.qFlow
      cxLift0 := G.xLift
      cqLift0 := fun _ => 0
      cxDelta1_restriction := ?_
      cxDelta1_restriction_global := ?_
      cqDelta1_restriction := ?_
      cqDelta1_restriction_global := ?_
      cxDelta0_restriction := ?_
      cxDelta0_sum_decomposition := ?_
      cxDelta1_decomposition := ?_
      cqDelta1_decomposition := ?_
      cxFlow_outside_x_sector := ?_
      cqFlow_outside_q_sector := ?_
      cx_regions_pairwise_disjoint := G.xSyndromeDisjoint
      cq_regions_pairwise_disjoint := G.qSyndromeDisjoint }
  · intro x f
    have hr := G.xRestriction x (extendWordLinear (G.lx.correctionRegion x) f)
    exact (congrArg (fun d => restrictWordLinear (G.lx.syndromeRegion x)
      (d (extendWordLinear (G.lx.correctionRegion x) f)))
      (presentationFamily_coboundary1 P A R S (1 : LevelIndex 1))).trans
        (hr.trans (congrArg (wordLinearMapTranspose (G.cx x).boundary2)
          (region_restrict_extend (G.lx.correctionRegion x) f)))
  · intro x e
    exact (congrArg (fun d => restrictWordLinear (G.lx.syndromeRegion x) (d e))
      (presentationFamily_coboundary1 P A R S (1 : LevelIndex 1))).trans
        (G.xRestriction x e)
  · intro q f
    have hr := G.qRestriction q (extendWordLinear (G.lq.correctionRegion q) f)
      (fun x => region_restrict_extend_disjoint _ _ (G.xqCorrectionDisjoint x q).symm f)
    exact (congrArg (fun d => restrictWordLinear (G.lq.syndromeRegion q)
      (d (extendWordLinear (G.lq.correctionRegion q) f)))
      (presentationFamily_coboundary1 P A R S (1 : LevelIndex 1))).trans
        (hr.trans (congrArg (wordLinearMapTranspose (G.cq q).boundary2)
          (region_restrict_extend (G.lq.correctionRegion q) f)))
  · intro q e hx
    exact (congrArg (fun d => restrictWordLinear (G.lq.syndromeRegion q) (d e))
      (presentationFamily_coboundary1 P A R S (1 : LevelIndex 1))).trans
        (G.qRestriction q e hx)
  · intro x s
    exact (congrArg (fun d => restrictWordLinear (G.lx.correctionRegion x) (d (G.xLift x s)))
      (presentationFamily_coboundary0 P A R S (1 : LevelIndex 1))).trans
        (G.xLiftRestriction x s)
  · intro s x
    exact (congrArg (fun d => restrictWordLinear (G.lx.correctionRegion x)
      (d (∑ y, G.xLift y (s y))))
      (presentationFamily_coboundary0 P A R S (1 : LevelIndex 1))).trans (G.xLiftSum s x)
  · intro x f
    exact (congrArg (fun d => d (extendWordLinear (G.lx.correctionRegion x) f))
      (presentationFamily_coboundary1 P A R S (1 : LevelIndex 1))).trans
        (G.xDecomposition x f)
  · intro q f
    exact (congrArg (fun d => d (extendWordLinear (G.lq.correctionRegion q) f))
      (presentationFamily_coboundary1 P A R S (1 : LevelIndex 1))).trans
        (G.qDecomposition q f)
  · intro x f p hp
    exact G.xFlowZeroX x f p (G.xsRegions.symm ▸ hp)
  · intro q f p hp
    exact G.qFlowZeroQ q f p (G.qsRegions.symm ▸ hp)
noncomputable def presentationContract (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) :
    RXConstructionContractSlice
      (X0 := fun x => DoubleCylinderVertex P x S)
      (Q0 := fun _ => Fin 0) (Z0 := fun _ => Fin 0)
      (Z1 := fun _ => Fin 0) (Z2 := fun _ => Fin 2)
      (presentationDecoderData P A R S) (0 : StepIndex 1) (presentationLx P A R S) (presentationLq P A R S) (presentationLz P A R S) where
  rx_local_complexes := presentationLocalComplexes P A R S
  rx_local_cohomology :=
    { cx_h1_ker_eq_range := (actualEndpoint P A R S).cxExact
      cq_h1_finrank := (actualEndpoint P A R S).cqFinrank }
  support_decomposition := presentationSupport P A R S
  local_boundary_weight_budgets :=
    { cx := (actualEndpoint P A R S).xBudget
      cq := (actualEndpoint P A R S).qBudget }
noncomputable def presentationRepresentative (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (q : P.Q) :
    ((presentationContract P A R S).rx_local_complexes.cq q).middleCohomology →ₗ[BDL26Field]
      ((presentationContract P A R S).rx_local_complexes.cq q).middleCocycleCode.carrier :=
  (actualEndpoint P A R S).representative q
theorem presentationRepresentative_section (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (q : P.Q) (v) :
    ((presentationContract P A R S).rx_local_complexes.cq q).middleCoboundaryInCocycles.mkQ
      (presentationRepresentative P A R S q v) = v :=
  (actualEndpoint P A R S).representativeSection q v
theorem presentationRepresentative_support (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (q : P.Q) (v)
    (p : LocalRegionIndex ((presentationLq P A R S).correctionRegion q))
    (hp : p.1 ∉ (actualEndpoint P A R S).qcs) :
    (presentationRepresentative P A R S q v).1 p = 0 :=
  (actualEndpoint P A R S).representativeSupport q v p hp
noncomputable def presentationQuotientEquiv (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) :
    (∀ q, ((presentationContract P A R S).rx_local_complexes.cq q).middleCohomology) ≃ₗ[BDL26Field]
      (presentationDecoderData P A R S).family.Cochain1 (0 : LevelIndex 1) :=
  (actualEndpoint P A R S).quotientEquiv
noncomputable def presentationData (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) :
    RXCoarseGrainingData
      (X0 := fun x => DoubleCylinderVertex P x S)
      (Q0 := fun _ => Fin 0) (Z0 := fun _ => Fin 0)
      (Z1 := fun _ => Fin 0) (Z2 := fun _ => Fin 2)
      (presentationDecoderData P A R S) (0 : StepIndex 1) (presentationLx P A R S) (presentationLq P A R S) (presentationLz P A R S) := by
  let G := actualEndpoint P A R S
  refine
    { induced :=
        { adjacencyMap := rxXQAdjacency P
          gXQ0 := actualGXQ0 P A.toTannerSquareAdmissible S
          gXQ0_eq_adjacency := actualGXQ0_eq_adjacency P A.toTannerSquareAdmissible S
          qzAdjacency := rxQZAdjacency P
          gQZ1 := actualGQZ1 P S
          gQZ1_eq_diagonal_comp := actualGQZ1_eq_diagonal P A.toTannerSquareAdmissible S
          zSector := G.zs
          zPairEquiv := G.pairEquiv
          map2_diagonal := ?_
          map2_auxiliary_zero := ?_ }
      contract := presentationContract P A R S
      xSector := G.xs
      qSector := G.qs
      zSector := G.zs
      zSector_eq_induced := rfl
      xSector_eq_regions := G.xsRegions
      qSector_eq_regions := G.qsRegions
      sectors_pairwise_disjoint := G.sectorsDisjoint
      sectors_cover := G.sectorsCover
      qCorrectionSector := G.qcs
      qCorrectionSector_eq_regions := G.qcsRegions
      correction_sectors_cover := G.correctionsCover
      correction_sectors_disjoint := G.correctionsDisjoint
      qRepresentativeSector := G.qcs
      qRepresentativeSector_subset_qCorrectionSector := Finset.Subset.refl _
      cqRepresentative := presentationRepresentative P A R S
      cqRepresentative_mkQ := presentationRepresentative_section P A R S
      cqRepresentative_supported := presentationRepresentative_support P A R S
      qCohomologyEquiv := presentationQuotientEquiv P A R S
      rxMap1_eq_cqRepresentative := ?_
      cqDelta0_sum_decomposition := ?_
      cqFlow_outside_xSector := G.qFlowZeroX
      levelGraph := rxLevel P
      levelGraph_kind_x := fun _ => rfl
      levelGraph_kind_q := fun _ => rfl
      levelGraph_kind_z := fun _ => rfl
      topCenter := G.topCenter
      coarseCenter := fun z => .inr (.inr z)
      coarseCenter_is_z := fun z => ⟨z,rfl⟩
      topCenter_coarse_pair := G.centerPair
      topCenter_x_iff := G.centerX
      topCenter_q_iff := G.centerQ
      topCenter_z_iff := G.centerZ
      zSector_eq_regions := G.zsRegions
      lz_regions_pairwise_disjoint := G.zSyndromeDisjoint
      cx_correction_regions_pairwise_disjoint := G.xCorrectionDisjoint
      cq_correction_regions_pairwise_disjoint := G.qCorrectionDisjoint
      cxFlow_radius_one := G.xRadius
      cqFlow_radius_one := G.qRadius
      distance_one_comp := distance_one_comp _ }
  · intro w z b
    change (presentationMap P A R S).map2 w (G.pairEquiv (z,b)).1 = w z
    rw [← (presentationEndpoint_maps P A R S).2.2]
    exact G.map2Diagonal w z b
  · intro w p hp
    change (presentationMap P A R S).map2 w p = 0
    rw [← (presentationEndpoint_maps P A R S).2.2]
    exact G.map2Auxiliary w p hp
  · intro w
    change (presentationMap P A R S).map1 w = _
    rw [← (presentationEndpoint_maps P A R S).2.1]
    exact G.map1Representative w
  · intro s
    change (presentationFamily P A R S).coboundary0 (1 : LevelIndex 1) (∑ q, (0 : _ →ₗ[BDL26Field] _) (s q)) =
      ∑ q, extendWordLinear (G.lq.correctionRegion q) (wordLinearMapTranspose (G.cq q).boundary1 (s q))
    simp only [LinearMap.zero_apply, Finset.sum_const_zero, map_zero, G.qDelta0Zero]
    rfl
open RXCoarseGrainingData
noncomputable def presentationOutput
    (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (sigma : (presentationFamily P A R S).Syndrome (1 : LevelIndex 1)) :
    AssemblyStepOutput (presentationDecoderData P A R S) (0 : StepIndex 1) := by
  let G := presentationData P A R S
  have hs := rx_coarse_graining_selected G rfl sigma
  have hrange : rxCoarseWord G sigma.val ∈
      LinearMap.range ((presentationFamily P A R S).coboundary1 (0 : LevelIndex 1)) := by
    obtain ⟨coarse,correction,hword,hcorrection,hrelation,hrest⟩ := hs
    rw [← hword]
    exact coarse.property
  let actualCoarse : (presentationFamily P A R S).Syndrome (0 : LevelIndex 1) :=
    ⟨rxCoarseWord G sigma.val,hrange⟩
  let actualCorrection := rxCorrectionTotal G sigma.val
  let pieces := (Finset.univ : Finset (RXVertex P.X P.Q P.Z)).toList.map
    (fun v => (rxLocalComponents G).component v sigma.val)
  apply AssemblyStepOutput.ofComponents sigma actualCoarse actualCorrection pieces
  · obtain ⟨coarse,correction,hword,hcorrection,hrelation,hrest⟩ := hs
    have hc : actualCoarse = coarse := Subtype.ext hword.symm
    simpa only [hc,actualCorrection,← hcorrection] using hrelation
  · dsimp [actualCorrection]
    calc
      rxCorrectionTotal G sigma.val =
          (∑ x, cxComponentTotal G sigma.val x) + ∑ q, cqComponentTotal G sigma.val q :=
        rx_total_eq_components G sigma.val
      _ = pieces.sum := by
        simp [pieces,rxLocalComponents,LocalCorrectionComponents.totalCorrection,
          Fintype.sum_sum_type]
end QEC.Coding.BDL26RXDecoderAdapter
end
namespace QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
end QEC.Coding.BDL26RXDecoderAdapter
noncomputable section
namespace QEC.Coding.BDL26RXDecoderAdapter
open BDL26IndexedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph BDL26AlternatingCochain MultiscaleDecoder RXCoarseGraining
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped Classical BigOperators
abbrev EndpointXCoordinates {P U : TannerSquarePresentation} {S : OddScale}
    (_G : EndpointData P U S) :=
  (Σ x : P.X, DoubleCylinderVertex P x S) ≃ U.X
def EndpointXLiftGeometry {P U : TannerSquarePresentation} {S : OddScale}
    (G : EndpointData P U S) (E : EndpointXCoordinates G) : Prop :=
  (∀ x w v, G.xLift x w (E ⟨x,v⟩) = w v) ∧
  (∀ x y, y ≠ x → ∀ w v, G.xLift x w (E ⟨y,v⟩) = 0) ∧
  (∀ x y, y ≠ x → ∀ w, restrictWordLinear (G.lx.correctionRegion y)
    (tannerCoboundary0 U (G.xLift x w)) = 0) ∧
  (∀ x q, P.xq x q ≠ true → ∀ w,
    restrictWordLinear (G.lq.correctionRegion q)
      (tannerCoboundary0 U (G.xLift x w)) = 0)
noncomputable def transportXCoordinates
    (P U V : TannerSquarePresentation) (S : OddScale) (h : U = V)
    (G : EndpointData P V S) (E : EndpointXCoordinates G) :
    EndpointXCoordinates (transportEndpoint P U V S h G) := by
  cases h
  exact E
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2 = 0)
def rxDegreeZeroEquiv :
    (Σ x : (state S i.val).presentation.X,
      DoubleCylinderVertex (state S i.val).presentation x S) ≃ FamilyX S depth i.succ :=
  transportXCoordinates _ _ _ S
    (congrArg ConstructionState.presentation (stateSuccRX S depth i h))
    (actualEndpoint (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S) (Equiv.refl _)
def EndpointXGradientKernel {P U : TannerSquarePresentation} {S : OddScale}
    (G : EndpointData P U S) : Prop :=
  ∀ x (w : Word BDL26Field (DoubleCylinderVertex P x S)),
    wordLinearMapTranspose (G.cx x).boundary1 w = 0 ↔
      wordLinearMapTranspose (doubleCylinderBoundary1 P x S) w = 0
end QEC.Coding.BDL26RXDecoderAdapter
noncomputable section
namespace QEC.Coding.BDL26RXDecoderAdapter
open BDL26IndexedDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26ReplacementSupport BDL26DecodingGraph
open MultiscaleDecoder
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2 = 0)
def rxPhysicalQEquiv :
    RX1 (state S i.val).presentation S ≃ FamilyQ S depth i.succ :=
  Equiv.cast (congrArg (fun C : ConstructionState => C.presentation.Q)
    (stateSuccRX S depth i h)).symm
end QEC.Coding.BDL26RXDecoderAdapter
noncomputable section
namespace QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26DecodingGraph BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical
end QEC.Coding.BDL26RXDecoderAdapter
end


