-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
-- name    : QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T06:11:12.047206+00:00
-- url     : https://prove2.me/theorems/79dec9c1-718b-4e3a-a190-a4c02cc81e4f
-- title:
--   RZFinite Block Transport
-- statement:
--   Definitions and structural lemmas for RZFinite Block Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean

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
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalWordPush_single
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
namespace QEC.Coding.BDL26RZFiniteBlockTransport
open BDL26FiniteAlternatingCore
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26ReplacementCochainMaps BDL26LevelTwoDistance BDL26IndexedDecoder
open MultiscaleDecoder RZCoarseGraining RZCoarseGrainingData
open scoped BigOperators Classical
namespace Coordinates
variable (P : TannerSquarePresentation) (S : OddScale)
def qBlocks (Q0 : Finset P.Q) : Finset (RZQ P S) :=
  Finset.univ.filter fun p => match p with
    | .inl _ => False
    | .inr ⟨q,_⟩ => q ∈ Q0
def zBlocks (Z0 : Finset P.Z) : Finset (RZQ P S) :=
  Finset.univ.filter fun p => match p with
    | .inl ⟨z,_⟩ => z ∈ Z0
    | .inr _ => False
def neighborZ (Q0 : Finset P.Q) : Finset P.Z :=
  Finset.univ.filter fun z => ∃ q ∈ Q0, P.qz q z=true
def zplus (Q0 : Finset P.Q) (Z0 : Finset P.Z) : Finset P.Z := Z0 ∪ neighborZ P Q0
def inputBlocks (Q0 : Finset P.Q) (Z0 : Finset P.Z) : Finset (RZQ P S) :=
  qBlocks P S Q0 ∪ zBlocks P S Z0
def star (Q0 : Finset P.Q) (Z0 : Finset P.Z) : Finset (RZQ P S) :=
  inputBlocks P S Q0 (zplus P Q0 Z0)
def potentialStar (Q0 : Finset P.Q) (Z0 : Finset P.Z) : Finset (RZX P S) :=
  Finset.univ.filter fun p => match p with
    | .inl (.inl ⟨z,_⟩) => z ∈ zplus P Q0 Z0
    | .inl (.inr ⟨q,_⟩) => q ∈ Q0
    | .inr _ => False
def syndromeBlocks (Z0 : Finset P.Z) : Finset (RZZ P S) :=
  Finset.univ.filter fun p => p.1 ∈ Z0
@[simp] theorem mem_qBlocks_q (Q0 : Finset P.Q) (q : P.Q)
    (v : QDoubleCylinderVertex (transposePresentation P) q S) :
    (Sum.inr ⟨q,v⟩ : RZQ P S) ∈ qBlocks P S Q0 ↔ q ∈ Q0 := by simp [qBlocks]
@[simp] theorem mem_zBlocks_z (Z0 : Finset P.Z) (z : P.Z)
    (e : ZDoubleCylinderEdge P z S) :
    (Sum.inl ⟨z,e⟩ : RZQ P S) ∈ zBlocks P S Z0 ↔ z ∈ Z0 := by simp [zBlocks]
@[simp] theorem mem_input_q (Q0 : Finset P.Q) (Z0 : Finset P.Z) (q : P.Q)
    (v : QDoubleCylinderVertex (transposePresentation P) q S) :
    (Sum.inr ⟨q,v⟩ : RZQ P S) ∈ inputBlocks P S Q0 Z0 ↔ q ∈ Q0 := by
  simp [inputBlocks,qBlocks,zBlocks]
@[simp] theorem mem_input_z (Q0 : Finset P.Q) (Z0 : Finset P.Z) (z : P.Z)
    (e : ZDoubleCylinderEdge P z S) :
    (Sum.inl ⟨z,e⟩ : RZQ P S) ∈ inputBlocks P S Q0 Z0 ↔ z ∈ Z0 := by
  simp [inputBlocks,qBlocks,zBlocks]
@[simp] theorem oldX_not_potentialStar (Q0 : Finset P.Q) (Z0 : Finset P.Z)
    (x : P.X) (copy : BDL26FiniteTannerSquare.Two) : (Sum.inr (x,copy) : RZX P S) ∉ potentialStar P S Q0 Z0 := by
  simp [potentialStar]
end Coordinates
def reindex {α β : Type} (h : α=β) :
    Word BDL26FiniteTannerSquare.Field α ≃ₗ[BDL26FiniteTannerSquare.Field] Word BDL26FiniteTannerSquare.Field β := by
  cases h
  exact LinearEquiv.refl _ _
theorem reindex_apply {α β : Type} (h : α=β) (w : Word BDL26FiniteTannerSquare.Field α) (x : β) :
    reindex h w x=w ((Equiv.cast h).symm x) := by cases h; rfl
open BDL26RZDecoderAdapter BDL26RZErrorPullback
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val % 2=0)
abbrev Old := (state S i.val).presentation
include odd in
theorem actual_rz_state : state S (i.val+1)=rzState S (state S i.val) := by
  change nextState S i.val (state S i.val)=_
  exact if_neg odd
def upper_eq : (state S (i.val+1)).presentation=
    rzReplacementPresentation (Old S depth i) (state S i.val).admissible.toTannerSquareAdmissible S :=
  congrArg ConstructionState.presentation (actual_rz_state S depth i odd)
def coord0 : FamilyX S depth i.succ ≃ RZX (Old S depth i) S :=
  Equiv.cast (congrArg TannerSquarePresentation.X (upper_eq S depth i odd))
def coord1 : FamilyQ S depth i.succ ≃ RZQ (Old S depth i) S :=
  Equiv.cast (congrArg TannerSquarePresentation.Q (upper_eq S depth i odd))
def coord2 : FamilyZ S depth i.succ ≃ RZZ (Old S depth i) S :=
  Equiv.cast (congrArg TannerSquarePresentation.Z (upper_eq S depth i odd))
def read0 : Potential S depth i ≃ₗ[BDL26FiniteTannerSquare.Field] Word BDL26FiniteTannerSquare.Field (RZX (Old S depth i) S) :=
  reindex (congrArg TannerSquarePresentation.X (upper_eq S depth i odd))
def read1 : Upper S depth i ≃ₗ[BDL26FiniteTannerSquare.Field] Word BDL26FiniteTannerSquare.Field (RZQ (Old S depth i) S) :=
  reindex (congrArg TannerSquarePresentation.Q (upper_eq S depth i odd))
def read2 : (indexedFamily S depth).Cochain2 i.succ ≃ₗ[BDL26FiniteTannerSquare.Field]
    Word BDL26FiniteTannerSquare.Field (RZZ (Old S depth i) S) :=
  reindex (congrArg TannerSquarePresentation.Z (upper_eq S depth i odd))
@[simp] theorem read0_apply (p : Potential S depth i) (x : RZX (Old S depth i) S) :
    read0 S depth i odd p x=p ((coord0 S depth i odd).symm x) := reindex_apply _ _ _
@[simp] theorem read1_apply (w : Upper S depth i) (q : RZQ (Old S depth i) S) :
    read1 S depth i odd w q=w ((coord1 S depth i odd).symm q) := reindex_apply _ _ _
@[simp] theorem read2_apply (w : (indexedFamily S depth).Cochain2 i.succ)
    (z : RZZ (Old S depth i) S) :
    read2 S depth i odd w z=w ((coord2 S depth i odd).symm z) := reindex_apply _ _ _
def qBlocks (Q0 : Finset (Old S depth i).Q) : Finset (FamilyQ S depth i.succ) :=
  Finset.univ.filter fun q => coord1 S depth i odd q ∈ Coordinates.qBlocks (Old S depth i) S Q0
def zBlocks (Z0 : Finset (Old S depth i).Z) : Finset (FamilyQ S depth i.succ) :=
  Finset.univ.filter fun q => coord1 S depth i odd q ∈ Coordinates.zBlocks (Old S depth i) S Z0
def inputBlocks (Q0 : Finset (Old S depth i).Q) (Z0 : Finset (Old S depth i).Z) :
    Finset (FamilyQ S depth i.succ) := qBlocks S depth i odd Q0 ∪ zBlocks S depth i odd Z0
def star (Q0 : Finset (Old S depth i).Q) (Z0 : Finset (Old S depth i).Z) :
    Finset (FamilyQ S depth i.succ) :=
  inputBlocks S depth i odd Q0 (Coordinates.zplus (Old S depth i) Q0 Z0)
def potentialStar (Q0 : Finset (Old S depth i).Q) (Z0 : Finset (Old S depth i).Z) :
    Finset (FamilyX S depth i.succ) :=
  Finset.univ.filter fun x => coord0 S depth i odd x ∈ Coordinates.potentialStar (Old S depth i) S Q0 Z0
def syndromeBlocks (Z0 : Finset (Old S depth i).Z) : Finset (FamilyZ S depth i.succ) :=
  Finset.univ.filter fun z => coord2 S depth i odd z ∈ Coordinates.syndromeBlocks (Old S depth i) S Z0
def lowerError (a b : Upper S depth i) : Lower S depth i :=
  (rzData S depth i odd).induced.correctionProjection (a+b)
def Pullback (Q0 : Finset (Old S depth i).Q) (Z0 : Finset (Old S depth i).Z)
    (a b : Upper S depth i) (p : Potential S depth i) : Prop :=
  ((indexedDecoderData S depth).selectedMap i).map1 (lowerError S depth i odd a b)=
    updated S depth i odd a b+(indexedFamily S depth).coboundary0 i.succ p ∧
  (indexedFamily S depth).coboundary1 i.castSucc (lowerError S depth i odd a b)=
    (run S depth i odd a).coarse.val+(run S depth i odd b).coarse.val ∧
  ((indexedDecoderData S depth).selectedMap i).map2
    ((run S depth i odd a).coarse.val+(run S depth i odd b).coarse.val)=
      (indexedFamily S depth).coboundary1 i.succ (updated S depth i odd a b) ∧
  (indexedFamily S depth).coboundary1 i.succ ((indexedFamily S depth).coboundary0 i.succ p)=0 ∧
  hammingSupport (lowerError S depth i odd a b) ⊆ Q0 ∧
  hammingSupport ((indexedFamily S depth).coboundary1 i.castSucc (lowerError S depth i odd a b)) ⊆
    Coordinates.neighborZ (Old S depth i) Q0 ∧
  hammingSupport (updated S depth i odd a b) ⊆ star S depth i odd Q0 Z0 ∧
  hammingSupport (((indexedDecoderData S depth).selectedMap i).map1 (lowerError S depth i odd a b)) ⊆
    star S depth i odd Q0 Z0 ∧
  hammingSupport p ⊆ potentialStar S depth i odd Q0 Z0 ∧
  hammingSupport ((indexedFamily S depth).coboundary0 i.succ p) ⊆ star S depth i odd Q0 Z0 ∧
  hammingSupport (((indexedDecoderData S depth).selectedMap i).map2
    ((run S depth i odd a).coarse.val+(run S depth i odd b).coarse.val)) ⊆
      syndromeBlocks S depth i odd (Coordinates.neighborZ (Old S depth i) Q0)
def coordinateOwner (p : FamilyQ S depth i.succ) : Vertex (Old S depth i) :=
  rzCorrectionOwner (Old S depth i) S (coord1 S depth i odd p)
def footprintQ (a b : Upper S depth i) : Finset (Old S depth i).Q :=
  Finset.univ.filter fun q => ∃ p ∈ hammingSupport (a+b), coordinateOwner S depth i odd p=.q q
def footprintZ (a b : Upper S depth i) : Finset (Old S depth i).Z :=
  Finset.univ.filter fun z => ∃ p ∈ hammingSupport (a+b), coordinateOwner S depth i odd p=.z z
def incidentQ (x : (Old S depth i).X) : Finset (Old S depth i).Q :=
  Finset.univ.filter fun q => (Old S depth i).xq x q=true
section TopHistory
open BDL26OwnerIncidenceMasks BDL26CanonicalHistoryMarks
def topStep (j : Nat) : StepIndex (2*j+4) := ⟨2*j+3,by omega⟩
theorem topStep_odd (j : Nat) : ¬ (topStep j).val % 2=0 := by simp only [topStep]; omega
def topOutput (j : Nat) (a : Upper S (2*j+4) (topStep j)) :
    AssemblyStepOutput (indexedDecoderData S (2*j+4)) (topStep j) :=
  BDL26CanonicalHistoryMarks.outputAt S (2*j+2)
    (errorSyndrome S (2*j+4) (topStep j) a) (Fin.last (2*j+1))
end TopHistory
section ConstructorWitness
def seedQEdge (S : OddScale) : QDoubleCylinderEdge (transposePresentation baseTannerSquarePresentation)
    (4 : BaseQubit) S := Sum.inr ⟨(0 : BaseX),by decide⟩
def seedOutsideCoordinate (S : OddScale) : RZQ baseTannerSquarePresentation S :=
  .inl ⟨(1 : BaseZ),qToZDoubleCylinderEdge baseTannerSquarePresentation
    baseTannerSquareAdmissibleV4.toTannerSquareAdmissible (4 : BaseQubit) (1 : BaseZ) (by decide) S (seedQEdge S)⟩
end ConstructorWitness
end QEC.Coding.BDL26RZFiniteBlockTransport


