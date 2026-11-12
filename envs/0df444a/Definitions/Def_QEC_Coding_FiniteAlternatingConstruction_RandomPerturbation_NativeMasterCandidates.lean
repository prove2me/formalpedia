-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeMasterCandidates
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeMasterCandidates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T09:01:21.897845+00:00
-- url     : https://prove2.me/theorems/5e613fc1-1ce5-4b24-b3ec-d297cc9c3bb2
-- title:
--   Native Master Candidates
-- statement:
--   Definitions and structural lemmas for Native Master Candidates, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeMasterCandidates.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Mathlib.Data.List.Sublists
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_coupling_x
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_coupling_y
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_coupling_z
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_check_hermitian
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_mem_x_checkSupport
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_mem_z_checkSupport
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_levelMap_zero
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_prefixStageCost_zero
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_correctionRegion_mem
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_syndromeRegion_mem
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_evaluate_succ
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_evaluate_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_history_last
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_outputLaw_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_prefix_last
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_prefix_self
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_prefix_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_tableAt_last
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_totalStageCost_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowTotalCost_zero
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_output_label_nodup
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_triangle_labels
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_map_value
import Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_atlas_actual
import Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_corners_membership
import Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_dedup_length
import Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_dedup_membership
import Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_dedup_nodup
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_encode_injective
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_encode_member
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_index_inverse
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_streamTotalCost_zero
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_totalCost_zero
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_transferTotal_zero
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalWordPush_single
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzFace_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzQ_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzX_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzZ_card
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_map2Coord_canonicalBasis
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary0_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary1_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_centerExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_vertexExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seedPoint_eq_zero
import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_physical_zero
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_BoundaryUnit_reverse
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_foldedSquare_bottom
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_foldedSquare_diagonal
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_foldedSquare_left
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_foldedSquare_right
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_foldedSquare_top
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_lower_last_normalized
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rawFineInteger_interior
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rawFineInteger_last
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_two_complement_val
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_upper_last_normalized
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_PointCode_eval_rename
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_PointCode_reads_rename
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_PointCode_work_rename
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_blendCode_reads
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_blendCode_work
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_extendedTotalCost_zero
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_totalMaterializationCost_zero
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
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_copiedQ_image_copy
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_copiedQ_image_vertical
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_verticalZ_image_copy
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_verticalZ_image_vertical
import Theorems.Thm_QEC_Coding_CSSGibbs_badProjector_adjoint
import Theorems.Thm_QEC_Coding_CSSGibbs_bitOutcome_one
import Theorems.Thm_QEC_Coding_CSSGibbs_bitOutcome_sign
import Theorems.Thm_QEC_Coding_CSSGibbs_bitOutcome_zero
import Theorems.Thm_QEC_Coding_CSSGibbs_hermitian_cssX
import Theorems.Thm_QEC_Coding_CSSGibbs_hermitian_cssZ
import Theorems.Thm_QEC_Coding_CSSGibbs_hermitian_row
import Theorems.Thm_QEC_Coding_CSSGibbs_projector_adjoint
import Theorems.Thm_QEC_Coding_CSSGibbs_projector_square
import Theorems.Thm_QEC_Coding_CSSGibbs_realizableEmbedding_apply
import Theorems.Thm_QEC_Coding_CSSGibbs_row_adjoint
import Theorems.Thm_QEC_Coding_CSSGibbs_syndromeOutcome_apply
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_coarseSyndrome_coe
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_historicalZeroSyndromeInput_supportFitsRadiusTwo
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_decode_encode_assignment
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_decode_encode_table
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_encode_decode_assignment
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_encode_decode_table
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_mem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_notMem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_nil_mem_witnessPaths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceHistory_length
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_zero
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_barycenterMap_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
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
import Theorems.Thm_QEC_Semantics_Davies_entry_diagonal_mul
import Theorems.Thm_QEC_Semantics_Davies_entry_frequencyComponent
import Theorems.Thm_QEC_Semantics_Davies_entry_mul_diagonal
import Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_zero
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocalToRegister_one
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocalToRegister_zero
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
import Theorems.Thm_QEC_Semantics_finiteLindbladEvolutionLinearMap_zero
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_traceNorm_neg
attribute [local simp] QEC.Coding.BDL26CSSDaviesLocality.coupling_x
attribute [local simp] QEC.Coding.BDL26CSSDaviesLocality.coupling_y
attribute [local simp] QEC.Coding.BDL26CSSDaviesLocality.coupling_z
attribute [local simp] QEC.Coding.BDL26CSSHamiltonian.check_hermitian
attribute [local simp] QEC.Coding.BDL26CSSHamiltonian.mem_x_checkSupport
attribute [local simp] QEC.Coding.BDL26CSSHamiltonian.mem_z_checkSupport
attribute [local simp] QEC.Coding.BDL26CountableEmbeddingExperiment.levelMap_zero
attribute [local simp] QEC.Coding.BDL26CountableEmbeddingExperiment.prefixStageCost_zero
attribute [local simp] QEC.Coding.BDL26DecodingGraph.correctionRegion_mem
attribute [local simp] QEC.Coding.BDL26DecodingGraph.syndromeRegion_mem
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.alternatingCarrier_zero
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_target_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_target_val
attribute [local simp] QEC.Coding.BDL26FiniteEmbeddingExperiment.evaluate_succ
attribute [local simp] QEC.Coding.BDL26FiniteEmbeddingExperiment.evaluate_zero
attribute [local simp] QEC.Coding.BDL26FiniteEmbeddingExperiment.history_last
attribute [local simp] QEC.Coding.BDL26FiniteEmbeddingExperiment.outputLaw_zero
attribute [local simp] QEC.Coding.BDL26FiniteEmbeddingExperiment.prefix_last
attribute [local simp] QEC.Coding.BDL26FiniteEmbeddingExperiment.prefix_self
attribute [local simp] QEC.Coding.BDL26FiniteEmbeddingExperiment.prefix_zero
attribute [local simp] QEC.Coding.BDL26FiniteEmbeddingExperiment.tableAt_last
attribute [local simp] QEC.Coding.BDL26FiniteEmbeddingExperiment.totalStageCost_zero
attribute [local simp] QEC.Coding.BDL26FiniteTannerSquare.doubleCylinderEndInclusion_apply
attribute [local simp] QEC.Coding.BDL26IncomingRowsExecution.rowTotalCost_zero
attribute [local simp] QEC.Coding.BDL26PaidRowsComposition.streamTotalCost_zero
attribute [local simp] QEC.Coding.BDL26PaidRowsComposition.totalCost_zero
attribute [local simp] QEC.Coding.BDL26PaidRowsComposition.transferTotal_zero
attribute [local simp] QEC.Coding.BDL26RXLocalReplacement.xLocalWordPush_single
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzFace_card
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzQ_card
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzX_card
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzZ_card
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.map2Coord_canonicalBasis
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary0_canonicalBasis_apply
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1_canonicalBasis_apply
attribute [local simp] QEC.Coding.BDL26RandomPerturbation.centerExpr_eval
attribute [local simp] QEC.Coding.BDL26RandomPerturbation.vertexExpr_eval
attribute [local simp] QEC.Coding.BDL26RandomSeedEmbedding.seedPoint_eq_zero
attribute [local simp] QEC.Coding.BDL26RandomSeedEmbedding.seed_physical_zero
attribute [local simp] QEC.Coding.BDL26ReplacementEmbedding.foldedSquare_bottom
attribute [local simp] QEC.Coding.BDL26ReplacementEmbedding.foldedSquare_diagonal
attribute [local simp] QEC.Coding.BDL26ReplacementEmbedding.foldedSquare_left
attribute [local simp] QEC.Coding.BDL26ReplacementEmbedding.foldedSquare_right
attribute [local simp] QEC.Coding.BDL26ReplacementEmbedding.foldedSquare_top
attribute [local simp] QEC.Coding.BDL26ReplacementEmbedding.lower_last_normalized
attribute [local simp] QEC.Coding.BDL26ReplacementEmbedding.rawFineInteger_interior
attribute [local simp] QEC.Coding.BDL26ReplacementEmbedding.rawFineInteger_last
attribute [local simp] QEC.Coding.BDL26ReplacementEmbedding.two_complement_val
attribute [local simp] QEC.Coding.BDL26ReplacementEmbedding.upper_last_normalized
attribute [local simp] QEC.Coding.BDL26ReplacementMaterialization.PointCode.eval_rename
attribute [local simp] QEC.Coding.BDL26ReplacementMaterialization.PointCode.reads_rename
attribute [local simp] QEC.Coding.BDL26ReplacementMaterialization.PointCode.work_rename
attribute [local simp] QEC.Coding.BDL26ReplacementMaterialization.blendCode_reads
attribute [local simp] QEC.Coding.BDL26ReplacementMaterialization.blendCode_work
attribute [local simp] QEC.Coding.BDL26ReplacementMaterialization.extendedTotalCost_zero
attribute [local simp] QEC.Coding.BDL26ReplacementMaterialization.totalMaterializationCost_zero
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
attribute [local simp] QEC.Coding.CSSGibbs.badProjector_adjoint
attribute [local simp] QEC.Coding.CSSGibbs.bitOutcome_one
attribute [local simp] QEC.Coding.CSSGibbs.bitOutcome_sign
attribute [local simp] QEC.Coding.CSSGibbs.bitOutcome_zero
attribute [local simp] QEC.Coding.CSSGibbs.hermitian_cssX
attribute [local simp] QEC.Coding.CSSGibbs.hermitian_cssZ
attribute [local simp] QEC.Coding.CSSGibbs.hermitian_row
attribute [local simp] QEC.Coding.CSSGibbs.projector_adjoint
attribute [local simp] QEC.Coding.CSSGibbs.projector_square
attribute [local simp] QEC.Coding.CSSGibbs.realizableEmbedding_apply
attribute [local simp] QEC.Coding.CSSGibbs.row_adjoint
attribute [local simp] QEC.Coding.CSSGibbs.syndromeOutcome_apply
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.originalBoundary_single
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.MultiscaleDecoder.RZCoarseGraining.coarseSyndrome_coe
attribute [local simp] QEC.Coding.MultiscaleDecoder.historicalZeroSyndromeInput_supportFitsRadiusTwo
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.decode_encode_assignment
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.decode_encode_table
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.encode_decode_assignment
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.encode_decode_table
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_mem
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_notMem
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.mem_closedNeighbors
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.nil_mem_witnessPaths
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.occurrenceHistory_length
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.witnessPartition_zero
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.barycenterMap_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert
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
attribute [local simp] QEC.Semantics.Davies.entry_diagonal_mul
attribute [local simp] QEC.Semantics.Davies.entry_frequencyComponent
attribute [local simp] QEC.Semantics.Davies.entry_mul_diagonal
attribute [local simp] QEC.Semantics.Davies.frequencyComponent_zero
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocalToRegister_one
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocalToRegister_zero
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
attribute [local simp] QEC.Semantics.finiteLindbladEvolutionLinearMap_zero
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.traceNorm_neg


set_option autoImplicit false
namespace QEC.Coding.BDL26NativeMasterCandidates
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
abbrev Code := BDL26NativePresentationGenerator.Code
abbrev Run := BDL26NativeStateRows.Run
abbrev FourCodes := BDL26NativeSupportMetadata.FourCodes
abbrev Index := BDL26NativeStateRows.Index
abbrev Quad (A : Type*) := A × A × A × A
noncomputable abbrev P := BDL26NativeStateRows.P
def copyCodeQ (c : Code) : Run Code :=
  ⟨{family:=c.family,owner:=c.owner,copy:=c.copy,part:=c.part,
    p:=c.p,q:=c.q,i:=c.i,j:=c.j,k:=c.k,l:=c.l},21,1⟩
def appendQ {A : Type*} : List A → List A → Run (List A)
  | [],right => ⟨right,1,0⟩
  | a::left,right =>
      let rest := appendQ left right
      ⟨a::rest.value,rest.operations+2,rest.allocations+1⟩
theorem append_spec {A : Type*} (left right : List A) :
    (appendQ left right).value=left++right ∧
      (appendQ left right).operations=2*left.length+1 ∧
      (appendQ left right).allocations=left.length := by
  induction left with
  | nil => simp [appendQ]
  | cons a left ih =>
      simp only [appendQ,List.cons_append,List.length_cons]
      exact ⟨congrArg (a::·) ih.1,by omega,by omega⟩
def suffixQ {A B : Type*} (f : A → List A → Run (List B)) : List A → Run (List B)
  | [] => ⟨[],1,0⟩
  | a::tail =>
      let left := f a tail
      let right := suffixQ f tail
      let joined := appendQ left.value right.value
      ⟨joined.value,left.operations+right.operations+joined.operations+3,
        left.allocations+right.allocations+joined.allocations+1⟩
def suffixValues {A B : Type*} (f : A → List A → List B) : List A → List B
  | [] => []
  | a::tail => f a tail++suffixValues f tail
theorem suffix_value {A B : Type*} (f : A → List A → Run (List B)) (L : List A) :
    (suffixQ f L).value=suffixValues (fun a tail => (f a tail).value) L := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      simp only [suffixQ,suffixValues,(append_spec _ _).1,ih]
theorem map_suffix {A B C : Type*} (g : B → C)
    (f : A → List A → List B) (L : List A) :
    (suffixValues f L).map g=suffixValues (fun a tail => (f a tail).map g) L := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [suffixValues,List.map_append,ih]
def levelTwoQ {A B : Type*} (f : A → A → Run B) (L : List A) : Run (List B) :=
  suffixQ (fun a tail => BDL26NativeStateRows.mapQ (f a) tail) L
def levelThreeQ {A B : Type*} (f : A → A → A → Run B) (L : List A) : Run (List B) :=
  suffixQ (fun a tail => levelTwoQ (f a) tail) L
def quadruplesQ {A B : Type*} (f : A → A → A → A → Run B) (L : List A) : Run (List B) :=
  suffixQ (fun a tail => levelThreeQ (f a) tail) L
def quadruples {A : Type*} (L : List A) : List (Quad A) :=
  suffixValues (fun a afterA => suffixValues (fun b afterB =>
    suffixValues (fun c afterC => afterC.map (fun d => (a,b,c,d))) afterB) afterA) L
def quadList {A : Type*} (t : Quad A) : List A := [t.1,t.2.1,t.2.2.1,t.2.2.2]
theorem quadList_injective {A : Type*} : Function.Injective (@quadList A) := by
  rintro ⟨a,b,c,d⟩ ⟨w,x,y,z⟩ h
  simpa only [quadList,List.cons.injEq,Prod.mk.injEq,and_true] using h
theorem quadruples_value {A B : Type*} (f : A → A → A → A → Run B) (L : List A) :
    (quadruplesQ f L).value=
      (quadruples L).map (fun t => (f t.1 t.2.1 t.2.2.1 t.2.2.2).value) := by
  simp only [quadruplesQ,levelThreeQ,levelTwoQ,suffix_value,
    BDL26NativeStateRows.map_value,quadruples,map_suffix,List.map_map,Function.comp_def]
def combinations {A : Type*} : ℕ → List A → List (List A)
  | 0,_ => [[]]
  | _+1,[] => []
  | k+1,a::L => (combinations k L).map (a::·)++combinations (k+1) L
theorem combinations_reverse {A : Type*} (k : ℕ) (L : List A) :
    combinations k L=(List.sublistsLen k L).reverse := by
  induction L generalizing k with
  | nil => cases k <;> simp [combinations]
  | cons a L ih =>
      cases k with
      | zero => simp [combinations]
      | succ k =>
          simp only [combinations,List.sublistsLen_succ_cons,List.reverse_append,
            List.map_reverse,ih]
theorem combinations_suffix {A : Type*} (k : ℕ) (L : List A) :
    combinations (k+1) L=
      suffixValues (fun a tail => (combinations k tail).map (a::·)) L := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [combinations,suffixValues,ih]
theorem combinations_one {A : Type*} (L : List A) :
    combinations 1 L=L.map (fun a => [a]) := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [combinations,ih]
theorem quadruples_lists {A : Type*} (L : List A) :
    (quadruples L).map quadList=(List.sublistsLen 4 L).reverse := by
  rw [←combinations_reverse]
  rw [combinations_suffix 3 L]
  simp only [combinations_suffix 2,combinations_suffix 1,
    combinations_one,quadruples,map_suffix,List.map_map,Function.comp_def,quadList]
theorem quadruples_mem {A : Type*} (L : List A) (t : Quad A) :
    t∈quadruples L ↔ List.Sublist (quadList t) L := by
  have ht : t∈quadruples L ↔ quadList t∈(quadruples L).map quadList := by
    constructor
    · intro h; exact List.mem_map.mpr ⟨t,h,rfl⟩
    · intro h
      obtain ⟨u,hu,he⟩ := List.mem_map.mp h
      exact (quadList_injective he) ▸ hu
  rw [ht,quadruples_lists,List.mem_reverse,List.mem_sublistsLen]
  simp [quadList]
def pack (a b c d : Code) : FourCodes := ⟨a,b,c,d⟩
def codeList (codes : FourCodes) : List Code :=
  [codes.first,codes.second,codes.third,codes.fourth]
def candidateQ (S : OddScale) (n : ℕ) (a b c d : Code) :
    Run (FourCodes × Option (List (Index S n))) :=
  let ca := copyCodeQ a
  let cb := copyCodeQ b
  let cc := copyCodeQ c
  let cd := copyCodeQ d
  let codes := pack ca.value cb.value cc.value cd.value
  let queried := BDL26NativeSupportMetadata.queryQ S n codes
  ⟨(codes,queried.value),ca.operations+cb.operations+cc.operations+cd.operations+
      queried.operations+5+3+8,ca.allocations+cb.allocations+cc.allocations+cd.allocations+
      queried.allocations+1+1⟩
def masterCandidatesQ (S : OddScale) (n : ℕ) :
    Run (List (FourCodes × Option (List (Index S n)))) :=
  let generated := BDL26NativePresentationGenerator.setupQ S n
  let rows := quadruplesQ (candidateQ S n) generated.1.triangles
  ⟨rows.value,generated.2+rows.operations+2,
    BDL26NativePresentationGenerator.allocatedRecords S n+rows.allocations+1⟩
abbrev actualCodes (S : OddScale) (n : ℕ) :=
  (BDL26NativePresentationGenerator.setupQ S n).1.triangles
abbrev Rows (S : OddScale) (n : ℕ) := (masterCandidatesQ S n).value
theorem master_value (S : OddScale) (n : ℕ) :
    Rows S n=(quadruples (actualCodes S n)).map (fun t =>
      (pack t.1 t.2.1 t.2.2.1 t.2.2.2,
        (BDL26NativeSupportMetadata.queryQ S n (pack t.1 t.2.1 t.2.2.1 t.2.2.2)).value)) := by
  change (quadruplesQ (candidateQ S n) (actualCodes S n)).value=_
  rw [quadruples_value]
  congr 1
noncomputable section
open scoped Classical
theorem actual_nodup (S : OddScale) (n : ℕ) : (actualCodes S n).Nodup :=
  (BDL26NativePresentationGenerator.output_label_nodup S n).2.2
theorem same_encoding (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    BDL26NativeTriangleKeys.encode S n t=BDL26NativeSupportMetadata.triangleCode S n t := rfl
def rawIndex (S : OddScale) (n : ℕ) (c : Code) (hc : c∈actualCodes S n) :
    Fin (BDL26NativeTriangleKeys.triangleCount S n) :=
  ⟨2*c.owner+c.copy,by
    obtain ⟨t,ht⟩ := (BDL26NativePresentationGenerator.triangle_labels S n c).mp hc
    subst c
    exact (BDL26NativeTriangleKeys.nativeTriangleIndex S n t).isLt⟩
def decodeCode (S : OddScale) (n : ℕ) (c : Code) (hc : c∈actualCodes S n) :
    Triangle (P S n) := (BDL26NativeTriangleKeys.nativeTriangleIndex S n).symm (rawIndex S n c hc)
theorem decode_encode (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    decodeCode S n (BDL26NativeTriangleKeys.encode S n t)
      (BDL26NativeTriangleKeys.encode_member S n t)=t := by
  change (BDL26NativeTriangleKeys.nativeTriangleIndex S n).symm
    (BDL26NativeTriangleKeys.nativeTriangleIndex S n t)=t
  exact (BDL26NativeTriangleKeys.index_inverse S n).1 t
theorem encode_decode (S : OddScale) (n : ℕ) (c : Code) (hc : c∈actualCodes S n) :
    BDL26NativeTriangleKeys.encode S n (decodeCode S n c hc)=c := by
  obtain ⟨t,ht⟩ := (BDL26NativePresentationGenerator.triangle_labels S n c).mp hc
  change BDL26NativeTriangleKeys.encode S n t=c at ht
  subst c
  rw [decode_encode]
def Rep (S : OddScale) (n : ℕ) (codes : FourCodes) (m : MasterEvent (P S n)) : Prop :=
  ∀c,c∈codeList codes ↔ ∃t∈m.val,BDL26NativeSupportMetadata.triangleCode S n t=c
theorem Rep_unique (S : OddScale) (n : ℕ) (codes : FourCodes)
    (m k : MasterEvent (P S n)) (hm : Rep S n codes m) (hk : Rep S n codes k) : m=k := by
  apply Subtype.ext
  apply Finset.ext
  intro t
  constructor
  · intro ht
    obtain ⟨u,hu,he⟩ := (hk _).mp ((hm _).mpr ⟨t,ht,rfl⟩)
    have he' : BDL26NativeTriangleKeys.encode S n u=BDL26NativeTriangleKeys.encode S n t := he
    exact (BDL26NativeTriangleKeys.encode_injective S n he') ▸ hu
  · intro ht
    obtain ⟨u,hu,he⟩ := (hm _).mp ((hk _).mpr ⟨t,ht,rfl⟩)
    have he' : BDL26NativeTriangleKeys.encode S n u=BDL26NativeTriangleKeys.encode S n t := he
    exact (BDL26NativeTriangleKeys.encode_injective S n he') ▸ hu
theorem sublist_filter_identity {A : Type*} (L xs : List A)
    (hd : L.Nodup) (hs : List.Sublist xs L) :
    L.filter (fun a => decide (a∈xs))=xs := by
  have hx : xs.filter (fun a => decide (a∈xs))=xs :=
    List.filter_eq_self.mpr (by intro a ha; simp [ha])
  have hsub := hs.filter (fun a => decide (a∈xs))
  rw [hx] at hsub
  have he : (L.filter (fun a => decide (a∈xs))).toFinset=xs.toFinset := by
    ext a
    simp only [List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right,fun ha => ⟨hs.subset ha,ha⟩⟩
  have hl : (L.filter (fun a => decide (a∈xs))).length=xs.length := by
    rw [←List.toFinset_card_of_nodup (hd.filter _),
      ←List.toFinset_card_of_nodup (hd.sublist hs),he]
  exact (hsub.eq_of_length hl.symm).symm
theorem sublists_same_set {A : Type*} (L xs ys : List A) (hd : L.Nodup)
    (hx : List.Sublist xs L) (hy : List.Sublist ys L) (he : xs.toFinset=ys.toFinset) : xs=ys := by
  have hp : (fun a => decide (a∈xs))=(fun a => decide (a∈ys)) := by
    funext a
    have hh : a∈xs ↔ a∈ys := by
      simpa only [List.mem_toFinset] using Finset.ext_iff.mp he a
    by_cases hx : a∈xs
    · have hy := hh.mp hx
      simp [hx,hy]
    · have hy : a∉ys := fun hy => hx (hh.mpr hy)
      simp [hx,hy]
  calc
    xs=L.filter (fun a => decide (a∈xs)) := (sublist_filter_identity L xs hd hx).symm
    _=L.filter (fun a => decide (a∈ys)) := congrArg (List.filter · L) hp
    _=ys := sublist_filter_identity L ys hd hy
theorem rep_codes_set (S : OddScale) (n : ℕ) (codes : FourCodes)
    (m : MasterEvent (P S n)) :
    Rep S n codes m ↔ (codeList codes).toFinset=m.val.image (BDL26NativeTriangleKeys.encode S n) := by
  simp only [Rep,Finset.ext_iff,List.mem_toFinset,Finset.mem_image,same_encoding]
def originalSet (S : OddScale) (n : ℕ) (codes : FourCodes) : Finset (Triangle (P S n)) :=
  Finset.univ.filter (fun t => BDL26NativeTriangleKeys.encode S n t∈codeList codes)
theorem originalSet_image (S : OddScale) (n : ℕ) (codes : FourCodes)
    (hc : ∀c∈codeList codes,c∈actualCodes S n) :
    (originalSet S n codes).image (BDL26NativeTriangleKeys.encode S n)=(codeList codes).toFinset := by
  ext c
  simp only [Finset.mem_image,originalSet,Finset.mem_filter,Finset.mem_univ,true_and,List.mem_toFinset]
  constructor
  · rintro ⟨t,ht,rfl⟩; exact ht
  · intro h
    refine ⟨decodeCode S n c (hc c h),?_,encode_decode S n c (hc c h)⟩
    rw [encode_decode]; exact h
theorem tuple_master (S : OddScale) (n : ℕ) (t : Quad Code)
    (ht : t∈quadruples (actualCodes S n)) :
    ∃m : MasterEvent (P S n),Rep S n (pack t.1 t.2.1 t.2.2.1 t.2.2.2) m := by
  have hs : List.Sublist (quadList t) (actualCodes S n) := (quadruples_mem _ _).mp ht
  have hn : (quadList t).Nodup := (actual_nodup S n).sublist hs
  let codes := pack t.1 t.2.1 t.2.2.1 t.2.2.2
  have hh : ∀c∈codeList codes,c∈actualCodes S n := by
    intro c hc
    exact hs.subset hc
  have him := originalSet_image S n codes hh
  have hcard : (originalSet S n codes).card=4 := by
    calc
      (originalSet S n codes).card=
        ((originalSet S n codes).image (BDL26NativeTriangleKeys.encode S n)).card :=
          (Finset.card_image_of_injective _ (BDL26NativeTriangleKeys.encode_injective S n)).symm
      _=(codeList codes).toFinset.card := congrArg Finset.card him
      _=4 := by
        have hcodes : (codeList codes).Nodup := by
          change (quadList t).Nodup
          exact hn
        exact List.toFinset_card_of_nodup hcodes
  exact ⟨⟨originalSet S n codes,hcard⟩,(rep_codes_set _ _ _ _).mpr him.symm⟩
theorem tuple_unique_for_master (S : OddScale) (n : ℕ) (t u : Quad Code)
    (ht : t∈quadruples (actualCodes S n)) (hu : u∈quadruples (actualCodes S n))
    (m : MasterEvent (P S n))
    (hr : Rep S n (pack t.1 t.2.1 t.2.2.1 t.2.2.2) m)
    (hs : Rep S n (pack u.1 u.2.1 u.2.2.1 u.2.2.2) m) : t=u := by
  have he : (quadList t).toFinset=(quadList u).toFinset :=
    ((rep_codes_set _ _ _ _).mp hr).trans ((rep_codes_set _ _ _ _).mp hs).symm
  apply quadList_injective
  apply sublists_same_set (actualCodes S n) _ _ (actual_nodup S n)
    ((quadruples_mem _ _).mp ht) ((quadruples_mem _ _).mp hu)
  ext c
  simpa only [List.mem_toFinset] using Finset.ext_iff.mp he c
theorem master_tuple (S : OddScale) (n : ℕ) (m : MasterEvent (P S n)) :
    ∃t∈quadruples (actualCodes S n),Rep S n (pack t.1 t.2.1 t.2.2.1 t.2.2.2) m := by
  let target := m.val.image (BDL26NativeTriangleKeys.encode S n)
  let xs := (actualCodes S n).filter (fun c => decide (c∈target))
  have he : xs.toFinset=target := by
    ext c
    simp only [xs,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    constructor
    · exact And.right
    · intro hc
      obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hc
      exact ⟨BDL26NativeTriangleKeys.encode_member S n t,hc⟩
  have hl : xs.length=4 := by
    rw [←List.toFinset_card_of_nodup ((actual_nodup S n).filter _),he]
    exact (Finset.card_image_of_injective _ (BDL26NativeTriangleKeys.encode_injective S n)).trans m.property
  have hm : xs∈(quadruples (actualCodes S n)).map quadList := by
    rw [quadruples_lists,List.mem_reverse,List.mem_sublistsLen]
    exact ⟨List.filter_sublist,hl⟩
  obtain ⟨t,ht,hx⟩ := List.mem_map.mp hm
  refine ⟨t,ht,(rep_codes_set _ _ _ _).mpr ?_⟩
  exact (congrArg List.toFinset hx).trans he
theorem row_tuple (S : OddScale) (n : ℕ)
    (row : FourCodes × Option (List (Index S n))) (h : row∈Rows S n) :
    ∃t∈quadruples (actualCodes S n),row=
      (pack t.1 t.2.1 t.2.2.1 t.2.2.2,
        (BDL26NativeSupportMetadata.queryQ S n (pack t.1 t.2.1 t.2.2.1 t.2.2.2)).value) := by
  rw [master_value] at h
  obtain ⟨t,ht,he⟩ := List.mem_map.mp h
  exact ⟨t,ht,he.symm⟩
theorem master_complete_unique (S : OddScale) (n : ℕ) (m : MasterEvent (P S n)) :
    ∃!row : FourCodes × Option (List (Index S n)),row∈Rows S n ∧ Rep S n row.1 m := by
  obtain ⟨t,ht,hr⟩ := master_tuple S n m
  let row := (pack t.1 t.2.1 t.2.2.1 t.2.2.2,
    (BDL26NativeSupportMetadata.queryQ S n (pack t.1 t.2.1 t.2.2.1 t.2.2.2)).value)
  refine ⟨row,⟨?_,hr⟩,?_⟩
  · rw [master_value]
    exact List.mem_map.mpr ⟨t,ht,rfl⟩
  · intro other ho
    obtain ⟨u,hu,rfl⟩ := row_tuple S n other ho.1
    have he := tuple_unique_for_master S n u t hu ht m ho.2 hr
    subst u
    rfl
theorem query_four_actual (S : OddScale) (n : ℕ) (a b c d : Triangle (P S n)) :
    ∃U,(BDL26NativeSupportMetadata.queryQ S n
      (pack (BDL26NativeSupportMetadata.triangleCode S n a)
        (BDL26NativeSupportMetadata.triangleCode S n b)
        (BDL26NativeSupportMetadata.triangleCode S n c)
        (BDL26NativeSupportMetadata.triangleCode S n d))).value=some U ∧
      U.Nodup ∧ U.length≤12 ∧ ∀i,i∈U ↔
        BDL26NativeStateRows.decode S n i∈triangleSupport (P S n) a ∨
        BDL26NativeStateRows.decode S n i∈triangleSupport (P S n) b ∨
        BDL26NativeStateRows.decode S n i∈triangleSupport (P S n) c ∨
        BDL26NativeStateRows.decode S n i∈triangleSupport (P S n) d := by
  let raw := BDL26NativeSupportMetadata.twelve
    (BDL26NativeSupportMetadata.corners S n a) (BDL26NativeSupportMetadata.corners S n b)
    (BDL26NativeSupportMetadata.corners S n c) (BDL26NativeSupportMetadata.corners S n d)
  refine ⟨(BDL26NativeSupportMetadata.dedupQ raw).value,?_,
    BDL26NativeSupportMetadata.dedup_nodup _,?_,?_⟩
  · simp [BDL26NativeSupportMetadata.queryQ,pack,BDL26NativeSupportMetadata.atlas_actual,raw]
  · simpa [raw,BDL26NativeSupportMetadata.twelve] using BDL26NativeSupportMetadata.dedup_length raw
  · intro i
    rw [BDL26NativeSupportMetadata.dedup_membership]
    have hm (x y z w : BDL26NativeSupportMetadata.Triple (Index S n)) :
        i∈BDL26NativeSupportMetadata.twelve x y z w ↔
        i∈BDL26NativeSupportMetadata.tripleList x ∨ i∈BDL26NativeSupportMetadata.tripleList y ∨
        i∈BDL26NativeSupportMetadata.tripleList z ∨ i∈BDL26NativeSupportMetadata.tripleList w := by
      simp [BDL26NativeSupportMetadata.twelve,BDL26NativeSupportMetadata.tripleList,or_assoc]
    rw [hm]
    simp only [BDL26NativeSupportMetadata.corners_membership]
theorem master_sound_support (S : OddScale) (n : ℕ)
    (row : FourCodes × Option (List (Index S n))) (hrow : row∈Rows S n) :
    ∃m : MasterEvent (P S n),∃U,row.2=some U ∧ Rep S n row.1 m ∧
      (codeList row.1).Nodup ∧ U.Nodup ∧ U.length≤12 ∧
      ∀i,i∈U ↔ BDL26NativeStateRows.decode S n i∈masterSupport (P S n) m := by
  obtain ⟨t,ht,rfl⟩ := row_tuple S n row hrow
  obtain ⟨m,hm⟩ := tuple_master S n t ht
  have hs : List.Sublist (quadList t) (actualCodes S n) := (quadruples_mem _ _).mp ht
  have hn : (quadList t).Nodup := (actual_nodup S n).sublist hs
  have ha : ∃a∈m.val,BDL26NativeSupportMetadata.triangleCode S n a=t.1 :=
    (hm _).mp (by simp [codeList,pack])
  have hb : ∃b∈m.val,BDL26NativeSupportMetadata.triangleCode S n b=t.2.1 :=
    (hm _).mp (by simp [codeList,pack])
  have hc : ∃c∈m.val,BDL26NativeSupportMetadata.triangleCode S n c=t.2.2.1 :=
    (hm _).mp (by simp [codeList,pack])
  have hd : ∃d∈m.val,BDL26NativeSupportMetadata.triangleCode S n d=t.2.2.2 :=
    (hm _).mp (by simp [codeList,pack])
  obtain ⟨a,ham,ha⟩ := ha
  obtain ⟨b,hbm,hb⟩ := hb
  obtain ⟨c,hcm,hc⟩ := hc
  obtain ⟨d,hdm,hd⟩ := hd
  obtain ⟨U,hU,hUn,hUl,hUm⟩ := query_four_actual S n a b c d
  rw [ha,hb,hc,hd] at hU
  refine ⟨m,U,hU,hm,hn,hUn,hUl,?_⟩
  intro i
  rw [hUm]
  simp only [masterSupport,Finset.mem_biUnion]
  constructor
  · rintro (h|h|h|h)
    · exact ⟨a,ham,h⟩
    · exact ⟨b,hbm,h⟩
    · exact ⟨c,hcm,h⟩
    · exact ⟨d,hdm,h⟩
  · rintro ⟨v,hvm,hv⟩
    have hvcode := (hm _).mpr ⟨v,hvm,rfl⟩
    simp only [codeList,pack,List.mem_cons,List.not_mem_nil,or_false] at hvcode
    rcases hvcode with he|he|he|he
    · have he' := BDL26NativeTriangleKeys.encode_injective S n (he.trans ha.symm)
      exact Or.inl (he' ▸ hv)
    · have he' := BDL26NativeTriangleKeys.encode_injective S n (he.trans hb.symm)
      exact Or.inr (Or.inl (he' ▸ hv))
    · have he' := BDL26NativeTriangleKeys.encode_injective S n (he.trans hc.symm)
      exact Or.inr (Or.inr (Or.inl (he' ▸ hv)))
    · have he' := BDL26NativeTriangleKeys.encode_injective S n (he.trans hd.symm)
      exact Or.inr (Or.inr (Or.inr (he' ▸ hv)))
def decodeRow (S : OddScale) (n : ℕ) (row : {row // row∈Rows S n}) : MasterEvent (P S n) :=
  Classical.choose (master_sound_support S n row.val row.property)
theorem decodeRow_rep (S : OddScale) (n : ℕ) (row : {row // row∈Rows S n}) :
    Rep S n row.val.1 (decodeRow S n row) := by
  have h := Classical.choose_spec (master_sound_support S n row.val row.property)
  exact (Classical.choose_spec h).2.1
def masterEquiv (S : OddScale) (n : ℕ) : {row // row∈Rows S n} ≃ MasterEvent (P S n) :=
  Equiv.ofBijective (decodeRow S n) (by
    constructor
    · intro a b he
      apply Subtype.ext
      have ha := decodeRow_rep S n a
      have hb := decodeRow_rep S n b
      rw [←he] at hb
      obtain ⟨row,hr,hu⟩ := master_complete_unique S n (decodeRow S n a)
      exact (hu a.val ⟨a.property,ha⟩).trans (hu b.val ⟨b.property,hb⟩).symm
    · intro m
      obtain ⟨row,hr,_⟩ := master_complete_unique S n m
      refine ⟨⟨row,hr.1⟩,?_⟩
      exact Rep_unique S n row.1 _ _ (decodeRow_rep S n ⟨row,hr.1⟩) hr.2)
def decodedMasters (S : OddScale) (n : ℕ) : List (MasterEvent (P S n)) :=
  (Rows S n).attach.map (decodeRow S n)
def originalEventSet (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space) (r : ℝ) :
    Finset (Event (P S n) J r) :=
  (((decodedMasters S n).toFinset.filter (fun m => Eligible (P S n) J r m.val)).attach).image
    (fun m => (⟨m.val.val,by
      have hm := m.property
      simp only [Finset.mem_filter] at hm
      exact hm.2⟩ : Event (P S n) J r))
def originalOrderedEvents (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space) (r : ℝ) :
    List (Event (P S n) J r) :=
  (originalEventSet S n J r).sort (eventPriorityLE (P S n) J r)
end
end QEC.Coding.BDL26NativeMasterCandidates


