-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T03:13:04.112386+00:00
-- url     : https://prove2.me/theorems/7742e17f-ac7e-4b0c-a147-e2adad65d0c7
-- title:
--   Incoming Rows Execution
-- statement:
--   Definitions and structural lemmas for Incoming Rows Execution, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_coupling_x
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_coupling_y
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_coupling_z
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_check_hermitian
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_mem_x_checkSupport
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_mem_z_checkSupport
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_levelMap_zero
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
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalWordPush_single
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzFace_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzQ_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzX_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzZ_card
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_map2Coord_canonicalBasis
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary0_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary1_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_centerExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_dedupQuery_value
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_stateRowQuery_cost_le
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_stateRowQuery_value
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangleLabelEqQuery_correct
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_vertexExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_vertexInputList_complete
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_vertexInputList_length
import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seedPoint_eq_zero
import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_physical_zero
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
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
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
import Theorems.Thm_QEC_Semantics_CompletelyPositive_sum
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum
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
noncomputable section
namespace QEC.Coding.BDL26IncomingRowsExecution
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
attribute [local instance] BDL26RandomPerturbation.countedLabelListMeasurable
  BDL26RandomPerturbation.countedLabelListSingleton
def incomingRows (P : TannerSquarePresentation) (J : Vertex P → Space) : StateRows P :=
  (vertexInputList P).map (fun v => (v,0,J v))
@[simp] theorem incomingRows_labels (P : TannerSquarePresentation) (J : Vertex P → Space) :
    (incomingRows P J).map Prod.fst = vertexInputList P := by
  simp [incomingRows,List.map_map,Function.comp_def]
@[simp] theorem incomingRows_length (P : TannerSquarePresentation) (J : Vertex P → Space) :
    (incomingRows P J).length = Fintype.card (Vertex P) := by
  simp only [incomingRows,List.length_map,vertexInputList_length]
@[simp] theorem incomingRows_points (P : TannerSquarePresentation) (J : Vertex P → Space) :
    statePoints (incomingRows P J) = J := by
  funext v
  have hm : ∃ row ∈ incomingRows P J, row.1=v :=
    ⟨(v,0,J v),List.mem_map.mpr ⟨v,vertexInputList_complete P v,rfl⟩,rfl⟩
  have hv := stateRowQuery_value v (incomingRows P J) (0,J v) (by
    intro row hr he
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hr
    change u = v at he
    subst v
    rfl) hm
  exact congrArg Prod.snd hv
def incomingRead (P : TannerSquarePresentation) (I : StateRows P) (v : Vertex P) : Space × ℕ :=
  let q := stateRowQuery v I
  (q.1.2,q.2)
@[simp] theorem incomingRead_value (P : TannerSquarePresentation) (I : StateRows P)
    (v : Vertex P) : (incomingRead P I v).1 = statePoints I v := rfl
theorem incomingRead_cost_le (P : TannerSquarePresentation) (I : StateRows P)
    (v : Vertex P) : (incomingRead P I v).2 ≤ 2*I.length := stateRowQuery_cost_le v I
@[simp] theorem incomingRead_empty (P : TannerSquarePresentation) (v : Vertex P) :
    incomingRead P [] v = (0,0) := rfl
@[simp] theorem incomingRead_head (P : TannerSquarePresentation) (v : Vertex P)
    (c : ℕ) (x : Space) (I : StateRows P) : incomingRead P ((v,c,x)::I) v = (x,2) := by
  simp [incomingRead,stateRowQuery]
def accessMultiplier {P : TannerSquarePresentation} (I : StateRows P) : ℕ := 6*I.length+1
theorem accessMultiplier_pos {P : TannerSquarePresentation} (I : StateRows P) :
    1 ≤ accessMultiplier I := by simp only [accessMultiplier]; omega
theorem self_le_scale (d n : ℕ) (hd : 1 ≤ d) : n ≤ d*n := by
  have h := Nat.mul_le_mul_right n hd
  simpa only [Nat.one_mul] using h
theorem extra_le_scale (m c e : ℕ) (hc : 1 ≤ c) (he : e ≤ 6*m) :
    c+e ≤ (6*m+1)*c := by
  have h := Nat.mul_le_mul_left (6*m) hc
  nlinarith
def Sim {A : Type*} (d : ℕ) (x y : A × ℕ) : Prop :=
  x.1=y.1 ∧ x.2 ≤ d*y.2
theorem all_sim {A : Type*} (d : ℕ) (hd : 1 ≤ d)
    (q q' : A → Bool × ℕ) (h : ∀ a, Sim d (q' a) (q a)) (L : List A) :
    Sim d (listAllQuery q' L) (listAllQuery q L) := by
  induction L with
  | nil => exact ⟨rfl,by simp [listAllQuery]⟩
  | cons a L ih =>
      have ha := h a
      constructor
      · simp only [listAllQuery,ha.1,ih.1]
      · dsimp only [listAllQuery]
        nlinarith [ha.2,ih.2]
def rowAnchorCloseQuery (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (a b : Triangle P) : Bool × ℕ :=
  let x := incomingRead P I (.x (P.faceX a.1))
  let y := incomingRead P I (.x (P.faceX b.1))
  let q := anchorCloseProgram.run (fun _ => y.1) x.1 r
  (q.1,q.2+x.2+y.2)
theorem rowAnchorCloseQuery_value (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (a b : Triangle P) :
    (rowAnchorCloseQuery P I r a b).1=(anchorCloseQuery P (statePoints I) r a b).1 := rfl
theorem rowAnchorCloseQuery_cost (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (a b : Triangle P) :
    (rowAnchorCloseQuery P I r a b).2=(anchorCloseQuery P (statePoints I) r a b).2+
      (incomingRead P I (.x (P.faceX a.1))).2+(incomingRead P I (.x (P.faceX b.1))).2 := rfl
theorem rowAnchorCloseQuery_cost_le (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (a b : Triangle P) : (rowAnchorCloseQuery P I r a b).2 ≤
      accessMultiplier I*(anchorCloseQuery P (statePoints I) r a b).2 := by
  have hx := incomingRead_cost_le P I (.x (P.faceX a.1))
  have hy := incomingRead_cost_le P I (.x (P.faceX b.1))
  have hp : 1 ≤ (anchorCloseQuery P (statePoints I) r a b).2 := by
    dsimp only [anchorCloseQuery,anchorCloseProgram,RealTest.run]
    omega
  rw [rowAnchorCloseQuery_cost]
  have h := extra_le_scale I.length _
    ((incomingRead P I (.x (P.faceX a.1))).2+(incomingRead P I (.x (P.faceX b.1))).2)
    hp (by omega)
  simpa only [accessMultiplier,Nat.add_assoc] using h
def rowEligiblePairQuery (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (a b : Triangle P) : Bool × ℕ :=
  let color := colorMatchQuery P a b
  let close := rowAnchorCloseQuery P I r a b
  (color.1 && close.1,color.2+close.2+1)
theorem pair_sim (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (a b : Triangle P) : Sim (accessMultiplier I)
    (rowEligiblePairQuery P I r a b) (eligiblePairQuery P (statePoints I) r a b) := by
  have hc := rowAnchorCloseQuery_cost_le P I r a b
  have hs := self_le_scale (accessMultiplier I) (colorMatchQuery P a b).2 (accessMultiplier_pos I)
  have hd := accessMultiplier_pos I
  constructor
  · exact congrArg (fun flag => (colorMatchQuery P a b).1 && flag)
      (rowAnchorCloseQuery_value P I r a b)
  · dsimp only [rowEligiblePairQuery,eligiblePairQuery]
    nlinarith
def rowEligibleListQuery (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (L : List (Triangle P)) : (Finset (Triangle P) × Bool) × ℕ := by
  let unique := dedupQuery (triangleLabelEqQuery P) L
  let s : Finset (Triangle P) := ⟨↑unique.1,by
    rw [dedupQuery_value _ (triangleLabelEqQuery_correct P)]
    exact List.nodup_dedup L⟩
  let pairs := listAllQuery (fun a => listAllQuery (rowEligiblePairQuery P I r a) unique.1) unique.1
  exact ((s,decide (unique.1.length=4) && pairs.1),unique.2+pairs.2+unique.1.length+2)
theorem eligible_sim (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (L : List (Triangle P)) : Sim (accessMultiplier I)
    (rowEligibleListQuery P I r L) (eligibleListQuery P (statePoints I) r L) := by
  let U := (dedupQuery (triangleLabelEqQuery P) L).1
  have hp := all_sim (accessMultiplier I) (accessMultiplier_pos I) _ _
    (fun a => all_sim (accessMultiplier I) (accessMultiplier_pos I) _ _ (pair_sim P I r a) U) U
  have hs := self_le_scale (accessMultiplier I)
    ((dedupQuery (triangleLabelEqQuery P) L).2+U.length+2) (accessMultiplier_pos I)
  constructor
  · dsimp only [rowEligibleListQuery,eligibleListQuery]
    rw [hp.1]
  · dsimp only [rowEligibleListQuery,eligibleListQuery]
    dsimp only [U] at hp hs
    nlinarith [hp.2]
theorem rowEligibleListQuery_value (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (L : List (Triangle P)) :
    (rowEligibleListQuery P I r L).1=(eligibleListQuery P (statePoints I) r L).1 :=
  (eligible_sim P I r L).1
def rowCandidateQuery (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) (L : List (Triangle P)) : Option (Event P (statePoints I) r) × ℕ :=
  let q := rowEligibleListQuery P I r L
  if h : q.1.2=true then
    (some ⟨q.1.1,by
      rw [rowEligibleListQuery_value]
      exact (eligibleListQuery_correct P (statePoints I) hr L).mp
        (by simpa only [q,rowEligibleListQuery_value] using h)⟩,q.2+1)
  else (none,q.2+1)
def rowRawUniverseQuery (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) : List (Event P (statePoints I) r) × ℕ :=
  let tuples := fourTuplesQuery (triangleInputList P)
  let events := filterMapQuery (rowCandidateQuery P I hr) tuples.1
  (events.1,tuples.2+events.2)
def rowUniverseQuery (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) : List (Event P (statePoints I) r) × ℕ :=
  let raw := rowRawUniverseQuery P I hr
  let unique := dedupQuery (eventEqQuery P (statePoints I) r) raw.1
  let sorted := sortQuery (eventCompareQuery P (statePoints I) r) unique.1
  (sorted.1,raw.2+unique.2+sorted.2)
def rowCenterQuery (P : TannerSquarePresentation) (I : StateRows P) (lambda : ℝ)
    (K : ℕ) (a : Option (Triangle P)) (g : Grid K) : Space × ℕ :=
  match a with
  | none => (0,1)
  | some t => let old := incomingRead P I (.x (P.faceX t.1))
              let grid := gridPointQuery K g
              let point := pointSnapshotQuery lambda old.1 grid.1
              (point.1,grid.2+point.2+2+old.2)
def centerExtra (P : TannerSquarePresentation) (I : StateRows P) : Option (Triangle P) → ℕ
  | none => 0
  | some t => (incomingRead P I (.x (P.faceX t.1))).2
def triangleExtra (P : TannerSquarePresentation) (I : StateRows P) (t : Triangle P) : ℕ :=
  (incomingRead P I (triangleVertex P t 0)).2+
  (incomingRead P I (triangleVertex P t 1)).2+
  (incomingRead P I (triangleVertex P t 2)).2
def rowTrianglePointsQuery (P : TannerSquarePresentation) (I : StateRows P)
    (lambda : ℝ) (t : Triangle P) (R : StateRows P) : (Fin 3 → Space) × ℕ :=
  let o0 := incomingRead P I (triangleVertex P t 0)
  let o1 := incomingRead P I (triangleVertex P t 1)
  let o2 := incomingRead P I (triangleVertex P t 2)
  let r0 := stateRowQuery (triangleVertex P t 0) R
  let r1 := stateRowQuery (triangleVertex P t 1) R
  let r2 := stateRowQuery (triangleVertex P t 2) R
  let q0 := pointSnapshotQuery lambda o0.1 r0.1.2
  let q1 := pointSnapshotQuery lambda o1.1 r1.1.2
  let q2 := pointSnapshotQuery lambda o2.1 r2.1.2
  (![q0.1,q1.1,q2.1],r0.2+r1.2+r2.2+q0.2+q1.2+q2.2+18+o0.2+o1.2+o2.2)
def rowTriangleQuery (P : TannerSquarePresentation) (I : StateRows P)
    (lambda : ℝ) (t : Triangle P) (R : StateRows P) (z : Space) : Bool × ℕ :=
  let points := rowTrianglePointsQuery P I lambda t R
  let query := triangleQuery points.1 z 2
  (query.1,points.2+query.2)
def rowStateEventQuery (P : TannerSquarePresentation) (I : StateRows P)
    (r lambda : ℝ) (K : ℕ) (e : Event P (statePoints I) r) (R : StateRows P) : Bool × ℕ :=
  let net := gridListQuery K
  let anchor := eventAnchorQuery P (statePoints I) r e
  let query := listAnyQuery (fun g : Grid K =>
    let center := rowCenterQuery P I lambda K anchor.1 g
    let triangles := listAllQuery (fun a : e.val =>
      rowTriangleQuery P I lambda a.val R center.1) (Finset.univ.toList : List e.val)
    (triangles.1,center.2+triangles.2+8)) net.1
  (query.1,net.2+anchor.2+query.2+1)
def rowScanQuery (P : TannerSquarePresentation) (I : StateRows P)
    (r lambda : ℝ) (K : ℕ) (events : List (Event P (statePoints I) r))
    (R : StateRows P) : Option (Event P (statePoints I) r) × ℕ :=
  scanQuery (rowStateEventQuery P I r lambda K) events R
def rowStepQuery (P : TannerSquarePresentation) (I : StateRows P)
    (r lambda : ℝ) (K : ℕ) (events : List (Event P (statePoints I) r))
    (T : Table (X := fun _ : Vertex P => Space)) (R : StateRows P) : StateRows P × ℕ :=
  let scan := rowScanQuery P I r lambda K events R
  match scan.1 with
  | none => (R,scan.2)
  | some e => let update := refreshStateRowsQuery P (statePoints I) r e T R
              (update.1,scan.2+update.2)
def rowPrefixQuery (P : TannerSquarePresentation) (I : StateRows P)
    (r lambda : ℝ) (K : ℕ) (events : List (Event P (statePoints I) r))
    (T : Table (X := fun _ : Vertex P => Space)) : ℕ → StateRows P × ℕ
  | 0 => initialRowsQuery P T
  | s+1 => let prior := rowPrefixQuery P I r lambda K events T s
           let next := rowStepQuery P I r lambda K events T prior.1
           (next.1,prior.2+next.2)
def rowOutputQuery (P : TannerSquarePresentation) (I : StateRows P)
    (lambda : ℝ) (R : StateRows P) : List (Vertex P × Space) × ℕ :=
  mapQuery (fun row => let old := incomingRead P I row.1
                      let q := pointSnapshotQuery lambda old.1 row.2.2
                      ((row.1,q.1),q.2+3+old.2)) R
def rowExecutionQuery (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : Table (X := fun _ : Vertex P => Space)) : List (Vertex P × Space) × ℝ≥0∞ :=
  let eventsRun := rowUniverseQuery P I hr
  let prior := rowPrefixQuery P I r lambda K eventsRun.1 T
    (haltTime (eventSupport P (statePoints I) r) (eventBad P (statePoints I) r lambda K) T)
  let final := rowScanQuery P I r lambda K eventsRun.1 prior.1
  let out := rowOutputQuery P I lambda prior.1
  (out.1,if Halts (eventSupport P (statePoints I) r) (eventBad P (statePoints I) r lambda K) T
    then ((eventsRun.2+prior.2+final.2+out.2 : ℕ) : ℝ≥0∞) else ∞)
def rowExecutionCost (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : Table (X := fun _ : Vertex P => Space)) : ℝ≥0∞ :=
  (rowExecutionQuery P I hr lambda K T).2
def pairExtra (P : TannerSquarePresentation) (I : StateRows P) (a b : Triangle P) : ℕ :=
  (incomingRead P I (.x (P.faceX a.1))).2+(incomingRead P I (.x (P.faceX b.1))).2
def eligibilityExtra (P : TannerSquarePresentation) (I : StateRows P) (L : List (Triangle P)) : ℕ :=
  let U := (dedupQuery (triangleLabelEqQuery P) L).1
  (U.map (fun a => (U.map (pairExtra P I a)).sum)).sum
def universeExtra (P : TannerSquarePresentation) (I : StateRows P) : ℕ :=
  ((fourTuplesQuery (triangleInputList P)).1.map (eligibilityExtra P I)).sum
def rowMasterCandidateQuery (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (L : List (Triangle P)) : Option (MasterEvent P) × ℕ :=
  let q := rowEligibleListQuery P I r L
  if hc : L.toFinset.card=4 then
    (if q.1.2 then some ⟨L.toFinset,hc⟩ else none,q.2+1)
  else (none,q.2+1)
def rowMasterUniverseQuery (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) : List (MasterEvent P) × ℕ :=
  let tuples := fourTuplesQuery (triangleInputList P)
  let events := filterMapQuery (rowMasterCandidateQuery P I r) tuples.1
  let raw := (events.1,tuples.2+events.2)
  let unique := dedupQuery (countedMasterEqQuery P) raw.1
  let sorted := sortQuery (countedMasterCompareQuery P) unique.1
  (sorted.1,raw.2+unique.2+sorted.2)
def eventExtra (P : TannerSquarePresentation) (I : StateRows P) (K : ℕ) (e : MasterEvent P) : ℕ :=
  ((gridListQuery K).1.map (fun _ => centerExtra P I (countedMasterAnchorQuery P e).1+
    ((Finset.univ.toList : List e.val).map (fun a => triangleExtra P I a.val)).sum)).sum
def rowMasterStateEventQuery (P : TannerSquarePresentation) (I : StateRows P)
    (lambda : ℝ) (K : ℕ) (e : MasterEvent P) (R : StateRows P) : Bool × ℕ :=
  let net := gridListQuery K
  let anchor := countedMasterAnchorQuery P e
  let query := listAnyQuery (fun g : Grid K =>
    let center := rowCenterQuery P I lambda K anchor.1 g
    let triangles := listAllQuery (fun a : e.val =>
      rowTriangleQuery P I lambda a.val R center.1) (Finset.univ.toList : List e.val)
    (triangles.1,center.2+triangles.2+8)) net.1
  (query.1,net.2+anchor.2+query.2+1)
def outputExtra (P : TannerSquarePresentation) (I : StateRows P) : ℕ :=
  ((vertexInputList P).map (fun v => (incomingRead P I v).2)).sum
def rowPerturbationOutput {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : StageTables p n) : StageMaps p n :=
  statePoints ((rowExecutionQuery (StagePresentation p n) (incomingRows (StagePresentation p n) J)
    (by positivity : (0 : ℝ) ≤ anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda) T).1.map
      (fun row => (row.1,0,row.2)))
def rowPhysicalSuccessor {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : StageTables p n) : StageMaps p (n+1) :=
  replacementOutput (perturbationOddScale p) n (state (perturbationOddScale p) n)
    (rowPerturbationOutput p n J T)
def rowEvaluate {L : ℝ} (p : GeometricParameters L) : (N : ℕ) → Experiment p N → StageMaps p N
  | 0, _ => BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p)
  | N+1, z => rowPhysicalSuccessor p N (rowEvaluate p N z.1) z.2
def rowHistory {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N)
    (i : Fin (N+1)) : StageMaps p i.val :=
  rowEvaluate p i.val (experimentPrefix p i.val N (by omega) z)
def jointRowStageCost {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (w : StageMaps p n × StageTables p n) : ℝ≥0∞ :=
  rowExecutionCost (StagePresentation p n) (incomingRows (StagePresentation p n) w.1)
    (by positivity : (0 : ℝ) ≤ anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda) w.2
def rowStageCost {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : ℝ≥0∞ := jointRowStageCost p i.val (stagePair p N i z)
def rowTotalCost {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N) : ℝ≥0∞ :=
  ∑ i : Fin N, rowStageCost p N i z
end QEC.Coding.BDL26IncomingRowsExecution


