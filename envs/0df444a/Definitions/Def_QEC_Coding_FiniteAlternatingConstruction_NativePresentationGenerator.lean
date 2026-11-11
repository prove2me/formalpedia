-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
-- name    : QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T23:35:55.391616+00:00
-- url     : https://prove2.me/theorems/340ce1fb-44ea-4e6d-a5ae-8ccb9985bec0
-- title:
--   Native Presentation Generator
-- statement:
--   Definitions and structural lemmas for Native Presentation Generator, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_InputSize
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_coupling_x
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_coupling_y
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_coupling_z
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_check_hermitian
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_mem_x_checkSupport
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_mem_z_checkSupport
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_correctionRegion_mem
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_syndromeRegion_mem
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
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
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_vertexExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seedPoint_eq_zero
import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_physical_zero
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_BoundaryUnit_swap
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_TriangleWidthAtLeast_swap
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_foldedSquare_bottom
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_foldedSquare_diagonal
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_foldedSquare_left
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_foldedSquare_right
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_foldedSquare_top
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_lower_last_normalized
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rawFineInteger_interior
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rawFineInteger_last
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rzFaceQ_transpose
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rzFaceX_transpose
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rzFaceZ_transpose
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
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_qToZDoubleCylinderEdge_end
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_qToZDoubleCylinderEdge_start
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
import Theorems.Thm_QEC_Semantics_CompletelyPositive_add
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
import Theorems.Thm_QEC_Semantics_JumpProtected_add
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_add
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
attribute [local simp] QEC.Coding.BDL26DecodingGraph.correctionRegion_mem
attribute [local simp] QEC.Coding.BDL26DecodingGraph.syndromeRegion_mem
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.alternatingCarrier_zero
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_target_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_target_val
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
namespace QEC.Coding.BDL26NativePresentationGenerator
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement hiding Two
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26RandomPerturbation
abbrev Query (A : Type*) := A × ℕ
def mapQ {A B : Type*} (f : A → Query B) : List A → Query (List B)
  | [] => ([],0)
  | a::as =>
      let x := f a
      let xs := mapQ f as
      (x.1::xs.1,x.2+xs.2+1)
def filterQ {A : Type*} (p : A → Query Bool) : List A → Query (List A)
  | [] => ([],0)
  | a::as =>
      let h := p a
      let xs := filterQ p as
      (if h.1 then a::xs.1 else xs.1,h.2+xs.2+1)
def rangeQ : ℕ → Query (List ℕ)
  | 0 => ([],1)
  | n+1 =>
      let r := rangeQ n
      (r.1++[n],r.2+2*r.1.length+4)
def appendQ {A : Type*} (a b : List A) : Query (List A) := (a++b,a.length+1)
def flattenQ {A : Type*} : List (List A) → Query (List A)
  | [] => ([],0)
  | a::as =>
      let xs := flattenQ as
      let out := appendQ a xs.1
      (out.1,xs.2+out.2+1)
def productQ {A B : Type*} (a : List A) (b : List B) : Query (List (A × B)) :=
  let rows := mapQ (fun x => mapQ (fun y => ((x,y),1)) b) a
  let out := flattenQ rows.1
  (out.1,rows.2+out.2)
theorem mapQ_value {A B : Type*} (f : A → Query B) (as : List A) :
    (mapQ f as).1 = as.map (fun a => (f a).1) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [mapQ,ih]
theorem filterQ_value {A : Type*} (p : A → Query Bool) (as : List A) :
    (filterQ p as).1 = as.filter (fun a => (p a).1) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      cases h : (p a).1 <;> simp [filterQ,ih,h]
theorem rangeQ_value (n : ℕ) : (rangeQ n).1 = List.range n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [rangeQ,ih] using (List.range_succ (n := n)).symm
theorem flattenQ_value {A : Type*} (as : List (List A)) :
    (flattenQ as).1 = as.flatten := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [flattenQ,appendQ,ih]
theorem productQ_value {A B : Type*} (a : List A) (b : List B) :
    (productQ a b).1 = a.flatMap (fun x => b.map (fun y => (x,y))) := by
  simp [productQ,flattenQ_value,mapQ_value,List.flatMap]
structure Code where
  family : ℕ := 0
  owner : ℕ := 0
  copy : ℕ := 0
  part : ℕ := 0
  p : ℕ := 0
  q : ℕ := 0
  i : ℕ := 0
  j : ℕ := 0
  k : ℕ := 0
  l : ℕ := 0
  deriving DecidableEq, BEq, Repr
@[ext] theorem Code.ext {a b : Code}
    (h_family : a.family = b.family)
    (h_owner : a.owner = b.owner)
    (h_copy : a.copy = b.copy)
    (h_part : a.part = b.part)
    (h_p : a.p = b.p)
    (h_q : a.q = b.q)
    (h_i : a.i = b.i)
    (h_j : a.j = b.j)
    (h_k : a.k = b.k)
    (h_l : a.l = b.l)
    : a = b := by
  cases a; cases b
  cases h_family
  cases h_owner
  cases h_copy
  cases h_part
  cases h_p
  cases h_q
  cases h_i
  cases h_j
  cases h_k
  cases h_l
  rfl
def equalCodeQ (a b : Code) : Query Bool := (decide (a=b),41)
def handleQ (c : Code) : List Code → Query ℕ
  | [] => (0,0)
  | a::as =>
      let h := equalCodeQ c a
      if h.1 then (0,h.2+1) else
        let r := handleQ c as
        (r.1+1,h.2+r.2+2)
structure FaceRow where
  code : Code
  x : ℕ
  z : ℕ
  q0 : ℕ
  q1 : ℕ
  deriving DecidableEq, BEq, Repr
structure Frame where
  nx : ℕ
  nq : ℕ
  nz : ℕ
  nf : ℕ
  xs : List Code
  qs : List Code
  zs : List Code
  faces : List FaceRow
  deriving Repr
def xqFaceTestQ (x q : ℕ) (f : FaceRow) : Query Bool :=
  (decide (f.x=x ∧ (f.q0=q ∨ f.q1=q)),8)
def qzFaceTestQ (q z : ℕ) (f : FaceRow) : Query Bool :=
  (decide (f.z=z ∧ (f.q0=q ∨ f.q1=q)),8)
def anyQ {A : Type*} (p : A → Query Bool) : List A → Query Bool
  | [] => (false,0)
  | a::as =>
      let h := p a
      let hs := anyQ p as
      (h.1 || hs.1,h.2+hs.2+1)
theorem anyQ_value {A : Type*} (p : A → Query Bool) (as : List A) :
    (anyQ p as).1 = as.any (fun a => (p a).1) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [anyQ,ih]
def xqQ (F : Frame) (x q : ℕ) : Query Bool := anyQ (xqFaceTestQ x q) F.faces
def qzQ (F : Frame) (q z : ℕ) : Query Bool := anyQ (qzFaceTestQ q z) F.faces
def seedFrame : Frame where
  nx := 2
  nq := 5
  nz := 2
  nf := 4
  xs := [⟨0,0,0,0,0,0,0,0,0,0⟩,⟨0,1,0,0,0,0,0,0,0,0⟩]
  qs := [{owner:=0},{owner:=1},{owner:=2},{owner:=3},{owner:=4}]
  zs := [⟨0,0,0,0,0,0,0,0,0,0⟩,⟨0,1,0,0,0,0,0,0,0,0⟩]
  faces := [⟨{owner:=0},0,0,0,4⟩,⟨{owner:=1},0,1,1,4⟩,
    ⟨{owner:=2},1,0,2,4⟩,⟨{owner:=3},1,1,3,4⟩]
def seedFrameQ : Query Frame :=
  (seedFrame,11*(2+5+2)+15*4+9)
theorem actual_xq_iff_face (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (x : P.X) (q : P.Q) :
    P.xq x q=true ↔ ∃ f : P.Face, ∃ c : Two, P.faceX f=x ∧ P.faceQ f c=q := by
  constructor
  · intro h
    let z := A.qzRoot q
    let shared : SharedQ P.data x z.1 := ⟨q,by simp [h,z.2]⟩
    obtain ⟨⟨f,c⟩,hc⟩ := (P.perfectPairing x z.1).2 shared
    exact ⟨f.1,c,f.2.1,congrArg Subtype.val hc⟩
  · rintro ⟨f,c,hx,hq⟩
    simpa [hx,hq] using P.data.faceQ_xq f c
theorem actual_qz_iff_face (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (z : P.Z) :
    P.qz q z=true ↔ ∃ f : P.Face, ∃ c : Two, P.faceZ f=z ∧ P.faceQ f c=q := by
  constructor
  · intro h
    let x := A.xqRoot q
    let shared : SharedQ P.data x.1 z := ⟨q,by simp [h,x.2]⟩
    obtain ⟨⟨f,c⟩,hc⟩ := (P.perfectPairing x.1 z).2 shared
    exact ⟨f.1,c,f.2.2,congrArg Subtype.val hc⟩
  · rintro ⟨f,c,hz,hq⟩
    simpa [hz,hq] using P.data.faceQ_qz f c
def flatMapQ {A B : Type*} (f : A → Query (List B)) : List A → Query (List B)
  | [] => ([],0)
  | a::as =>
      let r := f a
      let rs := flatMapQ f as
      let out := appendQ r.1 rs.1
      (out.1,r.2+rs.2+out.2+1)
def collectQ {A : Type*} (qs : List (Query (List A))) : Query (List A) :=
  flatMapQ id qs
theorem flatMapQ_value {A B : Type*} (f : A → Query (List B)) (as : List A) :
    (flatMapQ f as).1=as.flatMap (fun a => (f a).1) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [flatMapQ,appendQ,ih]
def emitQ (c : Code) : Query Code := (c,32)
def singletonQ (c : Code) : Query (List Code) := ([c],33)
def loopQ {A : Type*} (n : ℕ) (f : ℕ → Query (List A)) : Query (List A) :=
  let ids := rangeQ n
  let out := flatMapQ f ids.1
  (out.1,ids.2+out.2)
def mapCodesQ (f : Code → Code) (xs : List Code) : Query (List Code) :=
  mapQ (fun c => emitQ (f c)) xs
def facesAtXQ (F : Frame) (x : ℕ) : Query (List (ℕ × FaceRow)) :=
  let ids := rangeQ F.nf
  let rows := mapQ (fun i => ((i,F.faces[i]?.getD ⟨{},0,0,0,0⟩),2*i+3)) ids.1
  let out := filterQ (fun r => (decide (r.2.x=x),3)) rows.1
  (out.1,ids.2+rows.2+out.2)
def starQsQ (F : Frame) (x : ℕ) : Query (List ℕ) :=
  let ids := rangeQ F.nq
  let out := filterQ (xqQ F x) ids.1
  (out.1,ids.2+out.2)
def starZsQ (F : Frame) (x : ℕ) : Query (List ℕ) :=
  let ids := rangeQ F.nz
  let out := filterQ (fun z => anyQ (fun f : FaceRow =>
    (decide (f.x=x ∧ f.z=z),5)) F.faces) ids.1
  (out.1,ids.2+out.2)
def starSidesQ (F : Frame) (x : ℕ) : Query (List (ℕ × ℕ)) :=
  let qs := rangeQ F.nq
  let zs := rangeQ F.nz
  let pairs := productQ qs.1 zs.1
  let out := filterQ (fun e => anyQ (fun f : FaceRow =>
    (decide (f.x=x ∧ f.z=e.2 ∧ (f.q0=e.1 ∨ f.q1=e.1)),10)) F.faces) pairs.1
  (out.1,qs.2+zs.2+pairs.2+out.2)
def subVerticesQ (F : Frame) (x m : ℕ) : Query (List Code) :=
  let qs := starQsQ F x
  let zs := starZsQ F x
  let sides := starSidesQ F x
  let faces := facesAtXQ F x
  let qv := mapQ (fun q => emitQ {owner:=x,part:=1,p:=q}) qs.1
  let zv := mapQ (fun z => emitQ {owner:=x,part:=2,p:=z}) zs.1
  let radial := flatMapQ (fun q => loopQ (m-1) (fun i =>
    singletonQ {owner:=x,part:=3,p:=q,i:=i})) qs.1
  let side := flatMapQ (fun e => loopQ (m-1) (fun i =>
    singletonQ {owner:=x,part:=4,p:=e.1,q:=e.2,i:=i})) sides.1
  let bulk := flatMapQ (fun f => loopQ (m-1) (fun i => loopQ (m-1) (fun j =>
    singletonQ {owner:=x,part:=5,p:=f.1,i:=i,j:=j}))) faces.1
  let out := collectQ [singletonQ {owner:=x},qv,zv,radial,side,bulk]
  (out.1,qs.2+zs.2+sides.2+faces.2+out.2)
def subEdgesQ (F : Frame) (x m : ℕ) : Query (List Code) :=
  let qs := starQsQ F x
  let sides := starSidesQ F x
  let faces := facesAtXQ F x
  let radial := flatMapQ (fun q => loopQ m (fun i =>
    singletonQ {owner:=x,p:=q,i:=i})) qs.1
  let side := flatMapQ (fun e => loopQ m (fun i =>
    singletonQ {owner:=x,part:=1,p:=e.1,q:=e.2,i:=i})) sides.1
  let horizontal := flatMapQ (fun f => loopQ m (fun i => loopQ (m-1) (fun j =>
    singletonQ {owner:=x,part:=2,p:=f.1,i:=i,j:=j}))) faces.1
  let vertical := flatMapQ (fun f => loopQ (m-1) (fun i => loopQ m (fun j =>
    singletonQ {owner:=x,part:=3,p:=f.1,i:=i,j:=j}))) faces.1
  let out := collectQ [radial,side,horizontal,vertical]
  (out.1,qs.2+sides.2+faces.2+out.2)
def subFacesQ (F : Frame) (x m : ℕ) : Query (List Code) :=
  let faces := facesAtXQ F x
  let out := flatMapQ (fun f => loopQ m (fun i => loopQ m (fun j =>
    singletonQ {owner:=x,p:=f.1,i:=i,j:=j}))) faces.1
  (out.1,faces.2+out.2)
def doubleVerticesQ (F : Frame) (x m : ℕ) : Query (List Code) :=
  let cells := subVerticesQ F x m
  let copies := flatMapQ (fun c => mapCodesQ (fun v => {v with copy:=c}) cells.1) [0,1]
  (copies.1,cells.2+copies.2)
def doubleEdgesQ (F : Frame) (x m : ℕ) : Query (List Code) :=
  let edges := subEdgesQ F x m
  let vertices := subVerticesQ F x m
  let ends := flatMapQ (fun c => mapCodesQ (fun e => {e with copy:=c}) edges.1) [0,1]
  let boundary := filterQ (fun v => (decide (v.part=1 ∨ v.part=2 ∨ v.part=4),7)) vertices.1
  let bridge := mapCodesQ (fun v =>
    {v with part:=if v.part=1 then 4 else if v.part=2 then 5 else 6}) boundary.1
  let out := collectQ [ends,bridge]
  (out.1,edges.2+vertices.2+boundary.2+out.2)
def doubleFacesQ (F : Frame) (x m : ℕ) : Query (List Code) :=
  let faces := subFacesQ F x m
  let sides := starSidesQ F x
  let ends := flatMapQ (fun c => mapCodesQ (fun f => {f with copy:=c}) faces.1) [0,1]
  let rect := flatMapQ (fun e => loopQ m (fun i =>
    singletonQ {owner:=x,part:=1,p:=e.1,q:=e.2,i:=i})) sides.1
  let out := collectQ [ends,rect]
  (out.1,faces.2+sides.2+out.2)
def qNeighborsQ (F : Frame) (q : ℕ) : Query (List ℕ) :=
  let ids := rangeQ F.nz
  let out := filterQ (qzQ F q) ids.1
  (out.1,ids.2+out.2)
def qDoubleVerticesQ (F : Frame) (q m : ℕ) : Query (List Code) :=
  let ns := qNeighborsQ F q
  let endpoint := mapQ (fun z => emitQ {owner:=q,part:=1,p:=z}) ns.1
  let interior := flatMapQ (fun z => loopQ (m-1) (fun i =>
    singletonQ {owner:=q,part:=2,p:=z,i:=i})) ns.1
  let cells := collectQ [singletonQ {owner:=q},endpoint,interior]
  let out := flatMapQ (fun c => mapCodesQ (fun v => {v with copy:=c}) cells.1) [0,1]
  (out.1,ns.2+cells.2+out.2)
def qDoubleEdgesQ (F : Frame) (q m : ℕ) : Query (List Code) :=
  let ns := qNeighborsQ F q
  let ends := flatMapQ (fun c => flatMapQ (fun z => loopQ m (fun i =>
    singletonQ {owner:=q,copy:=c,p:=z,i:=i})) ns.1) [0,1]
  let vertical := mapQ (fun z => emitQ {owner:=q,part:=1,p:=z}) ns.1
  let out := collectQ [ends,vertical]
  (out.1,ns.2+out.2)
def rxXCodesQ (F : Frame) (m : ℕ) : Query (List Code) :=
  loopQ F.nx (fun x => doubleVerticesQ F x m)
def rxQCodesQ (F : Frame) (m : ℕ) : Query (List Code) :=
  let localPart := loopQ F.nx (fun x => doubleEdgesQ F x m)
  let qlocal := loopQ F.nq (fun q =>
    let cells := qDoubleVerticesQ F q m
    let out := mapCodesQ (fun c => {c with family:=1}) cells.1
    (out.1,cells.2+out.2))
  collectQ [localPart,qlocal]
def rxZCodesQ (F : Frame) (m : ℕ) : Query (List Code) :=
  let localPart := loopQ F.nx (fun x => doubleFacesQ F x m)
  let qlocal := loopQ F.nq (fun q =>
    let cells := qDoubleEdgesQ F q m
    let out := mapCodesQ (fun c => {c with family:=1}) cells.1
    (out.1,cells.2+out.2))
  let old := loopQ F.nz (fun z => mapQ (fun c => emitQ {family:=2,owner:=z,copy:=c}) [0,1])
  collectQ [localPart,qlocal,old]
def faceAtQ : List FaceRow → ℕ → Query FaceRow
  | [], _ => (⟨{},0,0,0,0⟩,1)
  | f::_, 0 => (f,2)
  | _::fs, i+1 => let r := faceAtQ fs i; (r.1,r.2+2)
def gridVertexQ (F : Frame) (x m f i j : ℕ) : Query Code :=
  let old := faceAtQ F.faces f
  let v : Code :=
    if i=0 then
      if j=0 then {owner:=x}
      else if j=m then {owner:=x,part:=1,p:=old.1.q1}
      else {owner:=x,part:=3,p:=old.1.q1,i:=j-1}
    else if i=m then
      if j=0 then {owner:=x,part:=1,p:=old.1.q0}
      else if j=m then {owner:=x,part:=2,p:=old.1.z}
      else {owner:=x,part:=4,p:=old.1.q0,q:=old.1.z,i:=j-1}
    else if j=0 then {owner:=x,part:=3,p:=old.1.q0,i:=i-1}
    else if j=m then {owner:=x,part:=4,p:=old.1.q1,q:=old.1.z,i:=i-1}
    else {owner:=x,part:=5,p:=f,i:=i-1,j:=j-1}
  (v,old.2+64)
def horizontalEdgeQ (F : Frame) (x m f i j : ℕ) : Query Code :=
  let old := faceAtQ F.faces f
  (if j=0 then {owner:=x,p:=old.1.q0,i:=i}
   else if j=m then {owner:=x,part:=1,p:=old.1.q1,q:=old.1.z,i:=i}
   else {owner:=x,part:=2,p:=f,i:=i,j:=j-1},old.2+48)
def verticalEdgeQ (F : Frame) (x m f i j : ℕ) : Query Code :=
  let old := faceAtQ F.faces f
  (if i=0 then {owner:=x,p:=old.1.q1,i:=j}
   else if i=m then {owner:=x,part:=1,p:=old.1.q0,q:=old.1.z,i:=j}
   else {owner:=x,part:=3,p:=f,i:=i-1,j:=j},old.2+48)
def segmentVertexQ (x m : ℕ) (e : Code) (endpoint : ℕ) : Query Code :=
  let pos := e.i+endpoint
  (if pos=0 then
     if e.part=0 then {owner:=x} else {owner:=x,part:=1,p:=e.p}
   else if pos=m then
     if e.part=0 then {owner:=x,part:=1,p:=e.p} else {owner:=x,part:=2,p:=e.q}
   else if e.part=0 then {owner:=x,part:=3,p:=e.p,i:=pos-1}
   else {owner:=x,part:=4,p:=e.p,q:=e.q,i:=pos-1},64)
def doubleEdgeVertexQ (F : Frame) (m : ℕ) (e : Code) (endpoint : ℕ) : Query Code :=
  if e.part≥4 then
    (if e.part=4 then {owner:=e.owner,copy:=endpoint,part:=1,p:=e.p}
     else if e.part=5 then {owner:=e.owner,copy:=endpoint,part:=2,p:=e.p}
     else {owner:=e.owner,copy:=endpoint,part:=4,p:=e.p,q:=e.q,i:=e.i},64)
  else
    let v := if e.part=0 ∨ e.part=1 then segmentVertexQ e.owner m e endpoint
      else if e.part=2 then gridVertexQ F e.owner m e.p (e.i+endpoint) (e.j+1)
      else gridVertexQ F e.owner m e.p (e.i+1) (e.j+endpoint)
    ({v.1 with copy:=e.copy},v.2+40)
def qDoubleEdgeVertexQ (m : ℕ) (e : Code) (endpoint : ℕ) : Query Code :=
  if e.part=1 then ({family:=1,owner:=e.owner,copy:=endpoint,part:=1,p:=e.p},48)
  else
    let pos := e.i+endpoint
    (if pos=0 then {family:=1,owner:=e.owner,copy:=e.copy}
     else if pos=m then {family:=1,owner:=e.owner,copy:=e.copy,part:=1,p:=e.p}
     else {family:=1,owner:=e.owner,copy:=e.copy,part:=2,p:=e.p,i:=pos-1},64)
def qEdgeImageQ (x : ℕ) (e : Code) : Query Code :=
  (if e.part=0 then {owner:=x,copy:=e.copy,part:=1,p:=e.owner,q:=e.p,i:=e.i}
   else {owner:=x,part:=5,p:=e.p},48)
def bridgeOfVertexQ (v : Code) : Query Code :=
  ({owner:=v.owner,part:=(if v.part=1 then 4 else if v.part=2 then 5 else 6),
    p:=v.p,q:=v.q,i:=v.i},48)
def rxLocalFaceCodesQ (F : Frame) (m : ℕ) : Query (List Code) :=
  loopQ F.nx (fun x =>
    let fs := doubleFacesQ F x m
    let out := flatMapQ (fun f => flatMapQ (fun a =>
      mapQ (fun b => emitQ {f with k:=a,l:=b}) [0,1]) [0,1]) fs.1
    (out.1,fs.2+out.2))
def rxGlueFaceCodesQ (F : Frame) (m : ℕ) : Query (List Code) :=
  loopQ F.nx (fun x =>
    let qs := starQsQ F x
    let out := flatMapQ (fun q =>
      let es := qDoubleEdgesQ F q m
      let out := flatMapQ (fun e => mapQ (fun a =>
        emitQ {family:=1,owner:=x,copy:=e.copy,part:=e.part,p:=q,q:=e.p,i:=e.i,k:=a}) [0,1]) es.1
      (out.1,es.2+out.2)) qs.1
    (out.1,qs.2+out.2))
def rxOldFaceCodesQ (F : Frame) : Query (List Code) :=
  loopQ F.nf (fun f => mapQ (fun c => emitQ {family:=2,owner:=f,copy:=c}) [0,1])
def rxFaceCodesQ (F : Frame) (m : ℕ) : Query (List Code) :=
  collectQ [rxLocalFaceCodesQ F m,rxGlueFaceCodesQ F m,rxOldFaceCodesQ F]
structure FaceCodes where
  x : Code
  z : Code
  q0 : Code
  q1 : Code
@[ext] theorem FaceCodes.ext {a b : FaceCodes}
    (hx : a.x=b.x) (hz : a.z=b.z) (h0 : a.q0=b.q0) (h1 : a.q1=b.q1) : a=b := by
  cases a; cases b
  cases hx; cases hz; cases h0; cases h1
  rfl
def localFaceEndpointsQ (F : Frame) (m : ℕ) (f : Code) : Query FaceCodes :=
  let z : Code := {f with k:=0,l:=0}
  if f.part=0 then
    let x := gridVertexQ F f.owner m f.p (f.i+f.k) (f.j+f.l)
    let q0 := horizontalEdgeQ F f.owner m f.p f.i (f.j+f.l)
    let q1 := verticalEdgeQ F f.owner m f.p (f.i+f.k) f.j
    (⟨{x.1 with copy:=f.copy},z,{q0.1 with copy:=f.copy},{q1.1 with copy:=f.copy}⟩,
      x.2+q0.2+q1.2+104)
  else
    let edge : Code := {owner:=f.owner,copy:=f.k,part:=1,p:=f.p,q:=f.q,i:=f.i}
    let x := doubleEdgeVertexQ F m edge f.l
    let q1 := bridgeOfVertexQ x.1
    (⟨x.1,z,edge,q1.1⟩,x.2+q1.2+72)
def glueFaceEndpointsQ (F : Frame) (m : ℕ) (f : Code) : Query FaceCodes :=
  let e : Code := {family:=1,owner:=f.p,copy:=f.copy,part:=f.part,p:=f.q,i:=f.i}
  let image := qEdgeImageQ f.owner e
  let x := doubleEdgeVertexQ F m image.1 f.k
  let q1 := qDoubleEdgeVertexQ m e f.k
  (⟨x.1,e,image.1,q1.1⟩,image.2+x.2+q1.2+72)
def oldFaceEndpointsQ (F : Frame) (f : Code) : Query FaceCodes :=
  let old := faceAtQ F.faces f.owner
  (⟨{owner:=old.1.x,copy:=f.copy,part:=2,p:=old.1.z},
    {family:=2,owner:=old.1.z,copy:=f.copy},
    {family:=1,owner:=old.1.q0,copy:=f.copy,part:=1,p:=old.1.z},
    {family:=1,owner:=old.1.q1,copy:=f.copy,part:=1,p:=old.1.z}⟩,old.2+136)
def faceEndpointsQ (F : Frame) (m : ℕ) (f : Code) : Query FaceCodes :=
  let out := if f.family=0 then localFaceEndpointsQ F m f
    else if f.family=1 then glueFaceEndpointsQ F m f else oldFaceEndpointsQ F f
  (out.1,out.2+5)
def indexFaceQ (xs qs zs : List Code) (code : Code) (f : FaceCodes) : Query FaceRow :=
  let x := handleQ f.x xs
  let z := handleQ f.z zs
  let q0 := handleQ f.q0 qs
  let q1 := handleQ f.q1 qs
  (⟨code,x.1,z.1,q0.1,q1.1⟩,x.2+z.2+q0.2+q1.2+7)
def packFrameQ (xs qs zs : List Code) (fs : List FaceRow) : Query Frame :=
  (⟨xs.length,qs.length,zs.length,fs.length,xs,qs,zs,fs⟩,
    xs.length+qs.length+zs.length+fs.length+13)
def memCodeQ (c : Code) (as : List Code) : Query Bool :=
  anyQ (equalCodeQ c) as
theorem memCodeQ_correct (c : Code) (as : List Code) :
    (memCodeQ c as).1=true ↔ c∈as := by
  induction as with
  | nil => simp [memCodeQ,anyQ]
  | cons a as ih => simp [memCodeQ,anyQ,equalCodeQ] at *; tauto
def dedupQ : List Code → Query (List Code)
  | [] => ([],0)
  | a::as =>
      let tail := dedupQ as
      let found := memCodeQ a tail.1
      (if found.1 then tail.1 else a::tail.1,tail.2+found.2+2)
theorem dedupQ_mem (c : Code) (as : List Code) : c∈(dedupQ as).1 ↔ c∈as := by
  induction as generalizing c with
  | nil => simp [dedupQ]
  | cons a as ih =>
      simp only [dedupQ]
      split <;> rename_i h
      · have ha := (memCodeQ_correct a (dedupQ as).1).mp h
        have haa := (ih a).mp ha
        simpa only [List.mem_cons,ih] using (show c∈as ↔ c=a ∨ c∈as by
          constructor
          · exact Or.inr
          · rintro (rfl|hc)
            · exact haa
            · exact hc)
      · simp only [List.mem_cons,ih]
theorem dedupQ_nodup (as : List Code) : (dedupQ as).1.Nodup := by
  induction as with
  | nil => simp [dedupQ]
  | cons a as ih =>
      simp only [dedupQ]
      split <;> rename_i h
      · exact ih
      · apply List.nodup_cons.mpr
        exact ⟨fun ha => h ((memCodeQ_correct a _).mpr ha),ih⟩
def rxFrameQ (F : Frame) (m : ℕ) : Query Frame :=
  let rawX := rxXCodesQ F m
  let rawQ := rxQCodesQ F m
  let rawZ := rxZCodesQ F m
  let rawF := rxFaceCodesQ F m
  let xs := dedupQ rawX.1
  let qs := dedupQ rawQ.1
  let zs := dedupQ rawZ.1
  let fc := dedupQ rawF.1
  let rows := mapQ (fun f =>
    let points := faceEndpointsQ F m f
    let out := indexFaceQ xs.1 qs.1 zs.1 f points.1
    (out.1,points.2+out.2)) fc.1
  let out := packFrameQ xs.1 qs.1 zs.1 rows.1
  (out.1,rawX.2+rawQ.2+rawZ.2+rawF.2+xs.2+qs.2+zs.2+fc.2+rows.2+out.2+16)
def transposeFrameQ (F : Frame) : Query Frame :=
  let rows := mapQ (fun f => (⟨f.code,f.z,f.x,f.q0,f.q1⟩,17)) F.faces
  (⟨F.nz,F.nq,F.nx,F.nf,F.zs,F.qs,F.xs,rows.1⟩,rows.2+17)
def rzFrameQ (F : Frame) (m : ℕ) : Query Frame :=
  let input := transposeFrameQ F
  let next := rxFrameQ input.1 m
  let output := transposeFrameQ next.1
  (output.1,input.2+next.2+output.2)
def nextFrameQ (S : OddScale) (n : ℕ) (F : Frame) : Query Frame :=
  let out := if n%2=0 then rxFrameQ F S.half else rzFrameQ F S.half
  (out.1,out.2+5)
def lastFrameQ : List Frame → Query Frame
  | [] => (seedFrame,1)
  | [f] => (f,2)
  | _::f::fs => let r := lastFrameQ (f::fs); (r.1,r.2+2)
def historyQ (S : OddScale) : ℕ → Query (List Frame)
  | 0 => ([seedFrameQ.1],seedFrameQ.2+1)
  | n+1 =>
      let before := historyQ S n
      let last := lastFrameQ before.1
      let next := nextFrameQ S n last.1
      let out := appendQ before.1 [next.1]
      (out.1,before.2+last.2+next.2+out.2+2)
def generateQ (S : OddScale) (n : ℕ) : Query Frame :=
  let frames := historyQ S n
  let final := lastFrameQ frames.1
  (final.1,frames.2+final.2)
def denseXQQ (F : Frame) : Query (List (ℕ × ℕ × Bool)) :=
  loopQ F.nx (fun x =>
    let qs := rangeQ F.nq
    let out := mapQ (fun q => let hit := xqQ F x q; ((x,q,hit.1),hit.2+4)) qs.1
    (out.1,qs.2+out.2))
def denseQZQ (F : Frame) : Query (List (ℕ × ℕ × Bool)) :=
  loopQ F.nq (fun q =>
    let zs := rangeQ F.nz
    let out := mapQ (fun z => let hit := qzQ F q z; ((q,z,hit.1),hit.2+4)) zs.1
    (out.1,zs.2+out.2))
def vertexCodesQ (F : Frame) : Query (List Code) :=
  let raw := collectQ [
    loopQ F.nx (fun x => singletonQ {owner:=x}),
    loopQ F.nq (fun q => singletonQ {family:=1,owner:=q}),
    loopQ F.nz (fun z => singletonQ {family:=2,owner:=z})]
  let unique := dedupQ raw.1
  (unique.1,raw.2+unique.2+1)
def edgeCodesQ (F : Frame) : Query (List Code) :=
  let a := denseXQQ F
  let b := denseQZQ F
  let ax := filterQ (fun t => (t.2.2,2)) a.1
  let bz := filterQ (fun t => (t.2.2,2)) b.1
  let left := mapQ (fun t => emitQ {owner:=t.1,p:=t.2.1}) ax.1
  let right := mapQ (fun t => emitQ {family:=1,owner:=t.1,p:=t.2.1}) bz.1
  let out := collectQ [left,right]
  let unique := dedupQ out.1
  (unique.1,a.2+b.2+ax.2+bz.2+out.2+unique.2+1)
def edgeVertexTestQ (e v : Code) : Query Bool :=
  (if e.family=0 then
     decide ((v.family=0 ∧ v.owner=e.owner) ∨ (v.family=1 ∧ v.owner=e.p))
   else decide ((v.family=1 ∧ v.owner=e.owner) ∨ (v.family=2 ∧ v.owner=e.p)),20)
def faceEdgeTestQ (f : FaceRow) (e : Code) : Query Bool :=
  (if e.family=0 then decide (e.owner=f.x ∧ (e.p=f.q0 ∨ e.p=f.q1))
   else decide (e.p=f.z ∧ (e.owner=f.q0 ∨ e.owner=f.q1)),20)
def cellularBoundary1Q (vertices edges : List Code) : Query (List (ℕ × ℕ × Bool)) :=
  let ei := rangeQ edges.length
  let vi := rangeQ vertices.length
  let out := flatMapQ (fun e => mapQ (fun v =>
    let ec := edges[e]?.getD {}
    let vc := vertices[v]?.getD {}
    let hit := edgeVertexTestQ ec vc
    ((v,e,hit.1),2*e+2*v+hit.2+8)) vi.1) ei.1
  (out.1,vertices.length+edges.length+ei.2+vi.2+out.2+2)
def cellularBoundary2Q (F : Frame) (edges : List Code) : Query (List (ℕ × ℕ × Bool)) :=
  let fi := rangeQ F.nf
  let ei := rangeQ edges.length
  let out := flatMapQ (fun f =>
    let row := faceAtQ F.faces f
    let cells := mapQ (fun e =>
      let ec := edges[e]?.getD {}
      let hit := faceEdgeTestQ row.1 ec
      ((e,f,hit.1),2*e+hit.2+6)) ei.1
    (cells.1,row.2+cells.2)) fi.1
  (out.1,edges.length+fi.2+ei.2+out.2+2)
structure Output where
  frame : Frame
  xq : List (ℕ × ℕ × Bool)
  qz : List (ℕ × ℕ × Bool)
  vertices : List Code
  edges : List Code
  boundary1 : List (ℕ × ℕ × Bool)
  boundary2 : List (ℕ × ℕ × Bool)
  deriving Repr
def runQ (S : OddScale) (n : ℕ) : Query Output :=
  let frame := generateQ S n
  let a := denseXQQ frame.1
  let b := denseQZQ frame.1
  let vertices := vertexCodesQ frame.1
  let edges := edgeCodesQ frame.1
  let boundary1 := cellularBoundary1Q vertices.1 edges.1
  let boundary2 := cellularBoundary2Q frame.1 edges.1
  (⟨frame.1,a.1,b.1,vertices.1,edges.1,boundary1.1,boundary2.1⟩,
    frame.2+a.2+b.2+vertices.2+edges.2+boundary1.2+boundary2.2+8)
structure SeedRow where
  kind : ℕ
  handle : ℕ
  counter : ℕ
  point : ℤ × ℤ × ℤ
  deriving DecidableEq, Repr
def seedRowsQ : Query (List SeedRow) :=
  let rows := collectQ [
    let ids := rangeQ 2
    let out := mapQ (fun i => (⟨0,i,0,(0,0,0)⟩,7)) ids.1
    (out.1,ids.2+out.2),
    let ids := rangeQ 5
    let out := mapQ (fun i => (⟨1,i,0,(0,0,0)⟩,7)) ids.1
    (out.1,ids.2+out.2),
    let ids := rangeQ 2
    let out := mapQ (fun i => (⟨2,i,0,(0,0,0)⟩,7)) ids.1
    (out.1,ids.2+out.2)]
  (rows.1,rows.2+1)
structure Refines (F : Frame) (P : TannerSquarePresentation) where
  xIndex : P.X ≃ Fin F.nx
  qIndex : P.Q ≃ Fin F.nq
  zIndex : P.Z ≃ Fin F.nz
  fIndex : P.Face ≃ Fin F.nf
  x_length : F.xs.length=F.nx
  q_length : F.qs.length=F.nq
  z_length : F.zs.length=F.nz
  f_length : F.faces.length=F.nf
  x_nodup : F.xs.Nodup
  q_nodup : F.qs.Nodup
  z_nodup : F.zs.Nodup
  f_nodup : (F.faces.map FaceRow.code).Nodup
  face_x : ∀ f : P.Face, (faceAtQ F.faces (fIndex f).val).1.x=(xIndex (P.faceX f)).val
  face_z : ∀ f : P.Face, (faceAtQ F.faces (fIndex f).val).1.z=(zIndex (P.faceZ f)).val
  face_q0 : ∀ f : P.Face, (faceAtQ F.faces (fIndex f).val).1.q0=(qIndex (P.faceQ f 0)).val
  face_q1 : ∀ f : P.Face, (faceAtQ F.faces (fIndex f).val).1.q1=(qIndex (P.faceQ f 1)).val
def encodeStarVertex {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (x : P.X) (v : XStarVertex P x) : Code :=
  match v.1 with
  | .x _ => {owner:=(r.xIndex x).val}
  | .q q => {owner:=(r.xIndex x).val,part:=1,p:=(r.qIndex q).val}
  | .z z => {owner:=(r.xIndex x).val,part:=2,p:=(r.zIndex z).val}
def encodeStarEdge {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (x : P.X) (e : XStarEdge P x) (i : ℕ) : Code :=
  match e.1 with
  | .inl a => {owner:=(r.xIndex x).val,p:=(r.qIndex a.1.2).val,i:=i}
  | .inr a =>
      { owner:=(r.xIndex x).val
        part:=1
        p:=(r.qIndex a.1.1).val
        q:=(r.zIndex a.1.2).val
        i:=i }
def encodeSubVertex {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (x : P.X) (S : OddScale) : SubdivisionVertex P x S → Code
  | .inl v => encodeStarVertex r x v
  | .inr (.inl ei) =>
      let e := encodeStarEdge r x ei.1 ei.2.val
      {e with part:=if e.part=0 then 3 else 4}
  | .inr (.inr f) =>
      { owner:=(r.xIndex x).val
        part:=5
        p:=(r.fIndex f.1.1).val
        i:=f.2.1.val
        j:=f.2.2.val }
def encodeSubEdge {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (x : P.X) (S : OddScale) : SubdivisionEdge P x S → Code
  | .inl ei => encodeStarEdge r x ei.1 ei.2.val
  | .inr (.inl f) =>
      { owner:=(r.xIndex x).val
        part:=2
        p:=(r.fIndex f.1.1).val
        i:=f.2.1.val
        j:=f.2.2.val }
  | .inr (.inr f) =>
      { owner:=(r.xIndex x).val
        part:=3
        p:=(r.fIndex f.1.1).val
        i:=f.2.1.val
        j:=f.2.2.val }
def encodeDoubleVertex {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (x : P.X) (S : OddScale) (v : DoubleCylinderVertex P x S) : Code :=
  {encodeSubVertex r x S v.2 with copy:=v.1.val}
def encodeDoubleEdge {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (x : P.X) (S : OddScale) : DoubleCylinderEdge P x S → Code
  | .inl e => {encodeSubEdge r x S e.2 with copy:=e.1.val}
  | .inr v =>
      let a := encodeSubVertex r x S v.1
      {a with part:=if a.part=1 then 4 else if a.part=2 then 5 else 6}
def encodeDoubleFace {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (x : P.X) (S : OddScale) : DoubleCylinderFace P x S → Code
  | .inl f =>
      { owner:=(r.xIndex x).val
        copy:=f.1.val
        p:=(r.fIndex f.2.1.1).val
        i:=f.2.2.1.val
        j:=f.2.2.2.val }
  | .inr e => encodeSubEdge r x S e.1
def encodeQVertex {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (q : P.Q) (S : OddScale) (v : QDoubleCylinderVertex P q S) : Code :=
  let code : Code := match v.2 with
    | .inl (.inl _) => {owner:=(r.qIndex q).val}
    | .inl (.inr z) => {owner:=(r.qIndex q).val,part:=1,p:=(r.zIndex z.1).val}
    | .inr zi => {owner:=(r.qIndex q).val,part:=2,p:=(r.zIndex zi.1.1).val,i:=zi.2.val}
  {code with copy:=v.1.val}
def encodeQEdge {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (q : P.Q) (S : OddScale) : QDoubleCylinderEdge P q S → Code
  | .inl e => {owner:=(r.qIndex q).val,copy:=e.1.val,p:=(r.zIndex e.2.1.1).val,i:=e.2.2.val}
  | .inr z => {owner:=(r.qIndex q).val,part:=1,p:=(r.zIndex z.1).val}
def encodeRX0 {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (S : OddScale) (x : RX0 P S) : Code :=
  encodeDoubleVertex r x.1 S x.2
def encodeRX1 {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (S : OddScale) : RX1 P S → Code
  | .inl e => encodeDoubleEdge r e.1 S e.2
  | .inr v => {encodeQVertex r v.1 S v.2 with family:=1}
def encodeRX2 {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (S : OddScale) : RX2 P S → Code
  | .inl (.inl f) => encodeDoubleFace r f.1 S f.2
  | .inl (.inr e) => {encodeQEdge r e.1 S e.2 with family:=1}
  | .inr z => {family:=2,owner:=(r.zIndex z.1).val,copy:=z.2.val}
def encodeRXFace {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (S : OddScale) : RXFace P S → Code
  | .inl f => {encodeDoubleFace r f.1 S f.2.1 with k:=f.2.2.1.val,l:=f.2.2.2.val}
  | .inr (.inl f) =>
      let e := encodeQEdge r f.1.1.2 S f.2.1
      { family:=1
        owner:=(r.xIndex f.1.1.1).val
        copy:=e.copy
        part:=e.part
        p:=e.owner
        q:=e.p
        i:=e.i
        k:=f.2.2.val }
  | .inr (.inr f) => {family:=2,owner:=(r.fIndex f.1).val,copy:=f.2.val}
theorem faceAtQ_get (fs : List FaceRow) (i : Fin fs.length) :
    (faceAtQ fs i.val).1=fs.get i := by
  induction fs with
  | nil => exact Fin.elim0 i
  | cons f fs ih =>
      rcases i with ⟨i,hi⟩
      cases i with
      | zero => rfl
      | succ i =>
          have hj : i< fs.length := by simpa using hi
          simpa [faceAtQ] using ih ⟨i,hj⟩
theorem faceAtQ_mem (F : Frame) (P : TannerSquarePresentation) (r : Refines F P)
    (f : P.Face) : (faceAtQ F.faces (r.fIndex f).val).1∈F.faces := by
  have hi : (r.fIndex f).val< F.faces.length := by rw [r.f_length]; exact (r.fIndex f).isLt
  rw [faceAtQ_get F.faces ⟨(r.fIndex f).val,hi⟩]
  exact List.get_mem _ _
theorem faceRows_exhaustive (F : Frame) (P : TannerSquarePresentation)
    (r : Refines F P) (row : FaceRow) (hrow : row∈F.faces) :
    ∃ f : P.Face, (faceAtQ F.faces (r.fIndex f).val).1=row := by
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hrow
  let k : Fin F.nf := ⟨j.val,by rw [←r.f_length]; exact j.isLt⟩
  refine ⟨r.fIndex.symm k,?_⟩
  rw [r.fIndex.apply_symm_apply]
  simpa [k,faceAtQ_get] using hj
theorem anyQ_exists {A : Type*} (p : A → Query Bool) (as : List A) :
    (anyQ p as).1=true ↔ ∃a∈as,(p a).1=true := by
  induction as with
  | nil => simp [anyQ]
  | cons a as ih => simp [anyQ,ih]
theorem bool_ext {a b : Bool} (h : a=true ↔ b=true) : a=b := by
  cases a <;> cases b <;> simp_all
theorem refines_xq {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (A : TannerSquareAdmissible P) (x : P.X) (q : P.Q) :
    (xqQ F (r.xIndex x).val (r.qIndex q).val).1=P.xq x q := by
  apply bool_ext
  rw [xqQ,anyQ_exists,actual_xq_iff_face P A]
  constructor
  · rintro ⟨row,hrow,h⟩
    obtain ⟨f,hf⟩ := faceRows_exhaustive F P r row hrow
    subst row
    simp only [xqFaceTestQ,decide_eq_true_eq,r.face_x,r.face_q0,r.face_q1] at h
    have hx : P.faceX f=x := r.xIndex.injective (Fin.ext h.1)
    rcases h.2 with hq|hq
    · exact ⟨f,0,hx,r.qIndex.injective (Fin.ext hq)⟩
    · exact ⟨f,1,hx,r.qIndex.injective (Fin.ext hq)⟩
  · rintro ⟨f,c,hx,hq⟩
    refine ⟨_,faceAtQ_mem F P r f,?_⟩
    have hc : c=0 ∨ c=1 := by
      fin_cases c <;> simp
    rcases hc with rfl|rfl <;>
      simp [xqFaceTestQ,r.face_x,r.face_q0,r.face_q1,hx,hq]
theorem refines_qz {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (A : TannerSquareAdmissible P) (q : P.Q) (z : P.Z) :
    (qzQ F (r.qIndex q).val (r.zIndex z).val).1=P.qz q z := by
  apply bool_ext
  rw [qzQ,anyQ_exists,actual_qz_iff_face P A]
  constructor
  · rintro ⟨row,hrow,h⟩
    obtain ⟨f,hf⟩ := faceRows_exhaustive F P r row hrow
    subst row
    simp only [qzFaceTestQ,decide_eq_true_eq,r.face_z,r.face_q0,r.face_q1] at h
    have hz : P.faceZ f=z := r.zIndex.injective (Fin.ext h.1)
    rcases h.2 with hq|hq
    · exact ⟨f,0,hz,r.qIndex.injective (Fin.ext hq)⟩
    · exact ⟨f,1,hz,r.qIndex.injective (Fin.ext hq)⟩
  · rintro ⟨f,c,hz,hq⟩
    refine ⟨_,faceAtQ_mem F P r f,?_⟩
    have hc : c=0 ∨ c=1 := by
      fin_cases c <;> simp
    rcases hc with rfl|rfl <;>
      simp [qzFaceTestQ,r.face_z,r.face_q0,r.face_q1,hz,hq]
def seedRefines : Refines seedFrame baseTannerSquarePresentation where
  xIndex := Equiv.refl _
  qIndex := Equiv.refl _
  zIndex := Equiv.refl _
  fIndex := Equiv.refl _
  x_length := rfl
  q_length := rfl
  z_length := rfl
  f_length := rfl
  x_nodup := by decide
  q_nodup := by decide
  z_nodup := by decide
  f_nodup := by decide
  face_x := by intro f; fin_cases f <;> rfl
  face_z := by intro f; fin_cases f <;> rfl
  face_q0 := by intro f; fin_cases f <;> rfl
  face_q1 := by intro f; fin_cases f <;> rfl
theorem encode_gridVertex {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (x : P.X) (S : OddScale) (f : XStarFace P x)
    (i j : Fin (S.half+1)) :
    encodeSubVertex r x S (subdivisionGridVertex P x S f i j)=
      (gridVertexQ F (r.xIndex x).val S.half (r.fIndex f.1).val i.val j.val).1 := by
  have hm : S.half≠0 := Nat.ne_of_gt S.half_pos
  by_cases hi0 : i.val=0
  <;> by_cases him : i.val=S.half
  <;> by_cases hj0 : j.val=0
  <;> by_cases hjm : j.val=S.half
  all_goals simp only [subdivisionGridVertex,gridVertexQ,encodeSubVertex,encodeStarVertex,
    encodeStarEdge,xStarFaceXVertex,xStarFaceQVertex,xStarFaceZVertex,
    xStarFaceXQEdge,xStarFaceQZEdge,hi0,him,hj0,hjm,
    faceXQEdge,faceQZEdge,hm,r.face_q0,r.face_q1,r.face_z,ite_true,ite_false]
  all_goals rfl
theorem encode_horizontalEdge {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (x : P.X) (S : OddScale) (f : XStarFace P x)
    (i : Fin S.half) (j : Fin (S.half+1)) :
    encodeSubEdge r x S (subdivisionHorizontalEdge P x S f i j)=
      (horizontalEdgeQ F (r.xIndex x).val S.half (r.fIndex f.1).val i.val j.val).1 := by
  have hm : S.half≠0 := Nat.ne_of_gt S.half_pos
  by_cases hj0 : j.val=0 <;> by_cases hjm : j.val=S.half
  all_goals simp only [subdivisionHorizontalEdge,horizontalEdgeQ,encodeSubEdge,
    encodeStarEdge,xStarFaceXQEdge,xStarFaceQZEdge,faceXQEdge,faceQZEdge,
    hj0,hjm,hm,r.face_q0,r.face_q1,r.face_z,ite_true,ite_false]
  all_goals rfl
theorem encode_verticalEdge {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (x : P.X) (S : OddScale) (f : XStarFace P x)
    (i : Fin (S.half+1)) (j : Fin S.half) :
    encodeSubEdge r x S (subdivisionVerticalEdge P x S f i j)=
      (verticalEdgeQ F (r.xIndex x).val S.half (r.fIndex f.1).val i.val j.val).1 := by
  have hm : S.half≠0 := Nat.ne_of_gt S.half_pos
  by_cases hi0 : i.val=0 <;> by_cases him : i.val=S.half
  all_goals simp only [subdivisionVerticalEdge,verticalEdgeQ,encodeSubEdge,
    encodeStarEdge,xStarFaceXQEdge,xStarFaceQZEdge,faceXQEdge,faceQZEdge,
    hi0,him,hm,r.face_q0,r.face_q1,r.face_z,ite_true,ite_false]
  all_goals rfl
theorem encode_qEdge_start {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (q : P.Q) (S : OddScale) (e : QDoubleCylinderEdge P q S) :
    {encodeQVertex r q S (qDoubleCylinderEdgeStart P q S e) with family:=1}=
      (qDoubleEdgeVertexQ S.half (encodeQEdge r q S e) 0).1 := by
  cases e with
  | inl e =>
      rcases e with ⟨c,z,i⟩
      have him : i.val≠S.half := Nat.ne_of_lt i.isLt
      by_cases hi : i.val=0
      all_goals simp [qDoubleCylinderEdgeStart,qSubdivisionEdgeStart,qStarEdgeStart,
        encodeQVertex,encodeQEdge,qDoubleEdgeVertexQ,hi,him]
  | inr z =>
      simp [qDoubleCylinderEdgeStart,qStarEdgeEnd,encodeQVertex,encodeQEdge,qDoubleEdgeVertexQ]
theorem encode_qEdge_end {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (q : P.Q) (S : OddScale) (e : QDoubleCylinderEdge P q S) :
    {encodeQVertex r q S (qDoubleCylinderEdgeEnd P q S e) with family:=1}=
      (qDoubleEdgeVertexQ S.half (encodeQEdge r q S e) 1).1 := by
  cases e with
  | inl e =>
      rcases e with ⟨c,z,i⟩
      have hp : i.val+1≠0 := by omega
      have hm : S.half≠0 := Nat.ne_of_gt S.half_pos
      by_cases hi : i.val+1=S.half
      all_goals simp [qDoubleCylinderEdgeEnd,qSubdivisionEdgeEnd,qStarEdgeEnd,
        encodeQVertex,encodeQEdge,qDoubleEdgeVertexQ,hi,hp,hm]
  | inr z =>
      simp [qDoubleCylinderEdgeEnd,qStarEdgeEnd,encodeQVertex,encodeQEdge,qDoubleEdgeVertexQ]
theorem index_val_eq {A : Type*} {n : ℕ} (e : A ≃ Fin n) (a b : A) :
    (e a).val=(e b).val ↔ a=b :=
  ⟨fun h => e.injective (Fin.ext h),fun h => congrArg (fun x => (e x).val) h⟩
theorem faceAtQ_option (fs : List FaceRow) (i : ℕ) :
    (faceAtQ fs i).1=fs[i]?.getD ⟨{},0,0,0,0⟩ := by
  induction fs generalizing i with
  | nil => rfl
  | cons f fs ih => cases i <;> simp [faceAtQ,ih]
theorem face_scan_iff {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (p : FaceRow → Prop) :
    (∃ row∈F.faces,p row) ↔ ∃f : P.Face,p (faceAtQ F.faces (r.fIndex f).val).1 := by
  constructor
  · rintro ⟨row,hr,hp⟩
    obtain ⟨f,hf⟩ := faceRows_exhaustive F P r row hr
    exact ⟨f,hf.symm ▸ hp⟩
  · rintro ⟨f,hf⟩
    exact ⟨_,faceAtQ_mem F P r f,hf⟩
theorem starQs_actual {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (A : TannerSquareAdmissible P) (x : P.X) (q : P.Q) :
    (r.qIndex q).val∈(starQsQ F (r.xIndex x).val).1 ↔ P.xq x q=true := by
  simp only [starQsQ,filterQ_value,rangeQ_value,List.mem_filter,List.mem_range]
  rw [refines_xq r A]
  simp [(r.qIndex q).isLt]
theorem starZs_actual {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (x : P.X) (z : P.Z) :
    (r.zIndex z).val∈(starZsQ F (r.xIndex x).val).1 ↔
      ∃f : P.Face,P.faceX f=x ∧ P.faceZ f=z := by
  simp only [starZsQ,filterQ_value,rangeQ_value,List.mem_filter,List.mem_range,anyQ_exists]
  simp only [(r.zIndex z).isLt,true_and,decide_eq_true_eq]
  rw [face_scan_iff r]
  simp only [r.face_x,r.face_z,index_val_eq]
theorem productQ_mem {A B : Type*} (as : List A) (bs : List B) (a : A) (b : B) :
    (a,b)∈(productQ as bs).1 ↔ a∈as ∧ b∈bs := by
  simp only [productQ_value,List.mem_flatMap,List.mem_map,Prod.mk.injEq]
  aesop
theorem starSides_actual {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (x : P.X) (q : P.Q) (z : P.Z) :
    ((r.qIndex q).val,(r.zIndex z).val)∈(starSidesQ F (r.xIndex x).val).1 ↔
      ∃f : P.Face,P.faceX f=x ∧ P.faceZ f=z ∧ (P.faceQ f 0=q ∨ P.faceQ f 1=q) := by
  simp only [starSidesQ,filterQ_value,List.mem_filter,productQ_mem,
    rangeQ_value,List.mem_range,anyQ_exists,decide_eq_true_eq]
  simp only [(r.qIndex q).isLt,(r.zIndex z).isLt,true_and]
  rw [face_scan_iff r]
  simp only [r.face_x,r.face_z,r.face_q0,r.face_q1,index_val_eq]
theorem mapQ_length {A B : Type*} (f : A → Query B) (as : List A) :
    (mapQ f as).1.length=as.length := by simp [mapQ_value]
theorem loopQ_value {A : Type*} (n : ℕ) (f : ℕ → Query (List A)) :
    (loopQ n f).1=(List.range n).flatMap (fun i => (f i).1) := by
  simp [loopQ,rangeQ_value,flatMapQ_value]
def frameSize (F : Frame) : ℕ :=
  F.nx+F.nq+F.nz+F.nf+F.xs.length+F.qs.length+F.zs.length+F.faces.length+1
def radius (F : Frame) (m : ℕ) : ℕ := frameSize F+m+1
theorem collectQ_cons_value {A : Type*} (q : Query (List A))
    (qs : List (Query (List A))) :
    (collectQ (q::qs)).1 = q.1 ++ (collectQ qs).1 := rfl
theorem collectQ_nil_value {A : Type*} :
    (collectQ ([] : List (Query (List A)))).1 = [] := rfl
theorem loopQ_mem {A : Type*} (a : A) (n : ℕ) (f : ℕ → Query (List A)) :
    a∈(loopQ n f).1 ↔ ∃i< n,a∈(f i).1 := by
  simp [loopQ_value]
theorem mapCodesQ_mem (c : Code) (f : Code → Code) (xs : List Code) :
    c∈(mapCodesQ f xs).1 ↔ ∃a∈xs,f a=c := by simp [mapCodesQ,mapQ_value,emitQ]
theorem qNeighbors_actual {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (A : TannerSquareAdmissible P) (q : P.Q) (z : P.Z) :
    (r.zIndex z).val∈(qNeighborsQ F (r.qIndex q).val).1 ↔ P.qz q z=true := by
  simp only [qNeighborsQ,filterQ_value,rangeQ_value,List.mem_filter,List.mem_range]
  rw [refines_qz r A]
  simp [(r.zIndex z).isLt]
theorem qNeighbors_bounds (F : Frame) (q z : ℕ)
    (hz : z∈(qNeighborsQ F q).1) : z< F.nz := by
  simp only [qNeighborsQ,filterQ_value,rangeQ_value,List.mem_filter,List.mem_range] at hz
  exact hz.1
theorem finTwo_native (c : ℕ) (hc : c∈([0,1] : List ℕ)) : c<2 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  omega
theorem encodeQVertex_injective {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (q : P.Q) (S : OddScale) :
    Function.Injective (encodeQVertex r q S) := by
  rintro ⟨c,v⟩ ⟨d,w⟩ h
  have hc := congrArg Code.copy h
  have hp := congrArg Code.part h
  have hz := congrArg Code.p h
  have hi := congrArg Code.i h
  have hcd : c=d := Fin.ext hc
  subst d
  apply congrArg (fun u => (c,u))
  cases v with
  | inl v =>
      cases w with
      | inl w =>
          cases v with
          | inl v =>
              cases w with
              | inl w => cases v; cases w; rfl
              | inr w => simp [encodeQVertex] at hp
          | inr v =>
              cases w with
              | inl w => simp [encodeQVertex] at hp
              | inr w =>
                  have hvw : v=w := Subtype.ext (r.zIndex.injective (Fin.ext hz))
                  subst w; rfl
      | inr w => cases v <;> simp [encodeQVertex] at hp
  | inr v =>
      cases w with
      | inl w => cases w <;> simp [encodeQVertex] at hp
      | inr w =>
          have hvw : v.1=w.1 := Subtype.ext (r.zIndex.injective (Fin.ext hz))
          have hiv : v.2=w.2 := Fin.ext hi
          cases v; cases w; cases hvw; cases hiv; rfl
theorem encodeQEdge_injective {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (q : P.Q) (S : OddScale) :
    Function.Injective (encodeQEdge r q S) := by
  intro e f h
  have hc := congrArg Code.copy h
  have hp := congrArg Code.part h
  have hz := congrArg Code.p h
  have hi := congrArg Code.i h
  cases e with
  | inl e =>
      cases f with
      | inr f => simp [encodeQEdge] at hp
      | inl f =>
          have hcopy : e.1=f.1 := Fin.ext hc
          have hneighbor : e.2.1=f.2.1 := Subtype.ext (r.zIndex.injective (Fin.ext hz))
          have hsegment : e.2.2=f.2.2 := Fin.ext hi
          rcases e with ⟨e,e',i⟩; rcases f with ⟨f,f',j⟩
          cases hcopy; cases hneighbor; cases hsegment; rfl
  | inr e =>
      cases f with
      | inl f => simp [encodeQEdge] at hp
      | inr f =>
          have hef : e=f := Subtype.ext (r.zIndex.injective (Fin.ext hz))
          subst f; rfl
theorem qDoubleVertices_mem (F : Frame) (q m : ℕ) (c : Code) :
    c∈(qDoubleVerticesQ F q m).1 ↔ ∃d∈([0,1] : List ℕ),
      c={owner:=q,copy:=d} ∨
      (∃z∈(qNeighborsQ F q).1,c={owner:=q,copy:=d,part:=1,p:=z}) ∨
      (∃z∈(qNeighborsQ F q).1,∃i< m-1,c={owner:=q,copy:=d,part:=2,p:=z,i:=i}) := by
  simp only [qDoubleVerticesQ,collectQ_cons_value,collectQ_nil_value,flatMapQ_value,mapQ_value,mapCodesQ,
    singletonQ,emitQ,loopQ_value,List.mem_flatMap,List.mem_map,List.mem_append,
    List.mem_cons,List.not_mem_nil,List.mem_range,List.mem_singleton,or_false]
  aesop
theorem qDoubleEdges_mem (F : Frame) (q m : ℕ) (c : Code) :
    c∈(qDoubleEdgesQ F q m).1 ↔
      (∃d∈([0,1] : List ℕ),∃z∈(qNeighborsQ F q).1,∃i< m,
        c={owner:=q,copy:=d,p:=z,i:=i}) ∨
      (∃z∈(qNeighborsQ F q).1,c={owner:=q,part:=1,p:=z}) := by
  simp only [qDoubleEdgesQ,collectQ_cons_value,collectQ_nil_value,flatMapQ_value,mapQ_value,singletonQ,
    emitQ,loopQ_value,List.mem_flatMap,List.mem_map,List.mem_append,
    List.mem_cons,List.not_mem_nil,List.mem_range,List.mem_singleton,or_false]
  aesop
theorem qDoubleVertices_cover {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (A : TannerSquareAdmissible P) (q : P.Q) (S : OddScale) (c : Code) :
    c∈(qDoubleVerticesQ F (r.qIndex q).val S.half).1 ↔
      ∃v : QDoubleCylinderVertex P q S,encodeQVertex r q S v=c := by
  rw [qDoubleVertices_mem]
  constructor
  · rintro ⟨d,hd,hc⟩
    let copy : Two := ⟨d,finTwo_native d hd⟩
    rcases hc with hc|hc|hc
    · refine ⟨(copy,Sum.inl (Sum.inl ())),?_⟩
      simpa only [encodeQVertex,copy] using hc.symm
    · obtain ⟨z,hz,hc⟩ := hc
      let zi : Fin F.nz := ⟨z,qNeighbors_bounds F _ z hz⟩
      let old := r.zIndex.symm zi
      have hm : (r.zIndex old).val=z := by simp [old,zi]
      have hqz : P.qz q old=true := (qNeighbors_actual r A q old).mp (hm.symm ▸ hz)
      refine ⟨(copy,Sum.inl (Sum.inr ⟨old,hqz⟩)),?_⟩
      simpa only [encodeQVertex,copy,hm] using hc.symm
    · obtain ⟨z,hz,i,hi,hc⟩ := hc
      let zi : Fin F.nz := ⟨z,qNeighbors_bounds F _ z hz⟩
      let old := r.zIndex.symm zi
      have hm : (r.zIndex old).val=z := by simp [old,zi]
      have hqz : P.qz q old=true := (qNeighbors_actual r A q old).mp (hm.symm ▸ hz)
      refine ⟨(copy,Sum.inr (⟨old,hqz⟩,⟨i,hi⟩)),?_⟩
      simpa only [encodeQVertex,copy,hm] using hc.symm
  · rintro ⟨⟨d,v⟩,rfl⟩
    have hd : d.val∈([0,1] : List ℕ) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false]
      have := d.isLt
      omega
    refine ⟨d.val,hd,?_⟩
    cases v with
    | inl v =>
        cases v with
        | inl v => cases v; exact Or.inl rfl
        | inr z => exact Or.inr (Or.inl ⟨_,(qNeighbors_actual r A q z.1).mpr z.2,rfl⟩)
    | inr zi =>
        exact Or.inr (Or.inr ⟨_,(qNeighbors_actual r A q zi.1.1).mpr zi.1.2,
          zi.2.val,zi.2.isLt,rfl⟩)
theorem qDoubleEdges_cover {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (A : TannerSquareAdmissible P) (q : P.Q) (S : OddScale) (c : Code) :
    c∈(qDoubleEdgesQ F (r.qIndex q).val S.half).1 ↔
      ∃e : QDoubleCylinderEdge P q S,encodeQEdge r q S e=c := by
  rw [qDoubleEdges_mem]
  constructor
  · intro hc
    rcases hc with hc|hc
    · obtain ⟨d,hd,z,hz,i,hi,hc⟩ := hc
      let copy : Two := ⟨d,finTwo_native d hd⟩
      let zi : Fin F.nz := ⟨z,qNeighbors_bounds F _ z hz⟩
      let old := r.zIndex.symm zi
      have hm : (r.zIndex old).val=z := by simp [old,zi]
      have hqz : P.qz q old=true := (qNeighbors_actual r A q old).mp (hm.symm ▸ hz)
      refine ⟨Sum.inl (copy,(⟨old,hqz⟩,⟨i,hi⟩)),?_⟩
      simpa only [encodeQEdge,copy,hm] using hc.symm
    · obtain ⟨z,hz,hc⟩ := hc
      let zi : Fin F.nz := ⟨z,qNeighbors_bounds F _ z hz⟩
      let old := r.zIndex.symm zi
      have hm : (r.zIndex old).val=z := by simp [old,zi]
      have hqz : P.qz q old=true := (qNeighbors_actual r A q old).mp (hm.symm ▸ hz)
      refine ⟨Sum.inr ⟨old,hqz⟩,?_⟩
      simpa only [encodeQEdge,hm] using hc.symm
  · rintro ⟨e,rfl⟩
    cases e with
    | inl e =>
        rcases e with ⟨d,z,i⟩
        have hd : d.val∈([0,1] : List ℕ) := by
          simp only [List.mem_cons,List.not_mem_nil,or_false]
          have := d.isLt
          omega
        exact Or.inl ⟨d.val,hd,_,(qNeighbors_actual r A q z.1).mpr z.2,i.val,i.isLt,rfl⟩
    | inr z => exact Or.inr ⟨_,(qNeighbors_actual r A q z.1).mpr z.2,rfl⟩
theorem facesAtX_mem {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (x : P.X) (f : P.Face) :
    ((r.fIndex f).val,(faceAtQ F.faces (r.fIndex f).val).1)∈
      (facesAtXQ F (r.xIndex x).val).1 ↔ P.faceX f=x := by
  simp only [facesAtXQ,filterQ_value,mapQ_value,rangeQ_value,List.mem_filter,
    List.mem_map,List.mem_range,Prod.mk.injEq,decide_eq_true_eq]
  simp only [←faceAtQ_option]
  simp [r.face_x,index_val_eq,(r.fIndex f).isLt]
theorem facesAtX_cover {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (x : P.X) (a : ℕ × FaceRow) :
    a∈(facesAtXQ F (r.xIndex x).val).1 ↔
      ∃f : XStarFace P x,a=((r.fIndex f.1).val,(faceAtQ F.faces (r.fIndex f.1).val).1) := by
  constructor
  · intro ha
    have hp := ha
    simp only [facesAtXQ,filterQ_value,mapQ_value,rangeQ_value,List.mem_filter,
      List.mem_map,List.mem_range,decide_eq_true_eq] at hp
    obtain ⟨⟨i,hi,hai⟩,hxa⟩ := hp
    let f := r.fIndex.symm ⟨i,hi⟩
    have hfi : (r.fIndex f).val=i := by simp [f]
    have hrow : (i,F.faces[i]?.getD ⟨{},0,0,0,0⟩)=
        ((r.fIndex f).val,(faceAtQ F.faces (r.fIndex f).val).1) := by
      rw [hfi,faceAtQ_option]
    have hcoord := congrArg (fun row : ℕ × FaceRow => row.2.x) (hai.symm.trans hrow)
    have hx : P.faceX f=x := by
      apply (index_val_eq r.xIndex (P.faceX f) x).mp
      calc
        (r.xIndex (P.faceX f)).val=(faceAtQ F.faces (r.fIndex f).val).1.x := (r.face_x f).symm
        _ = a.2.x := hcoord.symm
        _ = (r.xIndex x).val := hxa
    exact ⟨⟨f,by simpa [xStarFaceMember] using hx⟩,hai.symm.trans hrow⟩
  · rintro ⟨f,rfl⟩
    exact (facesAtX_mem r x f.1).mpr (by simpa [xStarFaceMember] using f.2)
theorem starRadial_iff (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (x : P.X) (e : XQEdge P) :
    xStarEdgeMember P x (.inl e)=true ↔ e.1.1=x := by
  change (decide (∃ f : P.Face,decide (P.faceX f=x)=true ∧
    decide (e=faceXQEdge P f 0 ∨ e=faceXQEdge P f 1)=true)=true) ↔ _
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨f,hf,he|he⟩ <;>
      exact (congrArg (fun a : XQEdge P => a.1.1) he).trans hf
  · intro he
    obtain ⟨f,c,hx,hq⟩ := (actual_xq_iff_face P A x e.1.2).mp (he ▸ e.2)
    refine ⟨f,hx,?_⟩
    have eqe : e=faceXQEdge P f c := by
      apply Subtype.ext
      exact Prod.ext (he.trans hx.symm) hq.symm
    fin_cases c <;> simp_all
theorem starSide_iff (P : TannerSquarePresentation) (x : P.X) (e : QZEdge P) :
    xStarEdgeMember P x (.inr e)=true ↔
      ∃f : P.Face,P.faceX f=x ∧ P.faceZ f=e.1.2 ∧
        (P.faceQ f 0=e.1.1 ∨ P.faceQ f 1=e.1.1) := by
  change (decide (∃ f : P.Face,decide (P.faceX f=x)=true ∧
    decide (e=faceQZEdge P f 0 ∨ e=faceQZEdge P f 1)=true)=true) ↔ _
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨f,hx,he|he⟩
    · exact ⟨f,hx,(congrArg (fun a : QZEdge P => a.1.2) he).symm,
        Or.inl (congrArg (fun a : QZEdge P => a.1.1) he).symm⟩
    · exact ⟨f,hx,(congrArg (fun a : QZEdge P => a.1.2) he).symm,
        Or.inr (congrArg (fun a : QZEdge P => a.1.1) he).symm⟩
  · rintro ⟨f,hx,hz,hq|hq⟩
    · exact ⟨f,hx,Or.inl (Subtype.ext (Prod.ext hq.symm hz.symm))⟩
    · exact ⟨f,hx,Or.inr (Subtype.ext (Prod.ext hq.symm hz.symm))⟩
theorem starQ_iff (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (q : P.Q) : xStarVertexMember P x (.q q)=true ↔ P.xq x q=true := by
  change (decide (∃f : P.Face,decide (P.faceX f=x)=true ∧
    (q=P.faceQ f 0 ∨ q=P.faceQ f 1))=true) ↔ _
  rw [decide_eq_true_eq,actual_xq_iff_face P A]
  constructor
  · rintro ⟨f,hf,hq|hq⟩
    · exact ⟨f,0,by simpa using hf,hq.symm⟩
    · exact ⟨f,1,by simpa using hf,hq.symm⟩
  · rintro ⟨f,c,hx,hq⟩
    refine ⟨f,by simpa using hx,?_⟩
    fin_cases c <;> simp_all
theorem starZ_iff (P : TannerSquarePresentation) (x : P.X) (z : P.Z) :
    xStarVertexMember P x (.z z)=true ↔ ∃f : P.Face,P.faceX f=x ∧ P.faceZ f=z := by
  simp only [xStarVertexMember,decide_eq_true_eq,xStarFaceMember]
  aesop
theorem subVertices_mem (F : Frame) (x m : ℕ) (c : Code) :
    c∈(subVerticesQ F x m).1 ↔ c={owner:=x} ∨
      (∃q∈(starQsQ F x).1,c={owner:=x,part:=1,p:=q}) ∨
      (∃z∈(starZsQ F x).1,c={owner:=x,part:=2,p:=z}) ∨
      (∃q∈(starQsQ F x).1,∃i< m-1,c={owner:=x,part:=3,p:=q,i:=i}) ∨
      (∃e∈(starSidesQ F x).1,∃i< m-1,c={owner:=x,part:=4,p:=e.1,q:=e.2,i:=i}) ∨
      (∃f∈(facesAtXQ F x).1,∃i< m-1,∃j< m-1,c={owner:=x,part:=5,p:=f.1,i:=i,j:=j}) := by
  simp only [subVerticesQ,collectQ_cons_value,collectQ_nil_value,List.mem_append,List.not_mem_nil,or_false,
    mapQ_value,List.mem_map,flatMapQ_value,List.mem_flatMap,loopQ_mem,
    singletonQ,emitQ,List.mem_singleton]
  aesop
theorem subEdges_mem (F : Frame) (x m : ℕ) (c : Code) :
    c∈(subEdgesQ F x m).1 ↔
      (∃q∈(starQsQ F x).1,∃i< m,c={owner:=x,p:=q,i:=i}) ∨
      (∃e∈(starSidesQ F x).1,∃i< m,c={owner:=x,part:=1,p:=e.1,q:=e.2,i:=i}) ∨
      (∃f∈(facesAtXQ F x).1,∃i< m,∃j< m-1,c={owner:=x,part:=2,p:=f.1,i:=i,j:=j}) ∨
      (∃f∈(facesAtXQ F x).1,∃i< m-1,∃j< m,c={owner:=x,part:=3,p:=f.1,i:=i,j:=j}) := by
  simp only [subEdgesQ,collectQ_cons_value,collectQ_nil_value,List.mem_append,List.not_mem_nil,or_false,
    flatMapQ_value,List.mem_flatMap,loopQ_mem,singletonQ,List.mem_singleton]
theorem subFaces_mem (F : Frame) (x m : ℕ) (c : Code) :
    c∈(subFacesQ F x m).1 ↔ ∃f∈(facesAtXQ F x).1,∃i< m,∃j< m,
      c={owner:=x,p:=f.1,i:=i,j:=j} := by
  simp only [subFacesQ,flatMapQ_value,List.mem_flatMap,loopQ_mem,singletonQ,
    List.mem_singleton]
theorem starQs_bound (F : Frame) (x q : ℕ) (hq : q∈(starQsQ F x).1) : q< F.nq := by
  simp only [starQsQ,filterQ_value,rangeQ_value,List.mem_filter,List.mem_range] at hq
  exact hq.1
theorem starZs_bound (F : Frame) (x z : ℕ) (hz : z∈(starZsQ F x).1) : z< F.nz := by
  simp only [starZsQ,filterQ_value,rangeQ_value,List.mem_filter,List.mem_range] at hz
  exact hz.1
theorem starSides_bound (F : Frame) (x : ℕ) (e : ℕ×ℕ)
    (he : e∈(starSidesQ F x).1) : e.1< F.nq ∧ e.2< F.nz := by
  simp only [starSidesQ,filterQ_value,List.mem_filter] at he
  have h := (productQ_mem _ _ _ _).mp he.1
  simpa only [rangeQ_value,List.mem_range] using h
theorem subVertices_cover {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (A : TannerSquareAdmissible P) (x : P.X) (S : OddScale) (c : Code) :
    c∈(subVerticesQ F (r.xIndex x).val S.half).1 ↔
      ∃v : SubdivisionVertex P x S,encodeSubVertex r x S v=c := by
  rw [subVertices_mem]
  constructor
  · intro hc
    rcases hc with hc|hc|hc|hc|hc|hc
    · refine ⟨.inl ⟨.x x,by simp [xStarVertexMember]⟩,hc.symm⟩
    · obtain ⟨q,hq,hc⟩ := hc
      let old := r.qIndex.symm ⟨q,starQs_bound F _ q hq⟩
      have hi : (r.qIndex old).val=q := by simp [old]
      have hxq : P.xq x old=true := (starQs_actual r A x old).mp (hi.symm ▸ hq)
      refine ⟨.inl ⟨.q old,(starQ_iff P A x old).mpr hxq⟩,?_⟩
      simpa only [encodeSubVertex,encodeStarVertex,hi] using hc.symm
    · obtain ⟨z,hz,hc⟩ := hc
      let old := r.zIndex.symm ⟨z,starZs_bound F _ z hz⟩
      have hi : (r.zIndex old).val=z := by simp [old]
      have hxz := (starZs_actual r x old).mp (hi.symm ▸ hz)
      refine ⟨.inl ⟨.z old,(starZ_iff P x old).mpr hxz⟩,?_⟩
      simpa only [encodeSubVertex,encodeStarVertex,hi] using hc.symm
    · obtain ⟨q,hq,i,hi,hc⟩ := hc
      let old := r.qIndex.symm ⟨q,starQs_bound F _ q hq⟩
      have hqi : (r.qIndex old).val=q := by simp [old]
      have hxq : P.xq x old=true := (starQs_actual r A x old).mp (hqi.symm ▸ hq)
      let edge : XQEdge P := ⟨(x,old),hxq⟩
      let star : XStarEdge P x := ⟨.inl edge,(starRadial_iff P A x edge).mpr rfl⟩
      refine ⟨.inr (.inl (star,⟨i,hi⟩)),?_⟩
      simpa only [encodeSubVertex,encodeStarEdge,star,edge,hqi,ite_true] using hc.symm
    · obtain ⟨e,he,i,hi,hc⟩ := hc
      obtain ⟨hq,hz⟩ := starSides_bound F _ e he
      let q := r.qIndex.symm ⟨e.1,hq⟩
      let z := r.zIndex.symm ⟨e.2,hz⟩
      have hqi : (r.qIndex q).val=e.1 := by simp [q]
      have hzi : (r.zIndex z).val=e.2 := by simp [z]
      have hface := (starSides_actual r x q z).mp (by simpa only [hqi,hzi] using he)
      obtain ⟨f,hfx,hfz,hfq⟩ := hface
      have hqz : P.qz q z=true := by
        rcases hfq with hfq|hfq
        · simpa [←hfq,←hfz] using P.data.faceQ_qz f 0
        · simpa [←hfq,←hfz] using P.data.faceQ_qz f 1
      let edge : QZEdge P := ⟨(q,z),hqz⟩
      let star : XStarEdge P x := ⟨.inr edge,(starSide_iff P x edge).mpr ⟨f,hfx,hfz,hfq⟩⟩
      refine ⟨.inr (.inl (star,⟨i,hi⟩)),?_⟩
      simpa only [encodeSubVertex,encodeStarEdge,star,edge,hqi,hzi,ite_false,Nat.one_ne_zero] using hc.symm
    · obtain ⟨a,ha,i,hi,j,hj,hc⟩ := hc
      obtain ⟨f,hf⟩ := (facesAtX_cover r x a).mp ha
      refine ⟨.inr (.inr (f,⟨i,hi⟩,⟨j,hj⟩)),?_⟩
      simpa only [encodeSubVertex,hf] using hc.symm
  · rintro ⟨v,rfl⟩
    cases v with
    | inl v =>
        rcases v with ⟨v,hv⟩
        cases v with
        | x y =>
            have hy : y=x := by simpa [xStarVertexMember] using hv
            subst y; exact Or.inl rfl
        | q q => exact Or.inr (Or.inl ⟨_,(starQs_actual r A x q).mpr ((starQ_iff P A x q).mp hv),rfl⟩)
        | z z => exact Or.inr (Or.inr (Or.inl ⟨_,(starZs_actual r x z).mpr ((starZ_iff P x z).mp hv),rfl⟩))
    | inr v =>
        cases v with
        | inl ei =>
            rcases ei with ⟨⟨e,he⟩,i⟩
            cases e with
            | inl e =>
                have hx := (starRadial_iff P A x e).mp he
                have hq := (starQs_actual r A x e.1.2).mpr (hx ▸ e.2)
                exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_,hq,i.val,i.isLt,rfl⟩)))
            | inr e =>
                have hs := (starSides_actual r x e.1.1 e.1.2).mpr ((starSide_iff P x e).mp he)
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_,hs,i.val,i.isLt,rfl⟩))))
        | inr f =>
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_,
              (facesAtX_cover r x _).mpr ⟨f.1,rfl⟩,f.2.1.val,f.2.1.isLt,
              f.2.2.val,f.2.2.isLt,rfl⟩))))
theorem subEdges_cover {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (A : TannerSquareAdmissible P) (x : P.X) (S : OddScale) (c : Code) :
    c∈(subEdgesQ F (r.xIndex x).val S.half).1 ↔
      ∃e : SubdivisionEdge P x S,encodeSubEdge r x S e=c := by
  rw [subEdges_mem]
  constructor
  · intro hc
    rcases hc with hc|hc|hc|hc
    · obtain ⟨q,hq,i,hi,hc⟩ := hc
      let old := r.qIndex.symm ⟨q,starQs_bound F _ q hq⟩
      have hqi : (r.qIndex old).val=q := by simp [old]
      have hxq : P.xq x old=true := (starQs_actual r A x old).mp (hqi.symm ▸ hq)
      let edge : XQEdge P := ⟨(x,old),hxq⟩
      let star : XStarEdge P x := ⟨.inl edge,(starRadial_iff P A x edge).mpr rfl⟩
      refine ⟨.inl (star,⟨i,hi⟩),?_⟩
      simpa only [encodeSubEdge,encodeStarEdge,star,edge,hqi] using hc.symm
    · obtain ⟨e,he,i,hi,hc⟩ := hc
      obtain ⟨hq,hz⟩ := starSides_bound F _ e he
      let q := r.qIndex.symm ⟨e.1,hq⟩
      let z := r.zIndex.symm ⟨e.2,hz⟩
      have hqi : (r.qIndex q).val=e.1 := by simp [q]
      have hzi : (r.zIndex z).val=e.2 := by simp [z]
      obtain ⟨f,hfx,hfz,hfq⟩ := (starSides_actual r x q z).mp (by simpa only [hqi,hzi] using he)
      have hqz : P.qz q z=true := by
        rcases hfq with hfq|hfq
        · simpa [←hfq,←hfz] using P.data.faceQ_qz f 0
        · simpa [←hfq,←hfz] using P.data.faceQ_qz f 1
      let edge : QZEdge P := ⟨(q,z),hqz⟩
      let star : XStarEdge P x := ⟨.inr edge,(starSide_iff P x edge).mpr ⟨f,hfx,hfz,hfq⟩⟩
      refine ⟨.inl (star,⟨i,hi⟩),?_⟩
      simpa only [encodeSubEdge,encodeStarEdge,star,edge,hqi,hzi] using hc.symm
    · obtain ⟨a,ha,i,hi,j,hj,hc⟩ := hc
      obtain ⟨f,hf⟩ := (facesAtX_cover r x a).mp ha
      refine ⟨.inr (.inl (f,⟨i,hi⟩,⟨j,hj⟩)),?_⟩
      simpa only [encodeSubEdge,hf] using hc.symm
    · obtain ⟨a,ha,i,hi,j,hj,hc⟩ := hc
      obtain ⟨f,hf⟩ := (facesAtX_cover r x a).mp ha
      refine ⟨.inr (.inr (f,⟨i,hi⟩,⟨j,hj⟩)),?_⟩
      simpa only [encodeSubEdge,hf] using hc.symm
  · rintro ⟨v,rfl⟩
    cases v with
    | inl ei =>
        rcases ei with ⟨⟨e,he⟩,i⟩
        cases e with
        | inl e =>
            have hx := (starRadial_iff P A x e).mp he
            exact Or.inl ⟨_,(starQs_actual r A x e.1.2).mpr (hx ▸ e.2),i.val,i.isLt,rfl⟩
        | inr e =>
            exact Or.inr (Or.inl ⟨_,(starSides_actual r x e.1.1 e.1.2).mpr
              ((starSide_iff P x e).mp he),i.val,i.isLt,rfl⟩)
    | inr v =>
        cases v with
        | inl f => exact Or.inr (Or.inr (Or.inl ⟨_,(facesAtX_cover r x _).mpr ⟨f.1,rfl⟩,
            f.2.1.val,f.2.1.isLt,f.2.2.val,f.2.2.isLt,rfl⟩))
        | inr f => exact Or.inr (Or.inr (Or.inr ⟨_,(facesAtX_cover r x _).mpr ⟨f.1,rfl⟩,
            f.2.1.val,f.2.1.isLt,f.2.2.val,f.2.2.isLt,rfl⟩))
def encodeSubFace {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (x : P.X) (S : OddScale) (f : SubdivisionFace P x S) : Code :=
  {owner:=(r.xIndex x).val,p:=(r.fIndex f.1.1).val,i:=f.2.1.val,j:=f.2.2.val}
theorem subFaces_cover {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (x : P.X) (S : OddScale) (c : Code) :
    c∈(subFacesQ F (r.xIndex x).val S.half).1 ↔
      ∃f : SubdivisionFace P x S,encodeSubFace r x S f=c := by
  rw [subFaces_mem]
  constructor
  · rintro ⟨a,ha,i,hi,j,hj,hc⟩
    obtain ⟨f,hf⟩ := (facesAtX_cover r x a).mp ha
    refine ⟨(f,⟨i,hi⟩,⟨j,hj⟩),?_⟩
    simpa only [encodeSubFace,hf] using hc.symm
  · rintro ⟨f,rfl⟩
    exact ⟨_,(facesAtX_cover r x _).mpr ⟨f.1,rfl⟩,
      f.2.1.val,f.2.1.isLt,f.2.2.val,f.2.2.isLt,rfl⟩
theorem encodeStarVertex_injective {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (x : P.X) : Function.Injective (encodeStarVertex r x) := by
  rintro ⟨a,ha⟩ ⟨b,hb⟩ h
  apply Subtype.ext
  cases a with
  | x a =>
      cases b with
      | x b =>
          have hax : a=x := by simpa only [xStarVertexMember,decide_eq_true_eq] using ha
          have hbx : b=x := by simpa only [xStarVertexMember,decide_eq_true_eq] using hb
          exact congrArg Vertex.x (hax.trans hbx.symm)
      | q b => have hp := congrArg Code.part h; simp only [encodeStarVertex] at hp; omega
      | z b => have hp := congrArg Code.part h; simp only [encodeStarVertex] at hp; omega
  | q a =>
      cases b with
      | x b => have hp := congrArg Code.part h; simp only [encodeStarVertex] at hp; omega
      | q b => exact congrArg Vertex.q (r.qIndex.injective (Fin.ext (congrArg Code.p h)))
      | z b => have hp := congrArg Code.part h; simp only [encodeStarVertex] at hp; omega
  | z a =>
      cases b with
      | x b => have hp := congrArg Code.part h; simp only [encodeStarVertex] at hp; omega
      | q b => have hp := congrArg Code.part h; simp only [encodeStarVertex] at hp; omega
      | z b => exact congrArg Vertex.z (r.zIndex.injective (Fin.ext (congrArg Code.p h)))
theorem encodeSubVertex_injective {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (A : TannerSquareAdmissible P) (x : P.X) (S : OddScale) :
    Function.Injective (encodeSubVertex r x S) := by
  intro a b h
  have old (a b : XStarVertex P x) (he : encodeStarVertex r x a=encodeStarVertex r x b) :
      (Sum.inl a : SubdivisionVertex P x S)=Sum.inl b :=
    congrArg Sum.inl (encodeStarVertex_injective r x he)
  have hpart := congrArg Code.part h
  have hp := congrArg Code.p h
  have hq := congrArg Code.q h
  have hi := congrArg Code.i h
  have hj := congrArg Code.j h
  rcases a with ⟨a,ha⟩|⟨⟨a,ha⟩,ai⟩|⟨af,ai,aj⟩ <;>
    rcases b with ⟨b,hb⟩|⟨⟨b,hb⟩,bi⟩|⟨bf,bi,bj⟩
  all_goals try (simp only [encodeSubVertex] at hpart; contradiction)
  all_goals try (exact old _ _ h)
  all_goals try (cases a)
  all_goals try (cases b)
  all_goals simp only [encodeSubVertex,encodeStarVertex,encodeStarEdge,ite_true,
    ite_false,Nat.one_ne_zero] at hpart hp hq hi hj
  all_goals try omega
  all_goals try simp only [index_val_eq] at hp hq
  all_goals try (have := (starRadial_iff P A x _).mp ha)
  all_goals try (have := (starRadial_iff P A x _).mp hb)
  all_goals try (have hab_i : ai=bi := Fin.ext hi)
  all_goals try (have hab_j : aj=bj := Fin.ext hj)
  all_goals aesop (add safe apply [Subtype.ext, Fin.ext, Prod.ext])
theorem encodeSubEdge_injective {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (A : TannerSquareAdmissible P) (x : P.X) (S : OddScale) :
    Function.Injective (encodeSubEdge r x S) := by
  intro a b h
  have hpart := congrArg Code.part h
  have hp := congrArg Code.p h
  have hq := congrArg Code.q h
  have hi := congrArg Code.i h
  have hj := congrArg Code.j h
  rcases a with ⟨⟨a,ha⟩,ai⟩|⟨af,ai,aj⟩|⟨af,ai,aj⟩ <;>
    rcases b with ⟨⟨b,hb⟩,bi⟩|⟨bf,bi,bj⟩|⟨bf,bi,bj⟩
  all_goals try (cases a)
  all_goals try (cases b)
  all_goals simp only [encodeSubEdge,encodeStarEdge] at hpart hp hq hi hj
  all_goals try omega
  all_goals try simp only [index_val_eq] at hp hq
  all_goals try (have := (starRadial_iff P A x _).mp ha)
  all_goals try (have := (starRadial_iff P A x _).mp hb)
  all_goals try (have hab_i : ai=bi := Fin.ext hi)
  all_goals try (have hab_j : aj=bj := Fin.ext hj)
  all_goals aesop (add safe apply [Subtype.ext, Fin.ext, Prod.ext])
theorem encodeSubVertex_boundary {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (x : P.X) (S : OddScale) (v : SubdivisionVertex P x S) :
    subdivisionBoundaryVertexMember P x S v=true ↔
      (encodeSubVertex r x S v).part=1 ∨ (encodeSubVertex r x S v).part=2 ∨
        (encodeSubVertex r x S v).part=4 := by
  rcases v with ⟨v,hv⟩|⟨⟨e,he⟩,i⟩|f
  · cases v <;> simp [subdivisionBoundaryVertexMember,xStarBoundaryVertexMember,
      xStarVertexMember,encodeSubVertex,encodeStarVertex] at hv ⊢ <;> assumption
  · cases e <;> simp [subdivisionBoundaryVertexMember,xStarBoundaryEdgeMember,
      xStarEdgeMember,encodeSubVertex,encodeStarEdge] at he ⊢ <;> assumption
  · simp [subdivisionBoundaryVertexMember,encodeSubVertex]
theorem encodeSubEdge_boundary {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (x : P.X) (S : OddScale) (e : SubdivisionEdge P x S) :
    subdivisionBoundaryEdgeMember P x S e=true ↔ (encodeSubEdge r x S e).part=1 := by
  rcases e with ⟨⟨e,he⟩,i⟩|f|f
  · cases e <;> simp [subdivisionBoundaryEdgeMember,xStarBoundaryEdgeMember,
      xStarEdgeMember,encodeSubEdge,encodeStarEdge] at he ⊢ <;> assumption
  · simp [subdivisionBoundaryEdgeMember,encodeSubEdge]
  · simp [subdivisionBoundaryEdgeMember,encodeSubEdge]
theorem doubleVertices_cover {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (A : TannerSquareAdmissible P) (x : P.X) (S : OddScale) (c : Code) :
    c∈(doubleVerticesQ F (r.xIndex x).val S.half).1 ↔
      ∃v : DoubleCylinderVertex P x S,encodeDoubleVertex r x S v=c := by
  simp only [doubleVerticesQ,flatMapQ_value,List.mem_flatMap,mapCodesQ_mem]
  constructor
  · rintro ⟨d,hd,a,ha,hc⟩
    obtain ⟨v,hv⟩ := (subVertices_cover r A x S a).mp ha
    exact ⟨(⟨d,finTwo_native d hd⟩,v),by simpa [encodeDoubleVertex,hv] using hc⟩
  · rintro ⟨⟨d,v⟩,rfl⟩
    have hd : d.val∈([0,1] : List ℕ) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false]
      have := d.isLt; omega
    exact ⟨d.val,hd,encodeSubVertex r x S v,(subVertices_cover r A x S _).mpr ⟨v,rfl⟩,rfl⟩
theorem doubleEdges_cover {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (A : TannerSquareAdmissible P) (x : P.X) (S : OddScale) (c : Code) :
    c∈(doubleEdgesQ F (r.xIndex x).val S.half).1 ↔
      ∃e : DoubleCylinderEdge P x S,encodeDoubleEdge r x S e=c := by
  simp only [doubleEdgesQ,collectQ_cons_value,collectQ_nil_value,List.mem_append,List.not_mem_nil,or_false,
    flatMapQ_value,List.mem_flatMap,mapCodesQ_mem,filterQ_value,List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro (⟨d,hd,a,ha,hc⟩|⟨a,⟨ha,hb⟩,hc⟩)
    · obtain ⟨e,he⟩ := (subEdges_cover r A x S a).mp ha
      exact ⟨.inl (⟨d,finTwo_native d hd⟩,e),by simpa [encodeDoubleEdge,he] using hc⟩
    · obtain ⟨v,hv⟩ := (subVertices_cover r A x S a).mp ha
      have hb' := (encodeSubVertex_boundary r x S v).mpr (hv.symm ▸ hb)
      exact ⟨.inr ⟨v,hb'⟩,by simpa [encodeDoubleEdge,hv] using hc⟩
  · rintro ⟨e,rfl⟩
    cases e with
    | inl e =>
        have hd : e.1.val∈([0,1] : List ℕ) := by
          simp only [List.mem_cons,List.not_mem_nil,or_false]
          have := e.1.isLt; omega
        exact Or.inl ⟨e.1.val,hd,encodeSubEdge r x S e.2,
          (subEdges_cover r A x S _).mpr ⟨e.2,rfl⟩,rfl⟩
    | inr v => exact Or.inr ⟨encodeSubVertex r x S v.1,
        ⟨(subVertices_cover r A x S _).mpr ⟨v.1,rfl⟩,
          (encodeSubVertex_boundary r x S v.1).mp v.2⟩,rfl⟩
theorem doubleFaces_cover {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (A : TannerSquareAdmissible P) (x : P.X) (S : OddScale) (c : Code) :
    c∈(doubleFacesQ F (r.xIndex x).val S.half).1 ↔
      ∃f : DoubleCylinderFace P x S,encodeDoubleFace r x S f=c := by
  simp only [doubleFacesQ,collectQ_cons_value,collectQ_nil_value,List.mem_append,List.not_mem_nil,or_false,
    flatMapQ_value,List.mem_flatMap,mapCodesQ_mem,loopQ_mem,singletonQ,List.mem_singleton]
  constructor
  · rintro (⟨d,hd,a,ha,hc⟩|⟨e,he,i,hi,hc⟩)
    · obtain ⟨f,hf⟩ := (subFaces_cover r x S a).mp ha
      refine ⟨.inl (⟨d,finTwo_native d hd⟩,f),?_⟩
      change {encodeSubFace r x S f with copy:=d}=c
      exact (congrArg (fun a : Code => {a with copy:=d}) hf).trans hc
    · obtain ⟨hq,hz⟩ := starSides_bound F _ e he
      let q := r.qIndex.symm ⟨e.1,hq⟩
      let z := r.zIndex.symm ⟨e.2,hz⟩
      have hqi : (r.qIndex q).val=e.1 := by simp [q]
      have hzi : (r.zIndex z).val=e.2 := by simp [z]
      obtain ⟨f,hfx,hfz,hfq⟩ := (starSides_actual r x q z).mp (by simpa [hqi,hzi] using he)
      have hqz : P.qz q z=true := by
        rcases hfq with hfq|hfq
        · simpa [←hfq,←hfz] using P.data.faceQ_qz f 0
        · simpa [←hfq,←hfz] using P.data.faceQ_qz f 1
      let edge : QZEdge P := ⟨(q,z),hqz⟩
      let star : XStarEdge P x := ⟨.inr edge,(starSide_iff P x edge).mpr ⟨f,hfx,hfz,hfq⟩⟩
      let sub : SubdivisionEdge P x S := .inl (star,⟨i,hi⟩)
      have hb : subdivisionBoundaryEdgeMember P x S sub=true := by
        simpa [sub,encodeSubEdge,encodeStarEdge] using
          (encodeSubEdge_boundary r x S sub).mpr (by rfl)
      exact ⟨.inr ⟨sub,hb⟩,by simpa only [encodeDoubleFace,sub,encodeSubEdge,star,encodeStarEdge,edge,hqi,hzi] using hc.symm⟩
  · rintro ⟨f,rfl⟩
    cases f with
    | inl f =>
        have hd : f.1.val∈([0,1] : List ℕ) := by
          simp only [List.mem_cons,List.not_mem_nil,or_false]
          have := f.1.isLt; omega
        exact Or.inl ⟨f.1.val,hd,encodeSubFace r x S f.2,
          (subFaces_cover r x S _).mpr ⟨f.2,rfl⟩,rfl⟩
    | inr f =>
        rcases f with ⟨e,he⟩
        rcases e with ⟨⟨e,hstar⟩,i⟩|f|f
        · cases e with
          | inl e => simp [subdivisionBoundaryEdgeMember,xStarBoundaryEdgeMember] at he
          | inr e =>
              exact Or.inr ⟨_,(starSides_actual r x e.1.1 e.1.2).mpr
                ((starSide_iff P x e).mp hstar),i.val,i.isLt,rfl⟩
        · simp [subdivisionBoundaryEdgeMember] at he
        · simp [subdivisionBoundaryEdgeMember] at he
theorem encodeSubVertex_copy {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (x : P.X) (S : OddScale) (v : SubdivisionVertex P x S) :
    (encodeSubVertex r x S v).copy=0 := by
  rcases v with ⟨v,h⟩|⟨⟨e,h⟩,i⟩|f
  · cases v <;> rfl
  · cases e <;> rfl
  · rfl
theorem encodeSubEdge_copy {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (x : P.X) (S : OddScale) (e : SubdivisionEdge P x S) :
    (encodeSubEdge r x S e).copy=0 := by
  rcases e with ⟨⟨e,h⟩,i⟩|f|f
  · cases e <;> rfl
  · rfl
  · rfl
theorem encodeSubEdge_part {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (x : P.X) (S : OddScale) (e : SubdivisionEdge P x S) :
    (encodeSubEdge r x S e).part<4 := by
  rcases e with ⟨⟨e,h⟩,i⟩|f|f
  · cases e <;> norm_num [encodeSubEdge,encodeStarEdge]
  · norm_num [encodeSubEdge]
  · norm_num [encodeSubEdge]
theorem encodeDouble_owner {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (x : P.X) (S : OddScale) :
    (∀v,(encodeDoubleVertex r x S v).owner=(r.xIndex x).val) ∧
    (∀e,(encodeDoubleEdge r x S e).owner=(r.xIndex x).val) ∧
    (∀f,(encodeDoubleFace r x S f).owner=(r.xIndex x).val) := by
  constructor
  · rintro ⟨c,v⟩
    rcases v with ⟨v,h⟩|⟨⟨e,h⟩,i⟩|f
    · cases v <;> rfl
    · cases e <;> rfl
    · rfl
  · constructor
    · rintro (⟨c,e⟩|⟨v,hv⟩)
      · rcases e with ⟨⟨e,h⟩,i⟩|f|f
        · cases e <;> rfl
        · rfl
        · rfl
      · rcases v with ⟨v,h⟩|⟨⟨e,h⟩,i⟩|f
        · cases v <;> rfl
        · cases e <;> rfl
        · rfl
    · rintro (⟨c,f⟩|⟨e,he⟩)
      · rfl
      · rcases e with ⟨⟨e,h⟩,i⟩|f|f
        · cases e <;> rfl
        · rfl
        · rfl
theorem encodeDoubleVertex_injective {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (A : TannerSquareAdmissible P) (x : P.X) (S : OddScale) :
    Function.Injective (encodeDoubleVertex r x S) := by
  rintro ⟨a,v⟩ ⟨b,w⟩ h
  have hab : a=b := Fin.ext (congrArg Code.copy h)
  have hvw := congrArg (fun c : Code => {c with copy:=0}) h
  have hv : {encodeSubVertex r x S v with copy:=0}=encodeSubVertex r x S v := by
    ext <;> simp [encodeSubVertex_copy]
  have hw : {encodeSubVertex r x S w with copy:=0}=encodeSubVertex r x S w := by
    ext <;> simp [encodeSubVertex_copy]
  change {encodeSubVertex r x S v with copy:=0}={encodeSubVertex r x S w with copy:=0} at hvw
  exact Prod.ext hab ((encodeSubVertex_injective r A x S) (hv.symm.trans (hvw.trans hw)))
theorem encodeDoubleEdge_injective {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (A : TannerSquareAdmissible P) (x : P.X) (S : OddScale) :
    Function.Injective (encodeDoubleEdge r x S) := by
  intro a b h
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          have hc : a.1=b.1 := Fin.ext (congrArg Code.copy h)
          have he := congrArg (fun c : Code => {c with copy:=0}) h
          have ha : {encodeSubEdge r x S a.2 with copy:=0}=encodeSubEdge r x S a.2 := by
            ext <;> simp [encodeSubEdge_copy]
          have hb : {encodeSubEdge r x S b.2 with copy:=0}=encodeSubEdge r x S b.2 := by
            ext <;> simp [encodeSubEdge_copy]
          exact congrArg Sum.inl (Prod.ext hc ((encodeSubEdge_injective r A x S)
            (ha.symm.trans (he.trans hb))))
      | inr b =>
          have hp := congrArg Code.part h
          have ha := encodeSubEdge_part r x S a.2
          have hb := (encodeSubVertex_boundary r x S b.1).mp b.2
          simp only [encodeDoubleEdge] at hp
          rcases hb with hb|hb|hb <;> simp [hb] at hp <;> omega
  | inr a =>
      cases b with
      | inl b =>
          have hp := congrArg Code.part h
          have hb := encodeSubEdge_part r x S b.2
          have ha := (encodeSubVertex_boundary r x S a.1).mp a.2
          simp only [encodeDoubleEdge] at hp
          rcases ha with ha|ha|ha <;> simp [ha] at hp <;> omega
      | inr b =>
          have ha := (encodeSubVertex_boundary r x S a.1).mp a.2
          have hb := (encodeSubVertex_boundary r x S b.1).mp b.2
          have he := congrArg (fun c : Code =>
            {c with part:=if c.part=4 then 1 else if c.part=5 then 2 else 4}) h
          have ea : (fun c : Code =>
              {c with part:=if c.part=4 then 1 else if c.part=5 then 2 else 4})
                (encodeDoubleEdge r x S (.inr a))=encodeSubVertex r x S a.1 := by
            rcases ha with ha|ha|ha <;> ext <;> simp [encodeDoubleEdge,ha]
          have eb : (fun c : Code =>
              {c with part:=if c.part=4 then 1 else if c.part=5 then 2 else 4})
                (encodeDoubleEdge r x S (.inr b))=encodeSubVertex r x S b.1 := by
            rcases hb with hb|hb|hb <;> ext <;> simp [encodeDoubleEdge,hb]
          exact congrArg Sum.inr (Subtype.ext ((encodeSubVertex_injective r A x S)
            (ea.symm.trans (he.trans eb))))
theorem encodeDoubleFace_injective {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (A : TannerSquareAdmissible P) (x : P.X) (S : OddScale) :
    Function.Injective (encodeDoubleFace r x S) := by
  intro a b h
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          have hc := congrArg Code.copy h
          have hf := congrArg Code.p h
          have hi := congrArg Code.i h
          have hj := congrArg Code.j h
          simp only [encodeDoubleFace,index_val_eq] at hf
          exact congrArg Sum.inl (Prod.ext (Fin.ext hc)
            (Prod.ext (Subtype.ext hf) (Prod.ext (Fin.ext hi) (Fin.ext hj))))
      | inr b =>
          have hb := (encodeSubEdge_boundary r x S b.1).mp b.2
          have hp := congrArg Code.part h
          change 0=(encodeSubEdge r x S b.1).part at hp
          omega
  | inr a =>
      cases b with
      | inl b =>
          have ha := (encodeSubEdge_boundary r x S a.1).mp a.2
          have hp := congrArg Code.part h
          change (encodeSubEdge r x S a.1).part=0 at hp
          omega
      | inr b =>
          exact congrArg Sum.inr (Subtype.ext ((encodeSubEdge_injective r A x S) h))
theorem rxXCodes_cover {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (A : TannerSquareAdmissible P) (S : OddScale) (c : Code) :
    c∈(rxXCodesQ F S.half).1 ↔ ∃x : RX0 P S,encodeRX0 r S x=c := by
  rw [rxXCodesQ,loopQ_mem]
  constructor
  · rintro ⟨i,hi,hc⟩
    let x := r.xIndex.symm ⟨i,hi⟩
    have hx : (r.xIndex x).val=i := by simp [x]
    obtain ⟨v,hv⟩ := (doubleVertices_cover r A x S c).mp (hx.symm ▸ hc)
    exact ⟨⟨x,v⟩,hv⟩
  · rintro ⟨⟨x,v⟩,rfl⟩
    exact ⟨(r.xIndex x).val,(r.xIndex x).isLt,
      (doubleVertices_cover r A x S _).mpr ⟨v,rfl⟩⟩
theorem rxQCodes_cover {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (A : TannerSquareAdmissible P) (S : OddScale) (c : Code) :
    c∈(rxQCodesQ F S.half).1 ↔ ∃q : RX1 P S,encodeRX1 r S q=c := by
  simp only [rxQCodesQ,collectQ_cons_value,collectQ_nil_value,List.mem_append,List.not_mem_nil,or_false,loopQ_mem,mapCodesQ_mem]
  constructor
  · rintro (⟨i,hi,hc⟩|⟨i,hi,a,ha,hc⟩)
    · let x := r.xIndex.symm ⟨i,hi⟩
      have hx : (r.xIndex x).val=i := by simp [x]
      obtain ⟨e,he⟩ := (doubleEdges_cover r A x S c).mp (hx.symm ▸ hc)
      exact ⟨.inl ⟨x,e⟩,he⟩
    · let q := r.qIndex.symm ⟨i,hi⟩
      have hq : (r.qIndex q).val=i := by simp [q]
      obtain ⟨v,hv⟩ := (qDoubleVertices_cover r A q S a).mp (hq.symm ▸ ha)
      exact ⟨.inr ⟨q,v⟩,by simpa [encodeRX1,hv] using hc⟩
  · rintro ⟨q,rfl⟩
    cases q with
    | inl e => exact Or.inl ⟨_,(r.xIndex e.1).isLt,
        (doubleEdges_cover r A e.1 S _).mpr ⟨e.2,rfl⟩⟩
    | inr v => exact Or.inr ⟨_,(r.qIndex v.1).isLt,_,
        (qDoubleVertices_cover r A v.1 S _).mpr ⟨v.2,rfl⟩,rfl⟩
theorem rxZCodes_cover {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (A : TannerSquareAdmissible P) (S : OddScale) (c : Code) :
    c∈(rxZCodesQ F S.half).1 ↔ ∃z : RX2 P S,encodeRX2 r S z=c := by
  simp only [rxZCodesQ,collectQ_cons_value,collectQ_nil_value,List.mem_append,List.not_mem_nil,or_false,
    loopQ_mem,mapCodesQ_mem,mapQ_value,List.mem_map,emitQ]
  constructor
  · rintro (⟨i,hi,hc⟩|⟨i,hi,a,ha,hc⟩|⟨i,hi,d,hd,hc⟩)
    · let x := r.xIndex.symm ⟨i,hi⟩
      have hx : (r.xIndex x).val=i := by simp [x]
      obtain ⟨f,hf⟩ := (doubleFaces_cover r A x S c).mp (hx.symm ▸ hc)
      exact ⟨.inl (.inl ⟨x,f⟩),hf⟩
    · let q := r.qIndex.symm ⟨i,hi⟩
      have hq : (r.qIndex q).val=i := by simp [q]
      obtain ⟨e,he⟩ := (qDoubleEdges_cover r A q S a).mp (hq.symm ▸ ha)
      exact ⟨.inl (.inr ⟨q,e⟩),by simpa [encodeRX2,he] using hc⟩
    · let z := r.zIndex.symm ⟨i,hi⟩
      refine ⟨.inr (z,⟨d,finTwo_native d hd⟩),?_⟩
      simpa [encodeRX2,z,emitQ] using hc
  · rintro ⟨z,rfl⟩
    cases z with
    | inl z =>
        cases z with
        | inl f => exact Or.inl ⟨_,(r.xIndex f.1).isLt,
            (doubleFaces_cover r A f.1 S _).mpr ⟨f.2,rfl⟩⟩
        | inr e => exact Or.inr (Or.inl ⟨_,(r.qIndex e.1).isLt,_,
            (qDoubleEdges_cover r A e.1 S _).mpr ⟨e.2,rfl⟩,rfl⟩)
    | inr z =>
        have hd : z.2.val∈([0,1] : List ℕ) := by
          simp only [List.mem_cons,List.not_mem_nil,or_false]
          have := z.2.isLt; omega
        exact Or.inr (Or.inr ⟨_,(r.zIndex z.1).isLt,z.2.val,hd,rfl⟩)
theorem encodeDouble_family {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (x : P.X) (S : OddScale) :
    (∀v,(encodeDoubleVertex r x S v).family=0) ∧
    (∀e,(encodeDoubleEdge r x S e).family=0) ∧
    (∀f,(encodeDoubleFace r x S f).family=0) := by
  constructor
  · rintro ⟨c,v⟩
    rcases v with ⟨v,h⟩|⟨⟨e,h⟩,i⟩|f
    · cases v <;> rfl
    · cases e <;> rfl
    · rfl
  · constructor
    · rintro (⟨c,e⟩|⟨v,hv⟩)
      · rcases e with ⟨⟨e,h⟩,i⟩|f|f
        · cases e <;> rfl
        · rfl
        · rfl
      · rcases v with ⟨v,h⟩|⟨⟨e,h⟩,i⟩|f
        · cases v <;> rfl
        · cases e <;> rfl
        · rfl
    · rintro (⟨c,f⟩|⟨e,he⟩)
      · rfl
      · rcases e with ⟨⟨e,h⟩,i⟩|f|f
        · cases e <;> rfl
        · rfl
        · rfl
theorem encodeQVertex_family {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (q : P.Q) (S : OddScale) (v : QDoubleCylinderVertex P q S) :
    (encodeQVertex r q S v).family=0 := by
  rcases v with ⟨c,v⟩
  rcases v with (v|z)|zi <;> rfl
theorem encodeQEdge_family {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (q : P.Q) (S : OddScale) (e : QDoubleCylinderEdge P q S) :
    (encodeQEdge r q S e).family=0 := by cases e <;> rfl
theorem encodeQVertex_owner {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (q : P.Q) (S : OddScale) (v : QDoubleCylinderVertex P q S) :
    (encodeQVertex r q S v).owner=(r.qIndex q).val := by
  rcases v with ⟨c,v⟩
  rcases v with (v|z)|zi <;> rfl
theorem encodeQEdge_owner {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (q : P.Q) (S : OddScale) (e : QDoubleCylinderEdge P q S) :
    (encodeQEdge r q S e).owner=(r.qIndex q).val := by cases e <;> rfl
theorem encodeRX0_injective {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (A : TannerSquareAdmissible P) (S : OddScale) :
    Function.Injective (encodeRX0 r S) := by
  rintro ⟨x,a⟩ ⟨y,b⟩ h
  have hxy : x=y := by
    have ho := congrArg Code.owner h
    simpa only [encodeRX0,(encodeDouble_owner r x S).1 a,
      (encodeDouble_owner r y S).1 b,index_val_eq] using ho
  subst y
  exact Sigma.ext rfl (heq_of_eq ((encodeDoubleVertex_injective r A x S) h))
theorem encodeRX1_injective {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (A : TannerSquareAdmissible P) (S : OddScale) :
    Function.Injective (encodeRX1 r S) := by
  intro a b h
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          rcases a with ⟨x,a⟩; rcases b with ⟨y,b⟩
          have hxy : x=y := by
            have ho := congrArg Code.owner h
            simpa only [encodeRX1,(encodeDouble_owner r x S).2.1 a,
              (encodeDouble_owner r y S).2.1 b,index_val_eq] using ho
          subst y
          exact congrArg Sum.inl (Sigma.ext rfl (heq_of_eq ((encodeDoubleEdge_injective r A x S) h)))
      | inr b =>
          have hf := congrArg Code.family h
          simp only [encodeRX1,(encodeDouble_family r a.1 S).2.1 a.2] at hf
          omega
  | inr a =>
      cases b with
      | inl b =>
          have hf := congrArg Code.family h
          simp only [encodeRX1,(encodeDouble_family r b.1 S).2.1 b.2] at hf
          omega
      | inr b =>
          rcases a with ⟨q,a⟩; rcases b with ⟨t,b⟩
          have hqt : q=t := by
            have ho := congrArg Code.owner h
            simpa only [encodeRX1,encodeQVertex_owner,index_val_eq] using ho
          subst t
          have he := congrArg (fun c : Code => {c with family:=0}) h
          have ha : {encodeQVertex r q S a with family:=0}=encodeQVertex r q S a := by
            ext <;> simp [encodeQVertex_family]
          have hb : {encodeQVertex r q S b with family:=0}=encodeQVertex r q S b := by
            ext <;> simp [encodeQVertex_family]
          exact congrArg Sum.inr (Sigma.ext rfl (heq_of_eq ((encodeQVertex_injective r q S)
            (ha.symm.trans (he.trans hb)))))
theorem encodeRX2_injective {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (A : TannerSquareAdmissible P) (S : OddScale) :
    Function.Injective (encodeRX2 r S) := by
  intro a b h
  rcases a with (⟨x,a⟩|⟨q,a⟩)|⟨z,a⟩ <;>
    rcases b with (⟨y,b⟩|⟨t,b⟩)|⟨w,b⟩
  all_goals have hf := congrArg Code.family h
  all_goals simp only [encodeRX2,encodeQEdge_family,
    (encodeDouble_family r _ S).2.2] at hf
  all_goals try omega
  · have hxy : x=y := by
      have ho := congrArg Code.owner h
      simpa only [encodeRX2,(encodeDouble_owner r x S).2.2 a,
        (encodeDouble_owner r y S).2.2 b,index_val_eq] using ho
    subst y
    exact congrArg (Sum.inl ∘ Sum.inl) (Sigma.ext rfl (heq_of_eq
      ((encodeDoubleFace_injective r A x S) h)))
  · have hqt : q=t := by
      have ho := congrArg Code.owner h
      simpa only [encodeRX2,encodeQEdge_owner,index_val_eq] using ho
    subst t
    have he := congrArg (fun c : Code => {c with family:=0}) h
    have ha : {encodeQEdge r q S a with family:=0}=encodeQEdge r q S a := by
      ext <;> simp [encodeQEdge_family]
    have hb : {encodeQEdge r q S b with family:=0}=encodeQEdge r q S b := by
      ext <;> simp [encodeQEdge_family]
    exact congrArg (Sum.inl ∘ Sum.inr) (Sigma.ext rfl (heq_of_eq
      ((encodeQEdge_injective r q S) (ha.symm.trans (he.trans hb)))))
  · have hzw : z=w := by
      have ho := congrArg Code.owner h
      simpa only [encodeRX2,index_val_eq] using ho
    exact congrArg Sum.inr (Prod.ext hzw (Fin.ext (congrArg Code.copy h)))
theorem handleQ_lt {A : Type*} (e : A → Code) (xs : List Code) (a : A)
    (ha : e a∈xs) : (handleQ (e a) xs).1< xs.length := by
  induction xs with
  | nil => simp at ha
  | cons c cs ih =>
      by_cases h : e a=c
      · simp [handleQ,equalCodeQ,h]
      · have hn : e a≠c := h
        have htail : e a∈cs := (List.mem_cons.mp ha).resolve_left hn
        simpa [handleQ,equalCodeQ,h] using Nat.succ_lt_succ (ih htail)
theorem handleQ_get (c : Code) (xs : List Code) (hc : c∈xs) :
    xs.get ⟨(handleQ c xs).1,handleQ_lt id xs c hc⟩=c := by
  induction xs with
  | nil => simp at hc
  | cons a as ih =>
      by_cases h : c=a
      · subst a
        simp [handleQ,equalCodeQ]
      · have htail := (List.mem_cons.mp hc).resolve_left h
        simpa [handleQ,equalCodeQ,h] using ih htail
theorem handleQ_get_index (xs : List Code) (hn : xs.Nodup) (i : Fin xs.length) :
    (handleQ (xs.get i) xs).1=i.val := by
  induction xs with
  | nil => exact Fin.elim0 i
  | cons a as ih =>
      cases i using Fin.cases with
      | zero => simp [handleQ,equalCodeQ]
      | succ i =>
          have hnot : as.get i≠a := by
            intro h
            exact (List.nodup_cons.mp hn).1 (h ▸ List.get_mem as i)
          have hnot' : as[i.val]≠a := hnot
          change (handleQ (as.get i) (a::as)).1=i.val+1
          rw [show handleQ (as.get i) (a::as)=
            ((handleQ (as.get i) as).1+1,41+(handleQ (as.get i) as).2+2) from by
              simp [handleQ,equalCodeQ,hnot']]
          exact congrArg Nat.succ (ih (List.nodup_cons.mp hn).2 i)
noncomputable def listIndexEquiv {A : Type*} (xs : List Code) (e : A → Code)
    (hi : Function.Injective e) (hn : xs.Nodup)
    (hc : ∀c,c∈xs ↔ ∃a,e a=c) : A ≃ Fin xs.length :=
  Equiv.ofBijective (fun a => ⟨(handleQ (e a) xs).1,handleQ_lt e xs a ((hc _).mpr ⟨a,rfl⟩)⟩) (by
    constructor
    · intro a b hab
      apply hi
      have hget := congrArg (fun i : Fin xs.length => xs.get i) hab
      exact (handleQ_get (e a) xs ((hc _).mpr ⟨a,rfl⟩)).symm.trans
        (hget.trans (handleQ_get (e b) xs ((hc _).mpr ⟨b,rfl⟩)))
    · intro i
      obtain ⟨a,ha⟩ := (hc (xs.get i)).mp (List.get_mem xs i)
      refine ⟨a,Fin.ext ?_⟩
      change (handleQ (e a) xs).1=i.val
      rw [ha,handleQ_get_index xs hn i])
theorem finTwo_mem (d : Two) : d.val∈([0,1] : List ℕ) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  have := d.isLt
  omega
theorem rxFaceCodes_cover {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (A : TannerSquareAdmissible P) (S : OddScale) (c : Code) :
    c∈(rxFaceCodesQ F S.half).1 ↔ ∃f : RXFace P S,encodeRXFace r S f=c := by
  simp only [rxFaceCodesQ,collectQ_cons_value,collectQ_nil_value,List.mem_append,List.not_mem_nil,or_false,
    rxLocalFaceCodesQ,rxGlueFaceCodesQ,rxOldFaceCodesQ,loopQ_mem,
    flatMapQ_value,List.mem_flatMap,mapQ_value,List.mem_map,emitQ]
  constructor
  · rintro (⟨xi,hxi,a,ha,k,hk,l,hl,hc⟩|
      ⟨xi,hxi,qi,hqi,a,ha,k,hk,hc⟩|⟨fi,hfi,d,hd,hc⟩)
    · let x := r.xIndex.symm ⟨xi,hxi⟩
      have hx : (r.xIndex x).val=xi := by simp [x]
      obtain ⟨f,hf⟩ := (doubleFaces_cover r A x S a).mp (hx.symm ▸ ha)
      refine ⟨.inl ⟨x,f,(⟨k,finTwo_native k hk⟩,⟨l,finTwo_native l hl⟩)⟩,?_⟩
      simpa only [encodeRXFace,emitQ,hf] using hc
    · let x := r.xIndex.symm ⟨xi,hxi⟩
      have hx : (r.xIndex x).val=xi := by simp [x]
      let q := r.qIndex.symm ⟨qi,starQs_bound F xi qi hqi⟩
      have hq : (r.qIndex q).val=qi := by simp [q]
      have hxq : P.xq x q=true := (starQs_actual r A x q).mp (by simpa [hx,hq] using hqi)
      obtain ⟨e,he⟩ := (qDoubleEdges_cover r A q S a).mp (hq.symm ▸ ha)
      have ha_owner : a.owner=qi := by
        calc
          a.owner=(encodeQEdge r q S e).owner := congrArg Code.owner he.symm
          _=(r.qIndex q).val := by cases e <;> rfl
          _=qi := hq
      refine ⟨.inr (.inl ⟨⟨(x,q),hxq⟩,e,⟨k,finTwo_native k hk⟩⟩),?_⟩
      simpa only [encodeRXFace,emitQ,hx,hq,he,ha_owner] using hc
    · let f := r.fIndex.symm ⟨fi,hfi⟩
      refine ⟨.inr (.inr (f,⟨d,finTwo_native d hd⟩)),?_⟩
      simpa [encodeRXFace,f,emitQ] using hc
  · rintro ⟨f,rfl⟩
    cases f with
    | inl f => exact Or.inl ⟨_,(r.xIndex f.1).isLt,_,
        (doubleFaces_cover r A f.1 S _).mpr ⟨f.2.1,rfl⟩,
        f.2.2.1.val,finTwo_mem f.2.2.1,f.2.2.2.val,finTwo_mem f.2.2.2,rfl⟩
    | inr f =>
        cases f with
        | inl f => exact Or.inr (Or.inl ⟨_,(r.xIndex f.1.1.1).isLt,_,
            (starQs_actual r A f.1.1.1 f.1.1.2).mpr f.1.2,_,
            (qDoubleEdges_cover r A f.1.1.2 S _).mpr ⟨f.2.1,rfl⟩,
            f.2.2.val,finTwo_mem f.2.2,by simp only [encodeRXFace,encodeQEdge_owner]⟩)
        | inr f => exact Or.inr (Or.inr ⟨_,(r.fIndex f.1).isLt,f.2.val,finTwo_mem f.2,rfl⟩)
theorem encodeDoubleFace_corner_zero {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (x : P.X) (S : OddScale) (f : DoubleCylinderFace P x S) :
    (encodeDoubleFace r x S f).k=0 ∧ (encodeDoubleFace r x S f).l=0 := by
  cases f with
  | inl f => exact ⟨rfl,rfl⟩
  | inr f =>
      rcases f with ⟨e,he⟩
      rcases e with ⟨⟨e,h⟩,i⟩|f|f
      · cases e <;> exact ⟨rfl,rfl⟩
      · exact ⟨rfl,rfl⟩
      · exact ⟨rfl,rfl⟩
theorem encodeRXFace_injective {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (A : TannerSquareAdmissible P) (S : OddScale) :
    Function.Injective (encodeRXFace r S) := by
  intro a b h
  rcases a with ⟨x,a,ac⟩|(⟨a,ae,ac⟩|⟨af,ac⟩) <;>
    rcases b with ⟨y,b,bc⟩|(⟨b,be,bc⟩|⟨bf,bc⟩)
  all_goals have hf := congrArg Code.family h
  all_goals simp only [encodeRXFace,(encodeDouble_family r _ S).2.2] at hf
  all_goals try omega
  · have hxy : x=y := by
      have ho := congrArg Code.owner h
      simpa only [encodeRXFace,(encodeDouble_owner r x S).2.2 a,
        (encodeDouble_owner r y S).2.2 b,index_val_eq] using ho
    subst y
    have he := congrArg (fun c : Code => {c with k:=0,l:=0}) h
    have ha : {encodeDoubleFace r x S a with k:=0,l:=0}=encodeDoubleFace r x S a := by
      ext <;> simp [(encodeDoubleFace_corner_zero r x S a).1,
        (encodeDoubleFace_corner_zero r x S a).2]
    have hb : {encodeDoubleFace r x S b with k:=0,l:=0}=encodeDoubleFace r x S b := by
      ext <;> simp [(encodeDoubleFace_corner_zero r x S b).1,
        (encodeDoubleFace_corner_zero r x S b).2]
    have hab := (encodeDoubleFace_injective r A x S) (ha.symm.trans (he.trans hb))
    have hac : ac=bc := Prod.ext (Fin.ext (congrArg Code.k h)) (Fin.ext (congrArg Code.l h))
    subst b; subst bc; rfl
  · have hx : a.1.1=b.1.1 := by
      have ho := congrArg Code.owner h
      simpa only [encodeRXFace,index_val_eq] using ho
    have hq : a.1.2=b.1.2 := by
      have hp := congrArg Code.p h
      simpa only [encodeRXFace,encodeQEdge_owner,index_val_eq] using hp
    have hab : a=b := Subtype.ext (Prod.ext hx hq)
    subst b
    have he := congrArg (fun c : Code =>
      ({owner:=c.p,copy:=c.copy,part:=c.part,p:=c.q,i:=c.i} : Code)) h
    have hea : (fun c : Code => ({owner:=c.p,copy:=c.copy,part:=c.part,p:=c.q,i:=c.i} : Code))
        (encodeRXFace r S (.inr (.inl ⟨a,ae,ac⟩)))=encodeQEdge r a.1.2 S ae := by
      cases ae <;> rfl
    have heb : (fun c : Code => ({owner:=c.p,copy:=c.copy,part:=c.part,p:=c.q,i:=c.i} : Code))
        (encodeRXFace r S (.inr (.inl ⟨a,be,bc⟩)))=encodeQEdge r a.1.2 S be := by
      cases be <;> rfl
    have heq := (encodeQEdge_injective r a.1.2 S) (hea.symm.trans (he.trans heb))
    have hc : ac=bc := Fin.ext (congrArg Code.k h)
    subst be; subst bc; rfl
  · have hf' : af=bf := by
      have ho := congrArg Code.owner h
      simpa only [encodeRXFace,index_val_eq] using ho
    have hc : ac=bc := Fin.ext (congrArg Code.copy h)
    subst bf; subst bc; rfl
theorem encode_doubleEdge_endpoint {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (x : P.X) (S : OddScale) (e : DoubleCylinderEdge P x S) (d : Two) :
    (doubleEdgeVertexQ F S.half (encodeDoubleEdge r x S e) d.val).1=
      encodeDoubleVertex r x S
        (BDL26TannerLocalRegularity.edgeEndpoint (tannerDoubleCylinderEdgeStart P x S)
          (tannerDoubleCylinderEdgeEnd P x S) e d) := by
  cases e with
  | inl e =>
      rcases e with ⟨c,e⟩
      rcases e with ⟨⟨e,he⟩,i⟩|f|f
      · cases e with
        | inl e =>
            have hx : e.1.1=x := by
              change decide (∃f : P.Face,decide (P.faceX f=x)=true ∧
                decide (e=faceXQEdge P f 0 ∨ e=faceXQEdge P f 1)=true)=true at he
              simp only [decide_eq_true_eq] at he
              obtain ⟨f,hf,he|he⟩ := he <;>
                exact (congrArg (fun a : XQEdge P => a.1.1) he).trans hf
            by_cases hiz : i.val=0
            · have hhalfzero : S.half≠0 := Nat.ne_of_gt S.half_pos
              have hhalfpos : 1≤ S.half := S.half_pos
              by_cases hit : S.half=1
              · have hlast : (i.val+1=S.half) ↔ (S.half=1) := by omega
                fin_cases d <;>
                  simp only [BDL26TannerLocalRegularity.edgeEndpoint_zero,
                    BDL26TannerLocalRegularity.edgeEndpoint_one] <;>
                  simp [doubleEdgeVertexQ,segmentVertexQ,encodeDoubleEdge,encodeSubEdge,
                    encodeStarEdge,encodeDoubleVertex,encodeSubVertex,encodeStarVertex,
                    BDL26TannerLocalRegularity.edgeEndpoint_zero,BDL26TannerLocalRegularity.edgeEndpoint_one,tannerDoubleCylinderEdgeStart,tannerDoubleCylinderEdgeEnd,
                    subdivisionEdgeStart,subdivisionEdgeEnd,subdivisionSegmentStart,
                    subdivisionSegmentEnd,xStarEdgeStart,xStarEdgeEnd,hx,hiz,hit,hlast,hhalfzero,hhalfpos,Nat.ne_of_lt i.isLt]
              · have hreverse : 1≠S.half := Ne.symm hit
                have hlast : (i.val+1=S.half) ↔ (S.half=1) := by omega
                fin_cases d <;>
                  simp only [BDL26TannerLocalRegularity.edgeEndpoint_zero,
                    BDL26TannerLocalRegularity.edgeEndpoint_one] <;>
                  simp [doubleEdgeVertexQ,segmentVertexQ,encodeDoubleEdge,encodeSubEdge,
                    encodeStarEdge,encodeDoubleVertex,encodeSubVertex,encodeStarVertex,
                    BDL26TannerLocalRegularity.edgeEndpoint_zero,BDL26TannerLocalRegularity.edgeEndpoint_one,tannerDoubleCylinderEdgeStart,tannerDoubleCylinderEdgeEnd,
                    subdivisionEdgeStart,subdivisionEdgeEnd,subdivisionSegmentStart,
                    subdivisionSegmentEnd,xStarEdgeStart,xStarEdgeEnd,hx,hiz,hit,hreverse,hlast,hhalfzero,hhalfpos,Nat.ne_of_lt i.isLt]
            · have hhalfzero : S.half≠0 := Nat.ne_of_gt S.half_pos
              have hhalfpos : 1≤ S.half := S.half_pos
              by_cases hit : i.val+1=S.half
              all_goals fin_cases d <;>
                simp only [BDL26TannerLocalRegularity.edgeEndpoint_zero,
                  BDL26TannerLocalRegularity.edgeEndpoint_one] <;>
                simp [doubleEdgeVertexQ,segmentVertexQ,encodeDoubleEdge,encodeSubEdge,
                  encodeStarEdge,encodeDoubleVertex,encodeSubVertex,encodeStarVertex,
                  BDL26TannerLocalRegularity.edgeEndpoint_zero,BDL26TannerLocalRegularity.edgeEndpoint_one,tannerDoubleCylinderEdgeStart,tannerDoubleCylinderEdgeEnd,
                  subdivisionEdgeStart,subdivisionEdgeEnd,subdivisionSegmentStart,
                  subdivisionSegmentEnd,xStarEdgeStart,xStarEdgeEnd,hx,hiz,hit,hhalfzero,hhalfpos,Nat.ne_of_lt i.isLt]
        | inr e =>
            by_cases hiz : i.val=0
            · have hhalfzero : S.half≠0 := Nat.ne_of_gt S.half_pos
              have hhalfpos : 1≤ S.half := S.half_pos
              by_cases hit : S.half=1
              · have hlast : (i.val+1=S.half) ↔ (S.half=1) := by omega
                fin_cases d <;>
                  simp only [BDL26TannerLocalRegularity.edgeEndpoint_zero,
                    BDL26TannerLocalRegularity.edgeEndpoint_one] <;>
                  simp [doubleEdgeVertexQ,segmentVertexQ,encodeDoubleEdge,encodeSubEdge,
                    encodeStarEdge,encodeDoubleVertex,encodeSubVertex,encodeStarVertex,
                    BDL26TannerLocalRegularity.edgeEndpoint_zero,BDL26TannerLocalRegularity.edgeEndpoint_one,tannerDoubleCylinderEdgeStart,tannerDoubleCylinderEdgeEnd,
                    subdivisionEdgeStart,subdivisionEdgeEnd,subdivisionSegmentStart,
                    subdivisionSegmentEnd,xStarEdgeStart,xStarEdgeEnd,hiz,hit,hlast,hhalfzero,hhalfpos,Nat.ne_of_lt i.isLt]
              · have hreverse : 1≠S.half := Ne.symm hit
                have hlast : (i.val+1=S.half) ↔ (S.half=1) := by omega
                fin_cases d <;>
                  simp only [BDL26TannerLocalRegularity.edgeEndpoint_zero,
                    BDL26TannerLocalRegularity.edgeEndpoint_one] <;>
                  simp [doubleEdgeVertexQ,segmentVertexQ,encodeDoubleEdge,encodeSubEdge,
                    encodeStarEdge,encodeDoubleVertex,encodeSubVertex,encodeStarVertex,
                    BDL26TannerLocalRegularity.edgeEndpoint_zero,BDL26TannerLocalRegularity.edgeEndpoint_one,tannerDoubleCylinderEdgeStart,tannerDoubleCylinderEdgeEnd,
                    subdivisionEdgeStart,subdivisionEdgeEnd,subdivisionSegmentStart,
                    subdivisionSegmentEnd,xStarEdgeStart,xStarEdgeEnd,hiz,hit,hreverse,hlast,hhalfzero,hhalfpos,Nat.ne_of_lt i.isLt]
            · have hhalfzero : S.half≠0 := Nat.ne_of_gt S.half_pos
              have hhalfpos : 1≤ S.half := S.half_pos
              by_cases hit : i.val+1=S.half
              all_goals fin_cases d <;>
                simp only [BDL26TannerLocalRegularity.edgeEndpoint_zero,
                  BDL26TannerLocalRegularity.edgeEndpoint_one] <;>
                simp [doubleEdgeVertexQ,segmentVertexQ,encodeDoubleEdge,encodeSubEdge,
                  encodeStarEdge,encodeDoubleVertex,encodeSubVertex,encodeStarVertex,
                  BDL26TannerLocalRegularity.edgeEndpoint_zero,BDL26TannerLocalRegularity.edgeEndpoint_one,tannerDoubleCylinderEdgeStart,tannerDoubleCylinderEdgeEnd,
                  subdivisionEdgeStart,subdivisionEdgeEnd,subdivisionSegmentStart,
                  subdivisionSegmentEnd,xStarEdgeStart,xStarEdgeEnd,hiz,hit,hhalfzero,hhalfpos,Nat.ne_of_lt i.isLt]
      · rcases f with ⟨f,i,j⟩
        fin_cases d
        · let ii : Fin (S.half+1) := ⟨i.val,by have := i.isLt; omega⟩
          let jj : Fin (S.half+1) := ⟨j.val+1,by have := j.isLt; have := S.half_pos; omega⟩
          change { (gridVertexQ F (r.xIndex x).val S.half (r.fIndex f.1).val i.val (j.val+1)).1 with copy:=c.val } =
            { encodeSubVertex r x S (subdivisionGridVertex P x S f ii jj) with copy:=c.val }
          exact congrArg (fun v : Code => {v with copy:=c.val}) (encode_gridVertex r x S f ii jj).symm
        · let ii : Fin (S.half+1) := ⟨i.val+1,by have := i.isLt; omega⟩
          let jj : Fin (S.half+1) := ⟨j.val+1,by have := j.isLt; have := S.half_pos; omega⟩
          change { (gridVertexQ F (r.xIndex x).val S.half (r.fIndex f.1).val (i.val+1) (j.val+1)).1 with copy:=c.val } =
            { encodeSubVertex r x S (subdivisionGridVertex P x S f ii jj) with copy:=c.val }
          exact congrArg (fun v : Code => {v with copy:=c.val}) (encode_gridVertex r x S f ii jj).symm
      · rcases f with ⟨f,i,j⟩
        fin_cases d
        · let ii : Fin (S.half+1) := ⟨i.val+1,by have := i.isLt; have := S.half_pos; omega⟩
          let jj : Fin (S.half+1) := ⟨j.val,by have := j.isLt; omega⟩
          change { (gridVertexQ F (r.xIndex x).val S.half (r.fIndex f.1).val (i.val+1) j.val).1 with copy:=c.val } =
            { encodeSubVertex r x S (subdivisionGridVertex P x S f ii jj) with copy:=c.val }
          exact congrArg (fun v : Code => {v with copy:=c.val}) (encode_gridVertex r x S f ii jj).symm
        · let ii : Fin (S.half+1) := ⟨i.val+1,by have := i.isLt; have := S.half_pos; omega⟩
          let jj : Fin (S.half+1) := ⟨j.val+1,by have := j.isLt; omega⟩
          change { (gridVertexQ F (r.xIndex x).val S.half (r.fIndex f.1).val (i.val+1) (j.val+1)).1 with copy:=c.val } =
            { encodeSubVertex r x S (subdivisionGridVertex P x S f ii jj) with copy:=c.val }
          exact congrArg (fun v : Code => {v with copy:=c.val}) (encode_gridVertex r x S f ii jj).symm
  | inr v =>
      rcases v with ⟨v,hv⟩
      rcases v with ⟨v,hv'⟩|⟨⟨e,he⟩,i⟩|f
      · cases v with
        | x y => simp [subdivisionBoundaryVertexMember,xStarBoundaryVertexMember] at hv
        | q q => fin_cases d <;> rfl
        | z z => fin_cases d <;> rfl
      · cases e with
        | inl e => simp [subdivisionBoundaryVertexMember,xStarBoundaryEdgeMember] at hv
        | inr e => fin_cases d <;> rfl
      · simp [subdivisionBoundaryVertexMember] at hv
theorem encode_qEdge_image {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (q : P.Q) (x : P.X) (hxq : P.xq x q=true)
    (S : OddScale) (e : QDoubleCylinderEdge P q S) :
    (qEdgeImageQ (r.xIndex x).val (encodeQEdge r q S e)).1=
      encodeDoubleEdge r x S (qToXDoubleCylinderEdgeRaw P q x hxq S e) := by
  cases e with
  | inl e =>
      simp [qEdgeImageQ,encodeQEdge,encodeDoubleEdge,encodeSubEdge,encodeStarEdge,
        qToXDoubleCylinderEdgeRaw,qToXSubdivisionBoundaryEdge,
        subdivisionOriginalBoundaryEdge,xStarBoundaryEdgeToStar,qToXBoundaryEdge,
        qToXBoundaryEdge_value]
  | inr z =>
      simp [qEdgeImageQ,encodeQEdge,encodeDoubleEdge,encodeSubVertex,encodeStarVertex,
        qToXDoubleCylinderEdgeRaw,subdivisionOriginalBoundaryVertex,
        xStarBoundaryVertexToStar,xBoundaryEdgeEnd,qToXBoundaryEdge]
theorem encode_qEdge_endpoint {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (q : P.Q) (S : OddScale)
    (e : QDoubleCylinderEdge P q S) (d : Two) :
    (qDoubleEdgeVertexQ S.half (encodeQEdge r q S e) d.val).1=
      {encodeQVertex r q S
        (BDL26TannerLocalRegularity.edgeEndpoint (qDoubleCylinderEdgeStart P q S) (qDoubleCylinderEdgeEnd P q S) e d)
        with family:=1} := by
  fin_cases d
  · change (qDoubleEdgeVertexQ S.half (encodeQEdge r q S e) 0).1 =
        {encodeQVertex r q S (qDoubleCylinderEdgeStart P q S e) with family := 1}
    exact (encode_qEdge_start r q S e).symm
  · change (qDoubleEdgeVertexQ S.half (encodeQEdge r q S e) 1).1 =
        {encodeQVertex r q S (qDoubleCylinderEdgeEnd P q S e) with family := 1}
    exact (encode_qEdge_end r q S e).symm
theorem rx_endpoint_eq {V E : Type} (a b : E → V) (e : E) (d : Two) :
    BDL26RXLocalReplacement.edgeEndpoint a b e d=
      BDL26TannerLocalRegularity.edgeEndpoint a b e d := by
  fin_cases d <;> rfl
theorem rz_endpoint_eq {V E : Type} (a b : E → V) (e : E) (d : Two) :
    BDL26RZLocalReplacement.edgeEndpoint a b e d=
      BDL26TannerLocalRegularity.edgeEndpoint a b e d := by
  fin_cases d <;> rfl
theorem qEdgeImageQ_family (x : ℕ) (c : Code) :
    qEdgeImageQ x {c with family:=1}=qEdgeImageQ x c := rfl
theorem qDoubleEdgeVertexQ_family (m : ℕ) (c : Code) (d : ℕ) :
    qDoubleEdgeVertexQ m {c with family:=1} d=qDoubleEdgeVertexQ m c d := rfl
theorem encode_face_horizontal {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (x : P.X) (S : OddScale) (f : SubdivisionFace P x S) (d : Two) :
    encodeSubEdge r x S (subdivisionFaceBoundaryEdge P x S f (0,d)) =
      (horizontalEdgeQ F (r.xIndex x).val S.half (r.fIndex f.1.1).val
        f.2.1.val (f.2.2.val+d.val)).1 := by
  fin_cases d
  · let j : Fin (S.half+1) := ⟨f.2.2.val,by have := f.2.2.isLt; omega⟩
    change encodeSubEdge r x S (subdivisionHorizontalEdge P x S f.1 f.2.1 j) =
      (horizontalEdgeQ F (r.xIndex x).val S.half (r.fIndex f.1.1).val f.2.1.val f.2.2.val).1
    exact encode_horizontalEdge r x S f.1 f.2.1 j
  · let j : Fin (S.half+1) := ⟨f.2.2.val+1,by have := f.2.2.isLt; omega⟩
    change encodeSubEdge r x S (subdivisionHorizontalEdge P x S f.1 f.2.1 j) =
      (horizontalEdgeQ F (r.xIndex x).val S.half (r.fIndex f.1.1).val f.2.1.val (f.2.2.val+1)).1
    exact encode_horizontalEdge r x S f.1 f.2.1 j
theorem encode_face_vertical {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (x : P.X) (S : OddScale) (f : SubdivisionFace P x S) (d : Two) :
    encodeSubEdge r x S (subdivisionFaceBoundaryEdge P x S f (1,d)) =
      (verticalEdgeQ F (r.xIndex x).val S.half (r.fIndex f.1.1).val
        (f.2.1.val+d.val) f.2.2.val).1 := by
  fin_cases d
  · let i : Fin (S.half+1) := ⟨f.2.1.val,by have := f.2.1.isLt; omega⟩
    change encodeSubEdge r x S (subdivisionVerticalEdge P x S f.1 i f.2.2) =
      (verticalEdgeQ F (r.xIndex x).val S.half (r.fIndex f.1.1).val f.2.1.val f.2.2.val).1
    exact encode_verticalEdge r x S f.1 i f.2.2
  · let i : Fin (S.half+1) := ⟨f.2.1.val+1,by have := f.2.1.isLt; omega⟩
    change encodeSubEdge r x S (subdivisionVerticalEdge P x S f.1 i f.2.2) =
      (verticalEdgeQ F (r.xIndex x).val S.half (r.fIndex f.1.1).val (f.2.1.val+1) f.2.2.val).1
    exact encode_verticalEdge r x S f.1 i f.2.2
theorem faceEndpoints_correct {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (S : OddScale) (f : RXFace P S) :
    (faceEndpointsQ F S.half (encodeRXFace r S f)).1=
      ⟨encodeRX0 r S (rxFaceX P S f),encodeRX2 r S (rxFaceZ P S f),
        encodeRX1 r S (rxFaceQ P S f 0),encodeRX1 r S (rxFaceQ P S f 1)⟩ := by
  cases f with
  | inl f =>
      rcases f with ⟨x,f,⟨k,l⟩⟩
      cases f with
      | inl f =>
          have hki : (gridEndpoint f.2.2.1 k).val=f.2.2.1.val+k.val := by
            fin_cases k <;> simp [gridEndpoint,twoSelect,lowerGridIndex,upperGridIndex]
          have hlj : (gridEndpoint f.2.2.2 l).val=f.2.2.2.val+l.val := by
            fin_cases l <;> simp [gridEndpoint,twoSelect,lowerGridIndex,upperGridIndex]
          apply FaceCodes.ext
          · change { (gridVertexQ F (r.xIndex x).val S.half (r.fIndex f.2.1.1).val
                (f.2.2.1.val+k.val) (f.2.2.2.val+l.val)).1 with copy:=f.1.val } =
              { encodeSubVertex r x S (subdivisionGridVertex P x S f.2.1
                  (gridEndpoint f.2.2.1 k) (gridEndpoint f.2.2.2 l)) with copy:=f.1.val }
            have hg := encode_gridVertex r x S f.2.1
              (gridEndpoint f.2.2.1 k) (gridEndpoint f.2.2.2 l)
            exact congrArg (fun c : Code => {c with copy:=f.1.val})
              (by simpa only [hki,hlj] using hg.symm)
          · rfl
          · change { (horizontalEdgeQ F (r.xIndex x).val S.half (r.fIndex f.2.1.1).val
                  f.2.2.1.val (f.2.2.2.val+l.val)).1 with copy:=f.1.val } =
              {encodeSubEdge r x S (subdivisionFaceBoundaryEdge P x S f.2 (0,l)) with copy:=f.1.val}
            exact congrArg (fun c : Code => {c with copy:=f.1.val})
              (encode_face_horizontal r x S f.2 l).symm
          · change { (verticalEdgeQ F (r.xIndex x).val S.half (r.fIndex f.2.1.1).val
                  (f.2.2.1.val+k.val) f.2.2.2.val).1 with copy:=f.1.val } =
              {encodeSubEdge r x S (subdivisionFaceBoundaryEdge P x S f.2 (1,k)) with copy:=f.1.val}
            exact congrArg (fun c : Code => {c with copy:=f.1.val})
              (encode_face_vertical r x S f.2 k).symm
      | inr f =>
          have hp := (encodeSubEdge_boundary r x S f.1).mp f.2
          rcases f with ⟨e,he⟩
          rcases e with ⟨⟨e,hs⟩,i⟩|f|f
          · cases e with
            | inl e => simp [subdivisionBoundaryEdgeMember,xStarBoundaryEdgeMember] at he
            | inr e =>
                have hhalfzero : S.half≠0 := Nat.ne_of_gt S.half_pos
                by_cases hhalf : S.half=1
                · by_cases hiz : i.val=0 <;> by_cases hit : i.val+1=S.half <;>
                  fin_cases k <;> fin_cases l <;>
                    simp [faceEndpointsQ,localFaceEndpointsQ,encodeRXFace,encodeDoubleFace,
                      encodeRX0,rxFaceX,localFaceX,
                      doubleCylinderRectangleCorner,rx_endpoint_eq,
                      BDL26TannerLocalRegularity.edgeEndpoint_zero,
                      BDL26TannerLocalRegularity.edgeEndpoint_one,encodeDoubleVertex,encodeSubVertex,
                      encodeStarVertex,encodeRX2,rxFaceZ,localFaceZ,encodeRX1,rxFaceQ,
                      twoSelect,localFaceQ0,localFaceQ0Edge,localFaceQ0EdgeAt,
                      localFaceQ1,localFaceQ1Edge,localFaceQ1EdgeAt,
                      doubleCylinderRectangleBoundaryEdge,encodeDoubleEdge,bridgeOfVertexQ,
                      encode_doubleEdge_endpoint,doubleEdgeVertexQ,segmentVertexQ,encodeSubEdge,encodeStarEdge,
                      subdivisionBoundaryEdgeStart,subdivisionBoundaryEdgeEnd,
                      subdivisionEdgeStart,subdivisionEdgeEnd,subdivisionSegmentStart,
                      subdivisionSegmentEnd,xStarEdgeStart,xStarEdgeEnd,hhalf,hhalfzero,hiz,hit,Nat.ne_of_lt i.isLt] <;>
                    omega
                · have hreverse : 1≠S.half := Ne.symm hhalf
                  by_cases hiz : i.val=0 <;> by_cases hit : i.val+1=S.half <;>
                  fin_cases k <;> fin_cases l <;>
                    simp [faceEndpointsQ,localFaceEndpointsQ,encodeRXFace,encodeDoubleFace,
                      encodeRX0,rxFaceX,localFaceX,
                      doubleCylinderRectangleCorner,rx_endpoint_eq,
                      BDL26TannerLocalRegularity.edgeEndpoint_zero,
                      BDL26TannerLocalRegularity.edgeEndpoint_one,encodeDoubleVertex,encodeSubVertex,
                      encodeStarVertex,encodeRX2,rxFaceZ,localFaceZ,encodeRX1,rxFaceQ,
                      twoSelect,localFaceQ0,localFaceQ0Edge,localFaceQ0EdgeAt,
                      localFaceQ1,localFaceQ1Edge,localFaceQ1EdgeAt,
                      doubleCylinderRectangleBoundaryEdge,encodeDoubleEdge,bridgeOfVertexQ,
                      encode_doubleEdge_endpoint,doubleEdgeVertexQ,segmentVertexQ,encodeSubEdge,encodeStarEdge,
                      subdivisionBoundaryEdgeStart,subdivisionBoundaryEdgeEnd,
                      subdivisionEdgeStart,subdivisionEdgeEnd,subdivisionSegmentStart,
                      subdivisionSegmentEnd,xStarEdgeStart,xStarEdgeEnd,hhalf,hreverse,hhalfzero,hiz,hit,Nat.ne_of_lt i.isLt] <;>
                    omega
          · simp [subdivisionBoundaryEdgeMember] at he
          · simp [subdivisionBoundaryEdgeMember] at he
  | inr f =>
      cases f with
      | inl f =>
          rcases f with ⟨a,e,d⟩
          let ce : Code := encodeQEdge r a.1.2 S e
          have hcode : ({ family := 1, owner := ce.owner, copy := ce.copy, part := ce.part, p := ce.p, i := ce.i } : Code) =
              {ce with family := 1} := by
            cases e <;> rfl
          dsimp only [ce] at hcode
          have himage := encode_qEdge_image r a.1.2 a.1.1 a.2 S e
          apply FaceCodes.ext
          · simpa [faceEndpointsQ,glueFaceEndpointsQ,encodeRXFace,rxFaceX,glueFaceX,
              encodeRX0,hcode,qEdgeImageQ_family,himage,rx_endpoint_eq] using
                encode_doubleEdge_endpoint r a.1.1 S
                  (qToXDoubleCylinderEdgeRaw P a.1.2 a.1.1 a.2 S e) d
          · cases e <;> rfl
          · simpa [faceEndpointsQ,glueFaceEndpointsQ,encodeRXFace,rxFaceQ,twoSelect,
              glueFaceQ0,encodeRX1,hcode,qEdgeImageQ_family,ite_true] using
                encode_qEdge_image r a.1.2 a.1.1 a.2 S e
          · simpa [faceEndpointsQ,glueFaceEndpointsQ,encodeRXFace,rxFaceQ,twoSelect,
              glueFaceQ1,encodeRX1,hcode,qDoubleEdgeVertexQ_family,rx_endpoint_eq,ite_false] using
                encode_qEdge_endpoint r a.1.2 S e d
      | inr f =>
          apply FaceCodes.ext <;>
            simp [faceEndpointsQ,oldFaceEndpointsQ,encodeRXFace,rxFaceX,rxFaceZ,rxFaceQ,
              oldZFaceX,oldZFaceZ,oldZFaceQ,oldFaceInXStar,xStarFaceZVertex,encodeRX0,encodeRX1,encodeRX2,
              encodeDoubleVertex,encodeSubVertex,encodeStarVertex,encodeQVertex,
              r.face_x,r.face_z,r.face_q0,r.face_q1]
def finLengthEquiv {m n : ℕ} (h : m=n) : Fin m ≃ Fin n := by
  subst n
  exact Equiv.refl _
theorem finLengthEquiv_val {m n : ℕ} (h : m=n) (i : Fin m) :
    (finLengthEquiv h i).val=i.val := by
  subst n
  rfl
theorem native_list_get_map {A B : Type*} (f : A → B) (as : List A)
    (i : ℕ) (hi : i<as.length) :
    (as.map f).get ⟨i,by simpa only [List.length_map] using hi⟩ =
      f (as.get ⟨i,hi⟩) := by
  induction as generalizing i with
  | nil => simp at hi
  | cons a as ih =>
      cases i with
      | zero => rfl
      | succ i => exact ih i (Nat.lt_of_succ_lt_succ hi)
theorem native_list_get_transport {A : Type*} (as bs : List A)
    (h : as=bs) (i : ℕ) (ha : i<as.length) (hb : i<bs.length) :
    as.get ⟨i,ha⟩=bs.get ⟨i,hb⟩ := by
  subst bs
  rfl
theorem faceAtQ_map_handle (k : Code → Query FaceRow) (cs : List Code)
    (c : Code) (hc : c∈cs) :
    (faceAtQ (mapQ k cs).1 (handleQ c cs).1).1=(k c).1 := by
  have hi := handleQ_lt id cs c hc
  let j : Fin cs.length := ⟨(handleQ c cs).1,by simpa only [id_eq] using hi⟩
  have hj : cs.get j=c := handleQ_get c cs hc
  have hm := native_list_get_map (fun a => (k a).1) cs j.val j.isLt
  have hh := faceAtQ_get (mapQ k cs).1
    (⟨j.val,by simpa only [mapQ_length] using j.isLt⟩)
  calc
    (faceAtQ (mapQ k cs).1 (handleQ c cs).1).1 =
        (mapQ k cs).1.get ⟨j.val,by simpa only [mapQ_length] using j.isLt⟩ := hh
    _ = (k (cs.get j)).1 := by
      have he := native_list_get_transport (mapQ k cs).1
        (cs.map (fun a => (k a).1)) (mapQ_value k cs) j.val
        (by simpa only [mapQ_length] using j.isLt)
        (by simpa only [List.length_map] using j.isLt)
      exact he.trans hm
    _ = (k c).1 := congrArg (fun a => (k a).1) hj
theorem rxRows_codes (F : Frame) (m : ℕ) :
    ((rxFrameQ F m).1.faces.map FaceRow.code)=(dedupQ (rxFaceCodesQ F m).1).1 := by
  simp only [rxFrameQ,packFrameQ,mapQ_value,List.map_map,indexFaceQ]
  exact List.map_id _
noncomputable def rxRefines {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (A : TannerSquareAdmissible P) (S : OddScale) :
    Refines (rxFrameQ F S.half).1 (rxReplacementPresentation P S) := by
  let xs := (dedupQ (rxXCodesQ F S.half).1).1
  let qs := (dedupQ (rxQCodesQ F S.half).1).1
  let zs := (dedupQ (rxZCodesQ F S.half).1).1
  let fs := (dedupQ (rxFaceCodesQ F S.half).1).1
  have cx : ∀c,c∈xs ↔ ∃a : RX0 P S,encodeRX0 r S a=c := by
    intro c; exact (dedupQ_mem _ _).trans (rxXCodes_cover r A S c)
  have cq : ∀c,c∈qs ↔ ∃a : RX1 P S,encodeRX1 r S a=c := by
    intro c; exact (dedupQ_mem _ _).trans (rxQCodes_cover r A S c)
  have cz : ∀c,c∈zs ↔ ∃a : RX2 P S,encodeRX2 r S a=c := by
    intro c; exact (dedupQ_mem _ _).trans (rxZCodes_cover r A S c)
  have cf : ∀c,c∈fs ↔ ∃a : RXFace P S,encodeRXFace r S a=c := by
    intro c; exact (dedupQ_mem _ _).trans (rxFaceCodes_cover r A S c)
  let ix := listIndexEquiv xs (encodeRX0 r S) (encodeRX0_injective r A S) (dedupQ_nodup _) cx
  let iq := listIndexEquiv qs (encodeRX1 r S) (encodeRX1_injective r A S) (dedupQ_nodup _) cq
  let iz := listIndexEquiv zs (encodeRX2 r S) (encodeRX2_injective r A S) (dedupQ_nodup _) cz
  let ifc := listIndexEquiv fs (encodeRXFace r S) (encodeRXFace_injective r A S) (dedupQ_nodup _) cf
  let row := fun c =>
    let points := faceEndpointsQ F S.half c
    let out := indexFaceQ xs qs zs c points.1
    (out.1,points.2+out.2)
  have hlen : fs.length=(mapQ row fs).1.length := (mapQ_length row fs).symm
  let iff := ifc.trans (finLengthEquiv hlen)
  have rows (f : RXFace P S) :
      (faceAtQ (mapQ row fs).1 (iff f).val).1=
        (indexFaceQ xs qs zs (encodeRXFace r S f)
          ⟨encodeRX0 r S (rxFaceX P S f),encodeRX2 r S (rxFaceZ P S f),
            encodeRX1 r S (rxFaceQ P S f 0),encodeRX1 r S (rxFaceQ P S f 1)⟩).1 := by
    have hf : encodeRXFace r S f∈fs := (cf _).mpr ⟨f,rfl⟩
    have h := faceAtQ_map_handle row fs (encodeRXFace r S f) hf
    have hiv : (iff f).val=(handleQ (encodeRXFace r S f) fs).1 := by
      change (finLengthEquiv hlen (ifc f)).val=(handleQ (encodeRXFace r S f) fs).1
      rw [finLengthEquiv_val]
      rfl
    rw [hiv]
    calc
      (faceAtQ (mapQ row fs).1 (handleQ (encodeRXFace r S f) fs).1).1 =
          (row (encodeRXFace r S f)).1 := h
      _ = _ := by dsimp only [row]; rw [faceEndpoints_correct]
  refine {
    xIndex:=ix,qIndex:=iq,zIndex:=iz,fIndex:=iff
    x_length:=rfl,q_length:=rfl,z_length:=rfl,f_length:=rfl
    x_nodup:=dedupQ_nodup _,q_nodup:=dedupQ_nodup _,z_nodup:=dedupQ_nodup _
    f_nodup:=?_,face_x:=?_,face_z:=?_,face_q0:=?_,face_q1:=?_ }
  · rw [rxRows_codes]; exact dedupQ_nodup _
  · intro f
    change (faceAtQ (mapQ row fs).1 (iff f).val).1.x=(ix (rxFaceX P S f)).val
    exact congrArg FaceRow.x (rows f)
  · intro f
    change (faceAtQ (mapQ row fs).1 (iff f).val).1.z=(iz (rxFaceZ P S f)).val
    exact congrArg FaceRow.z (rows f)
  · intro f
    change (faceAtQ (mapQ row fs).1 (iff f).val).1.q0=(iq (rxFaceQ P S f 0)).val
    exact congrArg FaceRow.q0 (rows f)
  · intro f
    change (faceAtQ (mapQ row fs).1 (iff f).val).1.q1=(iq (rxFaceQ P S f 1)).val
    exact congrArg FaceRow.q1 (rows f)
theorem faceAtQ_transpose (F : Frame) (i : Fin F.nf) (hlen : F.faces.length=F.nf) :
    (faceAtQ (transposeFrameQ F).1.faces i.val).1=
      let f := (faceAtQ F.faces i.val).1
      ⟨f.code,f.z,f.x,f.q0,f.q1⟩ := by
  let j : Fin F.faces.length := ⟨i.val,by simpa only [hlen] using i.isLt⟩
  let swap (f : FaceRow) : FaceRow := ⟨f.code,f.z,f.x,f.q0,f.q1⟩
  have h := faceAtQ_get F.faces j
  have ht := faceAtQ_get (transposeFrameQ F).1.faces
    (⟨j.val,by simpa only [transposeFrameQ,mapQ_length] using j.isLt⟩)
  have hm := native_list_get_map swap F.faces j.val j.isLt
  calc
    (faceAtQ (transposeFrameQ F).1.faces i.val).1 =
        (transposeFrameQ F).1.faces.get ⟨j.val,by simpa only [transposeFrameQ,mapQ_length] using j.isLt⟩ := ht
    _ = swap (F.faces.get j) := by
      change (mapQ (fun f => (swap f,17)) F.faces).1.get _ = swap (F.faces.get j)
      have he := native_list_get_transport (mapQ (fun f => (swap f,17)) F.faces).1
        (F.faces.map swap) (mapQ_value (fun f => (swap f,17)) F.faces) j.val
        (by simpa only [mapQ_length] using j.isLt)
        (by simpa only [List.length_map] using j.isLt)
      exact he.trans hm
    _ = swap (faceAtQ F.faces i.val).1 := congrArg swap h.symm
noncomputable def transposeRefines {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) : Refines (transposeFrameQ F).1 (transposePresentation P) where
  xIndex:=r.zIndex
  qIndex:=r.qIndex
  zIndex:=r.xIndex
  fIndex:=r.fIndex
  x_length:=r.z_length
  q_length:=r.q_length
  z_length:=r.x_length
  f_length:=by simpa only [transposeFrameQ,mapQ_length] using r.f_length
  x_nodup:=r.z_nodup
  q_nodup:=r.q_nodup
  z_nodup:=r.x_nodup
  f_nodup:=by simpa only [transposeFrameQ,mapQ_value,List.map_map,Function.comp_def] using r.f_nodup
  face_x:=by
    intro f
    change (faceAtQ (transposeFrameQ F).1.faces (r.fIndex f).val).1.x=(r.zIndex (P.faceZ f)).val
    rw [faceAtQ_transpose F (r.fIndex f) r.f_length]
    exact r.face_z f
  face_z:=by
    intro f
    change (faceAtQ (transposeFrameQ F).1.faces (r.fIndex f).val).1.z=(r.xIndex (P.faceX f)).val
    rw [faceAtQ_transpose F (r.fIndex f) r.f_length]
    exact r.face_x f
  face_q0:=by
    intro f
    change (faceAtQ (transposeFrameQ F).1.faces (r.fIndex f).val).1.q0=(r.qIndex (P.faceQ f 0)).val
    rw [faceAtQ_transpose F (r.fIndex f) r.f_length]
    exact r.face_q0 f
  face_q1:=by
    intro f
    change (faceAtQ (transposeFrameQ F).1.faces (r.fIndex f).val).1.q1=(r.qIndex (P.faceQ f 1)).val
    rw [faceAtQ_transpose F (r.fIndex f) r.f_length]
    exact r.face_q1 f
def rzXEquiv (P : TannerSquarePresentation) (S : OddScale) :
    BDL26RZLocalReplacement.RZX P S ≃ RX2 (transposePresentation P) S := Equiv.refl _
def rzQEquiv (P : TannerSquarePresentation) (S : OddScale) :
    BDL26RZLocalReplacement.RZQ P S ≃ RX1 (transposePresentation P) S := Equiv.refl _
def rzZEquiv (P : TannerSquarePresentation) (S : OddScale) :
    BDL26RZLocalReplacement.RZZ P S ≃ RX0 (transposePresentation P) S := Equiv.refl _
theorem rz_raw_edge (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (z : P.Z) (hz : P.qz q z=true) (S : OddScale)
    (e : QDoubleCylinderEdge (transposePresentation P) q S) :
    qToZDoubleCylinderEdge P A q z hz S e=
      qToXDoubleCylinderEdgeRaw (transposePresentation P) q z hz S e := by
  cases e with
  | inl e =>
      rcases e with ⟨copy,edge,i⟩
      have hb : (transposeXStarBoundaryEdgeEquiv P z).symm
          (qToZBoundaryEdge P q z hz edge)=
          qToXBoundaryEdge (transposePresentation P) q z hz edge := by
        apply Subtype.ext
        rfl
      simp only [qToZDoubleCylinderEdge,qToZSubdivisionBoundaryEdge,
        qToXDoubleCylinderEdgeRaw,qToXSubdivisionBoundaryEdge,hb]
  | inr edge =>
      have hv : (transposeXStarBoundaryVertexEquiv P z).symm
          (qToZBoundaryVertex P A q z hz (.inr edge))=
          xBoundaryEdgeEnd (transposePresentation P) z
            (qToXBoundaryEdge (transposePresentation P) q z hz edge) := by
        apply Subtype.ext
        rfl
      simp only [qToZDoubleCylinderEdge,qToXDoubleCylinderEdgeRaw,hv]
theorem rz_raw_vertex_endpoint (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (z : P.Z) (hz : P.qz q z=true)
    (S : OddScale) (e : QDoubleCylinderEdge (transposePresentation P) q S) (d : Two) :
    qToZDoubleCylinderVertex P A q z hz S
      (BDL26TannerLocalRegularity.edgeEndpoint (qDoubleCylinderEdgeStart (transposePresentation P) q S)
        (qDoubleCylinderEdgeEnd (transposePresentation P) q S) e d)=
      BDL26TannerLocalRegularity.edgeEndpoint (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
        (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
        (qToXDoubleCylinderEdgeRaw (transposePresentation P) q z hz S e) d := by
  rw [←rz_raw_edge P A q z hz S e]
  fin_cases d
  · change qToZDoubleCylinderVertex P A q z hz S
        (qDoubleCylinderEdgeStart (transposePresentation P) q S e) =
        tannerDoubleCylinderEdgeStart (transposePresentation P) z S
          (qToZDoubleCylinderEdge P A q z hz S e)
    exact qToZDoubleCylinderEdge_start P A q z hz S e
  · change qToZDoubleCylinderVertex P A q z hz S
        (qDoubleCylinderEdgeEnd (transposePresentation P) q S e) =
        tannerDoubleCylinderEdgeEnd (transposePresentation P) z S
          (qToZDoubleCylinderEdge P A q z hz S e)
    exact qToZDoubleCylinderEdge_end P A q z hz S e
theorem rz_face_endpoints (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale)
    (f : BDL26RZLocalReplacement.RZFace P S) :
    rzXEquiv P S (BDL26RZLocalReplacement.rzFaceX P S f)=
      rxFaceZ (transposePresentation P) S (rzFaceEquiv P S f) ∧
    rzZEquiv P S (BDL26RZLocalReplacement.rzFaceZ P A S f)=
      rxFaceX (transposePresentation P) S (rzFaceEquiv P S f) ∧
    ∀d,rzQEquiv P S (BDL26RZLocalReplacement.rzFaceQ P A S f d)=
      rxFaceQ (transposePresentation P) S (rzFaceEquiv P S f) d := by
  cases f with
  | inl f =>
      exact ⟨BDL26ReplacementEmbedding.rzFaceX_transpose P S (.inl f),
        BDL26ReplacementEmbedding.rzFaceZ_transpose P A S (.inl f),
        BDL26ReplacementEmbedding.rzFaceQ_transpose P A S (.inl f)⟩
  | inr f =>
      cases f with
      | inl f =>
          rcases f with ⟨a,e,d⟩
          refine ⟨BDL26ReplacementEmbedding.rzFaceX_transpose P S (.inr (.inl ⟨a,e,d⟩)),?_,?_⟩
          · change (⟨a.1.2,qToZDoubleCylinderVertex P A a.1.1 a.1.2 a.2 S
                (BDL26RZLocalReplacement.edgeEndpoint
                  (qDoubleCylinderEdgeStart (transposePresentation P) a.1.1 S)
                  (qDoubleCylinderEdgeEnd (transposePresentation P) a.1.1 S) e d)⟩ :
                RX0 (transposePresentation P) S)=
              ⟨a.1.2,BDL26RXLocalReplacement.edgeEndpoint
                (tannerDoubleCylinderEdgeStart (transposePresentation P) a.1.2 S)
                (tannerDoubleCylinderEdgeEnd (transposePresentation P) a.1.2 S)
                (qToXDoubleCylinderEdgeRaw (transposePresentation P) a.1.1 a.1.2 a.2 S e) d⟩
            apply congrArg (fun v : DoubleCylinderVertex (transposePresentation P) a.1.2 S =>
              (⟨a.1.2,v⟩ : RX0 (transposePresentation P) S))
            rw [rz_endpoint_eq,rx_endpoint_eq]
            exact rz_raw_vertex_endpoint P A a.1.1 a.1.2 a.2 S e d
          · intro c
            fin_cases c
            · change (Sum.inl ⟨a.1.2,qToZDoubleCylinderEdge P A a.1.1 a.1.2 a.2 S e⟩ :
                  RX1 (transposePresentation P) S)=
                Sum.inl ⟨a.1.2,qToXDoubleCylinderEdgeRaw (transposePresentation P) a.1.1 a.1.2 a.2 S e⟩
              exact congrArg (fun edge : DoubleCylinderEdge (transposePresentation P) a.1.2 S =>
                (Sum.inl ⟨a.1.2,edge⟩ : RX1 (transposePresentation P) S))
                  (rz_raw_edge P A a.1.1 a.1.2 a.2 S e)
            · rfl
      | inr f =>
          exact ⟨BDL26ReplacementEmbedding.rzFaceX_transpose P S (.inr (.inr f)),
            BDL26ReplacementEmbedding.rzFaceZ_transpose P A S (.inr (.inr f)),
            BDL26ReplacementEmbedding.rzFaceQ_transpose P A S (.inr (.inr f))⟩
noncomputable def rzRefines {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (A : TannerSquareAdmissible P) (S : OddScale) :
    Refines (rzFrameQ F S.half).1 (BDL26RZLocalReplacement.rzReplacementPresentation P A S) := by
  let rt := transposeRefines (rxRefines (transposeRefines r)
    (transposeTannerSquareAdmissible P A) S)
  refine {rt with
    xIndex:=(rzXEquiv P S).trans rt.xIndex
    qIndex:=(rzQEquiv P S).trans rt.qIndex
    zIndex:=(rzZEquiv P S).trans rt.zIndex
    fIndex:=(rzFaceEquiv P S).trans rt.fIndex
    face_x:=?_,face_z:=?_,face_q0:=?_,face_q1:=?_}
  · intro f
    change (faceAtQ (transposeFrameQ (rxFrameQ (transposeFrameQ F).1 S.half).1).1.faces
      (rt.fIndex (rzFaceEquiv P S f)).val).1.x=
      (rt.xIndex (rzXEquiv P S (BDL26RZLocalReplacement.rzFaceX P S f))).val
    rw [(rz_face_endpoints P A S f).1]
    exact rt.face_x (rzFaceEquiv P S f)
  · intro f
    change (faceAtQ (transposeFrameQ (rxFrameQ (transposeFrameQ F).1 S.half).1).1.faces
      (rt.fIndex (rzFaceEquiv P S f)).val).1.z=
      (rt.zIndex (rzZEquiv P S (BDL26RZLocalReplacement.rzFaceZ P A S f))).val
    rw [(rz_face_endpoints P A S f).2.1]
    exact rt.face_z (rzFaceEquiv P S f)
  · intro f
    change (faceAtQ (transposeFrameQ (rxFrameQ (transposeFrameQ F).1 S.half).1).1.faces
      (rt.fIndex (rzFaceEquiv P S f)).val).1.q0=
      (rt.qIndex (rzQEquiv P S (BDL26RZLocalReplacement.rzFaceQ P A S f 0))).val
    rw [(rz_face_endpoints P A S f).2.2 0]
    exact rt.face_q0 (rzFaceEquiv P S f)
  · intro f
    change (faceAtQ (transposeFrameQ (rxFrameQ (transposeFrameQ F).1 S.half).1).1.faces
      (rt.fIndex (rzFaceEquiv P S f)).val).1.q1=
      (rt.qIndex (rzQEquiv P S (BDL26RZLocalReplacement.rzFaceQ P A S f 1))).val
    rw [(rz_face_endpoints P A S f).2.2 1]
    exact rt.face_q1 (rzFaceEquiv P S f)
theorem lastFrame_append (fs : List Frame) (f : Frame) :
    (lastFrameQ (fs++[f])).1=f := by
  induction fs with
  | nil => rfl
  | cons a as ih =>
      cases as with
      | nil => rfl
      | cons b bs => exact ih
theorem generateQ_succ (S : OddScale) (n : ℕ) :
    (generateQ S (n+1)).1=(nextFrameQ S n (generateQ S n).1).1 := by
  change (lastFrameQ ((historyQ S n).1++[(nextFrameQ S n
    (lastFrameQ (historyQ S n).1).1).1])).1=_
  rw [lastFrame_append]
  rfl
noncomputable def generatedRefines (S : OddScale) :
    (n : ℕ) → Refines (generateQ S n).1 (state S n).presentation
  | 0 => seedRefines
  | n+1 => by
      rw [generateQ_succ]
      change Refines (nextFrameQ S n (generateQ S n).1).1
        (nextState S n (state S n)).presentation
      by_cases hn : n%2=0
      · simpa only [nextFrameQ,nextState,hn,ite_true,rxState] using
          rxRefines (generatedRefines S n) (state S n).admissible.toTannerSquareAdmissible S
      · simpa only [nextFrameQ,nextState,hn,ite_false,rzState] using
          rzRefines (generatedRefines S n) (state S n).admissible.toTannerSquareAdmissible S
def nativeXQ (F : Frame) : Matrix (Fin F.nx) (Fin F.nq) BDL26FiniteTannerSquare.Field :=
  fun x q => if (xqQ F x.val q.val).1 then 1 else 0
def nativeQZ (F : Frame) : Matrix (Fin F.nq) (Fin F.nz) BDL26FiniteTannerSquare.Field :=
  fun q z => if (qzQ F q.val z.val).1 then 1 else 0
def triangleCodesQ (F : Frame) : Query (List Code) :=
  let raw := loopQ F.nf (fun f => mapQ (fun d => emitQ {family:=3,owner:=f,copy:=d}) [0,1])
  let unique := dedupQ raw.1
  (unique.1,raw.2+unique.2)
structure SetupOutput where
  data : Output
  triangles : List Code
  seedRows : List SeedRow
  deriving Repr
def setupQ (S : OddScale) (n : ℕ) : Query SetupOutput :=
  let data := runQ S n
  let triangles := triangleCodesQ data.1.frame
  let initial := seedRowsQ
  (⟨data.1,triangles.1,initial.1⟩,data.2+triangles.2+initial.2+5)
theorem denseXQQ_mem (F : Frame) (x q : ℕ) (b : Bool) :
    (x,q,b)∈(denseXQQ F).1 ↔ x< F.nx ∧ q< F.nq ∧ b=(xqQ F x q).1 := by
  simp only [denseXQQ,loopQ_value,flatMapQ_value,List.mem_flatMap,mapQ_value,List.mem_map,
    rangeQ_value,List.mem_range,Prod.mk.injEq]
  aesop
theorem denseQZQ_mem (F : Frame) (q z : ℕ) (b : Bool) :
    (q,z,b)∈(denseQZQ F).1 ↔ q< F.nq ∧ z< F.nz ∧ b=(qzQ F q z).1 := by
  simp only [denseQZQ,loopQ_value,flatMapQ_value,List.mem_flatMap,mapQ_value,List.mem_map,
    rangeQ_value,List.mem_range,Prod.mk.injEq]
  aesop
def encodeVertex {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) : Vertex P → Code
  | .x x => {owner:=(r.xIndex x).val}
  | .q q => {family:=1,owner:=(r.qIndex q).val}
  | .z z => {family:=2,owner:=(r.zIndex z).val}
def encodeEdge {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) : Edge P → Code
  | .inl e => {owner:=(r.xIndex e.1.1).val,p:=(r.qIndex e.1.2).val}
  | .inr e => {family:=1,owner:=(r.qIndex e.1.1).val,p:=(r.zIndex e.1.2).val}
theorem vertexCodes_cover {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (c : Code) :
    c∈(vertexCodesQ F).1 ↔ ∃v : Vertex P,encodeVertex r v=c := by
  simp only [vertexCodesQ,dedupQ_mem,collectQ_cons_value,collectQ_nil_value,List.mem_append,List.not_mem_nil,
    or_false,loopQ_mem,singletonQ,List.mem_singleton]
  constructor
  · rintro (⟨i,hi,hc⟩|⟨i,hi,hc⟩|⟨i,hi,hc⟩)
    · exact ⟨.x (r.xIndex.symm ⟨i,hi⟩),by simpa [encodeVertex] using hc.symm⟩
    · exact ⟨.q (r.qIndex.symm ⟨i,hi⟩),by simpa [encodeVertex] using hc.symm⟩
    · exact ⟨.z (r.zIndex.symm ⟨i,hi⟩),by simpa [encodeVertex] using hc.symm⟩
  · rintro ⟨v,rfl⟩
    cases v with
    | x x => exact Or.inl ⟨_,(r.xIndex x).isLt,rfl⟩
    | q q => exact Or.inr (Or.inl ⟨_,(r.qIndex q).isLt,rfl⟩)
    | z z => exact Or.inr (Or.inr ⟨_,(r.zIndex z).isLt,rfl⟩)
theorem edgeCodes_cover {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (A : TannerSquareAdmissible P) (c : Code) :
    c∈(edgeCodesQ F).1 ↔ ∃e : Edge P,encodeEdge r e=c := by
  simp only [edgeCodesQ,dedupQ_mem,collectQ_cons_value,collectQ_nil_value,List.mem_append,List.not_mem_nil,
    or_false,mapQ_value,List.mem_map,filterQ_value,List.mem_filter,emitQ]
  constructor
  · rintro (⟨⟨x,q,b⟩,⟨hrow,hb⟩,hc⟩|⟨⟨q,z,b⟩,⟨hrow,hb⟩,hc⟩)
    · obtain ⟨hx,hq,hb'⟩ := (denseXQQ_mem F x q b).mp hrow
      let a := r.xIndex.symm ⟨x,hx⟩
      let b' := r.qIndex.symm ⟨q,hq⟩
      have ha : (r.xIndex a).val=x := by simp [a]
      have hq' : (r.qIndex b').val=q := by simp [b']
      have hxq : P.xq a b'=true := by
        rw [←refines_xq r A,ha,hq',←hb']; exact hb
      exact ⟨.inl ⟨(a,b'),hxq⟩,by simpa [encodeEdge,ha,hq'] using hc⟩
    · obtain ⟨hq,hz,hb'⟩ := (denseQZQ_mem F q z b).mp hrow
      let a := r.qIndex.symm ⟨q,hq⟩
      let b' := r.zIndex.symm ⟨z,hz⟩
      have ha : (r.qIndex a).val=q := by simp [a]
      have hz' : (r.zIndex b').val=z := by simp [b']
      have hqz : P.qz a b'=true := by
        rw [←refines_qz r A,ha,hz',←hb']; exact hb
      exact ⟨.inr ⟨(a,b'),hqz⟩,by simpa [encodeEdge,ha,hz'] using hc⟩
  · rintro ⟨e,rfl⟩
    cases e with
    | inl e => exact Or.inl ⟨(_,_,true),⟨(denseXQQ_mem F _ _ true).mpr
        ⟨(r.xIndex e.1.1).isLt,(r.qIndex e.1.2).isLt,
          by rw [refines_xq r A,e.2]⟩,rfl⟩,rfl⟩
    | inr e => exact Or.inr ⟨(_,_,true),⟨(denseQZQ_mem F _ _ true).mpr
        ⟨(r.qIndex e.1.1).isLt,(r.zIndex e.1.2).isLt,
          by rw [refines_qz r A,e.2]⟩,rfl⟩,rfl⟩
theorem encodeVertex_injective {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) : Function.Injective (encodeVertex r) := by
  intro a b h
  have hf := congrArg Code.family h
  have ho := congrArg Code.owner h
  cases a <;> cases b <;> simp only [encodeVertex,index_val_eq] at hf ho
  all_goals first | omega | (subst_vars; rfl)
theorem encodeEdge_injective {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) : Function.Injective (encodeEdge r) := by
  intro a b h
  have hf := congrArg Code.family h
  have ho := congrArg Code.owner h
  have hp := congrArg Code.p h
  cases a <;> cases b <;> simp only [encodeEdge,index_val_eq] at hf ho hp
  all_goals first | omega | (congr 1; exact Subtype.ext (Prod.ext ho hp))
noncomputable def vertexIndex {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) : Vertex P ≃ Fin (vertexCodesQ F).1.length :=
  listIndexEquiv _ (encodeVertex r) (encodeVertex_injective r)
    (by exact dedupQ_nodup _) (vertexCodes_cover r)
noncomputable def edgeIndex {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (A : TannerSquareAdmissible P) : Edge P ≃ Fin (edgeCodesQ F).1.length :=
  listIndexEquiv _ (encodeEdge r) (encodeEdge_injective r)
    (by exact dedupQ_nodup _) (edgeCodes_cover r A)
noncomputable def generatedVertexIndex (S : OddScale) (n : ℕ) :
    Vertex (state S n).presentation ≃ Fin (runQ S n).1.vertices.length :=
  vertexIndex (generatedRefines S n)
noncomputable def generatedEdgeIndex (S : OddScale) (n : ℕ) :
    Edge (state S n).presentation ≃ Fin (runQ S n).1.edges.length :=
  edgeIndex (generatedRefines S n) (state S n).admissible.toTannerSquareAdmissible
def NativeFaceOver (F : Frame) (x : Fin F.nx) (z : Fin F.nz) :=
  {f : Fin F.nf // (faceAtQ F.faces f.val).1.x=x.val ∧ (faceAtQ F.faces f.val).1.z=z.val}
def NativeSharedQ (F : Frame) (x : Fin F.nx) (z : Fin F.nz) :=
  {q : Fin F.nq // (xqQ F x.val q.val).1 && (qzQ F q.val z.val).1=true}
noncomputable def faceFiberEquiv {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (x : P.X) (z : P.Z) :
    FaceOver P.data x z ≃ NativeFaceOver F (r.xIndex x) (r.zIndex z) where
  toFun f:=⟨r.fIndex f.1,by
    constructor
    · exact (r.face_x f.1).trans (congrArg (fun a => (r.xIndex a).val) f.2.1)
    · exact (r.face_z f.1).trans (congrArg (fun a => (r.zIndex a).val) f.2.2)⟩
  invFun f:=⟨r.fIndex.symm f.1,by
    have hx := r.face_x (r.fIndex.symm f.1)
    have hz := r.face_z (r.fIndex.symm f.1)
    simp only [Equiv.apply_symm_apply] at hx hz
    exact ⟨(index_val_eq r.xIndex _ _).mp (hx.symm.trans f.2.1),
      (index_val_eq r.zIndex _ _).mp (hz.symm.trans f.2.2)⟩⟩
  left_inv f:=Subtype.ext (r.fIndex.symm_apply_apply f.1)
  right_inv f:=Subtype.ext (r.fIndex.apply_symm_apply f.1)
noncomputable def sharedFiberEquiv {F : Frame} {P : TannerSquarePresentation}
    (r : Refines F P) (A : TannerSquareAdmissible P) (x : P.X) (z : P.Z) :
    SharedQ P.data x z ≃ NativeSharedQ F (r.xIndex x) (r.zIndex z) where
  toFun q:=⟨r.qIndex q.1,by
    change (xqQ F (r.xIndex x).val (r.qIndex q.1).val).1 &&
      (qzQ F (r.qIndex q.1).val (r.zIndex z).val).1=true
    rw [refines_xq r A,refines_qz r A]
    have hb (b : Bool) : decide (b=true)=b := by cases b <;> rfl
    simpa only [hb] using q.2⟩
  invFun q:=⟨r.qIndex.symm q.1,by
    have h := q.2
    rw [←r.qIndex.apply_symm_apply q.1] at h
    rw [refines_xq r A,refines_qz r A] at h
    have hb (b : Bool) : decide (b=true)=b := by cases b <;> rfl
    simpa only [hb] using h⟩
  left_inv q:=Subtype.ext (r.qIndex.symm_apply_apply q.1)
  right_inv q:=Subtype.ext (r.qIndex.apply_symm_apply q.1)
noncomputable def generatedPairing (S : OddScale) (n : ℕ)
    (x : (state S n).presentation.X) (z : (state S n).presentation.Z) :
    NativeFaceOver (generateQ S n).1 ((generatedRefines S n).xIndex x)
      ((generatedRefines S n).zIndex z) × Two ≃
    NativeSharedQ (generateQ S n).1 ((generatedRefines S n).xIndex x)
      ((generatedRefines S n).zIndex z) :=
  ((Equiv.prodCongr (faceFiberEquiv (generatedRefines S n) x z) (Equiv.refl Two)).symm.trans
    ((state S n).presentation.faceCornerEquiv x z)).trans
      (sharedFiberEquiv (generatedRefines S n) (state S n).admissible.toTannerSquareAdmissible x z)
def nativeBoundary1 (F : Frame) :
    Matrix (Fin (vertexCodesQ F).1.length) (Fin (edgeCodesQ F).1.length) BDL26FiniteTannerSquare.Field :=
  fun v e => if (edgeVertexTestQ ((edgeCodesQ F).1.get e) ((vertexCodesQ F).1.get v)).1 then 1 else 0
def nativeBoundary2 (F : Frame) :
    Matrix (Fin (edgeCodesQ F).1.length) (Fin F.nf) BDL26FiniteTannerSquare.Field :=
  fun e f => if (faceEdgeTestQ (faceAtQ F.faces f.val).1 ((edgeCodesQ F).1.get e)).1 then 1 else 0
def work {A : Type*} (q : Query (List A)) : ℕ := q.1.length+q.2+1
noncomputable def inputRadius (S : OddScale) (n : ℕ) : ℕ :=
  S.ell+130*Fintype.card (state S n).presentation.Q+2
def frameRecords (F : Frame) : ℕ :=
  11*(F.xs.length+F.qs.length+F.zs.length)+15*F.faces.length+9
def prefixRecords (S : OddScale) (n : ℕ) : ℕ :=
  ((historyQ S n).1.map frameRecords).sum+(historyQ S n).1.length
def setupExponent : ℕ := 205+15
def outputRecords (o : SetupOutput) : ℕ :=
  frameRecords o.data.frame + 4*(o.data.xq.length+o.data.qz.length+
    o.data.boundary1.length+o.data.boundary2.length) +
    11*(o.data.vertices.length+o.data.edges.length+o.triangles.length)+
    7*o.seedRows.length+30
namespace Allocation
def mapQ {A B : Type*} (f : A → Query B) : List A → Query (List B)
  | [] => ([],0)
  | a::as =>
      let x := f a
      let xs := mapQ f as
      (x.1::xs.1,x.2+xs.2+1)
def filterQ {A : Type*} (p : A → Query Bool) : List A → Query (List A)
  | [] => ([],0)
  | a::as =>
      let h := p a
      let xs := filterQ p as
      (if h.1 then a::xs.1 else xs.1,h.2+xs.2+1)
def rangeQ : ℕ → Query (List ℕ)
  | 0 => ([],0)
  | n+1 =>
      let r := rangeQ n
      (r.1++[n],r.2+r.1.length+1)
def appendQ {A : Type*} (a b : List A) : Query (List A) := (a++b,a.length)
def flattenQ {A : Type*} : List (List A) → Query (List A)
  | [] => ([],0)
  | a::as =>
      let xs := flattenQ as
      let out := appendQ a xs.1
      (out.1,xs.2+out.2+1)
def productQ {A B : Type*} (a : List A) (b : List B) : Query (List (A × B)) :=
  let rows := mapQ (fun x => mapQ (fun y => ((x,y),1)) b) a
  let out := flattenQ rows.1
  (out.1,rows.2+out.2)
def equalCodeQ (a b : Code) : Query Bool := (decide (a=b),0)
def handleQ (c : Code) : List Code → Query ℕ
  | [] => (0,0)
  | a::as =>
      let h := equalCodeQ c a
      if h.1 then (0,h.2) else
        let r := handleQ c as
        (r.1+1,h.2+r.2)
def xqFaceTestQ (x q : ℕ) (f : FaceRow) : Query Bool :=
  (decide (f.x=x ∧ (f.q0=q ∨ f.q1=q)),0)
def qzFaceTestQ (q z : ℕ) (f : FaceRow) : Query Bool :=
  (decide (f.z=z ∧ (f.q0=q ∨ f.q1=q)),0)
def anyQ {A : Type*} (p : A → Query Bool) : List A → Query Bool
  | [] => (false,0)
  | a::as =>
      let h := p a
      let hs := anyQ p as
      (h.1 || hs.1,h.2+hs.2)
def xqQ (F : Frame) (x q : ℕ) : Query Bool := anyQ (xqFaceTestQ x q) F.faces
def qzQ (F : Frame) (q z : ℕ) : Query Bool := anyQ (qzFaceTestQ q z) F.faces
def seedFrameQ : Query Frame :=
  (seedFrame,31)
def flatMapQ {A B : Type*} (f : A → Query (List B)) : List A → Query (List B)
  | [] => ([],0)
  | a::as =>
      let r := f a
      let rs := flatMapQ f as
      let out := appendQ r.1 rs.1
      (out.1,r.2+rs.2+out.2+1)
def collectQ {A : Type*} (qs : List (Query (List A))) : Query (List A) :=
  flatMapQ id qs
def emitQ (c : Code) : Query Code := (c,1)
def singletonQ (c : Code) : Query (List Code) := ([c],2)
def loopQ {A : Type*} (n : ℕ) (f : ℕ → Query (List A)) : Query (List A) :=
  let ids := rangeQ n
  let out := flatMapQ f ids.1
  (out.1,ids.2+out.2)
def mapCodesQ (f : Code → Code) (xs : List Code) : Query (List Code) :=
  mapQ (fun c => emitQ (f c)) xs
def facesAtXQ (F : Frame) (x : ℕ) : Query (List (ℕ × FaceRow)) :=
  let ids := rangeQ F.nf
  let rows := mapQ (fun i => ((i,F.faces[i]?.getD ⟨{},0,0,0,0⟩),1)) ids.1
  let out := filterQ (fun r => (decide (r.2.x=x),0)) rows.1
  (out.1,ids.2+rows.2+out.2)
def starQsQ (F : Frame) (x : ℕ) : Query (List ℕ) :=
  let ids := rangeQ F.nq
  let out := filterQ (xqQ F x) ids.1
  (out.1,ids.2+out.2)
def starZsQ (F : Frame) (x : ℕ) : Query (List ℕ) :=
  let ids := rangeQ F.nz
  let out := filterQ (fun z => anyQ (fun f : FaceRow =>
    (decide (f.x=x ∧ f.z=z),0)) F.faces) ids.1
  (out.1,ids.2+out.2)
def starSidesQ (F : Frame) (x : ℕ) : Query (List (ℕ × ℕ)) :=
  let qs := rangeQ F.nq
  let zs := rangeQ F.nz
  let pairs := productQ qs.1 zs.1
  let out := filterQ (fun e => anyQ (fun f : FaceRow =>
    (decide (f.x=x ∧ f.z=e.2 ∧ (f.q0=e.1 ∨ f.q1=e.1)),0)) F.faces) pairs.1
  (out.1,qs.2+zs.2+pairs.2+out.2)
def subVerticesQ (F : Frame) (x m : ℕ) : Query (List Code) :=
  let qs := starQsQ F x
  let zs := starZsQ F x
  let sides := starSidesQ F x
  let faces := facesAtXQ F x
  let qv := mapQ (fun q => emitQ {owner:=x,part:=1,p:=q}) qs.1
  let zv := mapQ (fun z => emitQ {owner:=x,part:=2,p:=z}) zs.1
  let radial := flatMapQ (fun q => loopQ (m-1) (fun i =>
    singletonQ {owner:=x,part:=3,p:=q,i:=i})) qs.1
  let side := flatMapQ (fun e => loopQ (m-1) (fun i =>
    singletonQ {owner:=x,part:=4,p:=e.1,q:=e.2,i:=i})) sides.1
  let bulk := flatMapQ (fun f => loopQ (m-1) (fun i => loopQ (m-1) (fun j =>
    singletonQ {owner:=x,part:=5,p:=f.1,i:=i,j:=j}))) faces.1
  let out := collectQ [singletonQ {owner:=x},qv,zv,radial,side,bulk]
  (out.1,qs.2+zs.2+sides.2+faces.2+out.2)
def subEdgesQ (F : Frame) (x m : ℕ) : Query (List Code) :=
  let qs := starQsQ F x
  let sides := starSidesQ F x
  let faces := facesAtXQ F x
  let radial := flatMapQ (fun q => loopQ m (fun i =>
    singletonQ {owner:=x,p:=q,i:=i})) qs.1
  let side := flatMapQ (fun e => loopQ m (fun i =>
    singletonQ {owner:=x,part:=1,p:=e.1,q:=e.2,i:=i})) sides.1
  let horizontal := flatMapQ (fun f => loopQ m (fun i => loopQ (m-1) (fun j =>
    singletonQ {owner:=x,part:=2,p:=f.1,i:=i,j:=j}))) faces.1
  let vertical := flatMapQ (fun f => loopQ (m-1) (fun i => loopQ m (fun j =>
    singletonQ {owner:=x,part:=3,p:=f.1,i:=i,j:=j}))) faces.1
  let out := collectQ [radial,side,horizontal,vertical]
  (out.1,qs.2+sides.2+faces.2+out.2)
def subFacesQ (F : Frame) (x m : ℕ) : Query (List Code) :=
  let faces := facesAtXQ F x
  let out := flatMapQ (fun f => loopQ m (fun i => loopQ m (fun j =>
    singletonQ {owner:=x,p:=f.1,i:=i,j:=j}))) faces.1
  (out.1,faces.2+out.2)
def doubleVerticesQ (F : Frame) (x m : ℕ) : Query (List Code) :=
  let cells := subVerticesQ F x m
  let copies := flatMapQ (fun c => mapCodesQ (fun v => {v with copy:=c}) cells.1) [0,1]
  (copies.1,cells.2+copies.2)
def doubleEdgesQ (F : Frame) (x m : ℕ) : Query (List Code) :=
  let edges := subEdgesQ F x m
  let vertices := subVerticesQ F x m
  let ends := flatMapQ (fun c => mapCodesQ (fun e => {e with copy:=c}) edges.1) [0,1]
  let boundary := filterQ (fun v => (decide (v.part=1 ∨ v.part=2 ∨ v.part=4),0)) vertices.1
  let bridge := mapCodesQ (fun v =>
    {v with part:=if v.part=1 then 4 else if v.part=2 then 5 else 6}) boundary.1
  let out := collectQ [ends,bridge]
  (out.1,edges.2+vertices.2+boundary.2+out.2)
def doubleFacesQ (F : Frame) (x m : ℕ) : Query (List Code) :=
  let faces := subFacesQ F x m
  let sides := starSidesQ F x
  let ends := flatMapQ (fun c => mapCodesQ (fun f => {f with copy:=c}) faces.1) [0,1]
  let rect := flatMapQ (fun e => loopQ m (fun i =>
    singletonQ {owner:=x,part:=1,p:=e.1,q:=e.2,i:=i})) sides.1
  let out := collectQ [ends,rect]
  (out.1,faces.2+sides.2+out.2)
def qNeighborsQ (F : Frame) (q : ℕ) : Query (List ℕ) :=
  let ids := rangeQ F.nz
  let out := filterQ (qzQ F q) ids.1
  (out.1,ids.2+out.2)
def qDoubleVerticesQ (F : Frame) (q m : ℕ) : Query (List Code) :=
  let ns := qNeighborsQ F q
  let endpoint := mapQ (fun z => emitQ {owner:=q,part:=1,p:=z}) ns.1
  let interior := flatMapQ (fun z => loopQ (m-1) (fun i =>
    singletonQ {owner:=q,part:=2,p:=z,i:=i})) ns.1
  let cells := collectQ [singletonQ {owner:=q},endpoint,interior]
  let out := flatMapQ (fun c => mapCodesQ (fun v => {v with copy:=c}) cells.1) [0,1]
  (out.1,ns.2+cells.2+out.2)
def qDoubleEdgesQ (F : Frame) (q m : ℕ) : Query (List Code) :=
  let ns := qNeighborsQ F q
  let ends := flatMapQ (fun c => flatMapQ (fun z => loopQ m (fun i =>
    singletonQ {owner:=q,copy:=c,p:=z,i:=i})) ns.1) [0,1]
  let vertical := mapQ (fun z => emitQ {owner:=q,part:=1,p:=z}) ns.1
  let out := collectQ [ends,vertical]
  (out.1,ns.2+out.2)
def rxXCodesQ (F : Frame) (m : ℕ) : Query (List Code) :=
  loopQ F.nx (fun x => doubleVerticesQ F x m)
def rxQCodesQ (F : Frame) (m : ℕ) : Query (List Code) :=
  let localPart := loopQ F.nx (fun x => doubleEdgesQ F x m)
  let qlocal := loopQ F.nq (fun q =>
    let cells := qDoubleVerticesQ F q m
    let out := mapCodesQ (fun c => {c with family:=1}) cells.1
    (out.1,cells.2+out.2))
  collectQ [localPart,qlocal]
def rxZCodesQ (F : Frame) (m : ℕ) : Query (List Code) :=
  let localPart := loopQ F.nx (fun x => doubleFacesQ F x m)
  let qlocal := loopQ F.nq (fun q =>
    let cells := qDoubleEdgesQ F q m
    let out := mapCodesQ (fun c => {c with family:=1}) cells.1
    (out.1,cells.2+out.2))
  let old := loopQ F.nz (fun z => mapQ (fun c => emitQ {family:=2,owner:=z,copy:=c}) [0,1])
  collectQ [localPart,qlocal,old]
def faceAtQ : List FaceRow → ℕ → Query FaceRow
  | [], _ => (⟨{},0,0,0,0⟩,0)
  | f::_, 0 => (f,0)
  | _::fs, i+1 => let r := faceAtQ fs i; (r.1,r.2)
def gridVertexQ (F : Frame) (x m f i j : ℕ) : Query Code :=
  let old := faceAtQ F.faces f
  let v : Code :=
    if i=0 then
      if j=0 then {owner:=x}
      else if j=m then {owner:=x,part:=1,p:=old.1.q1}
      else {owner:=x,part:=3,p:=old.1.q1,i:=j-1}
    else if i=m then
      if j=0 then {owner:=x,part:=1,p:=old.1.q0}
      else if j=m then {owner:=x,part:=2,p:=old.1.z}
      else {owner:=x,part:=4,p:=old.1.q0,q:=old.1.z,i:=j-1}
    else if j=0 then {owner:=x,part:=3,p:=old.1.q0,i:=i-1}
    else if j=m then {owner:=x,part:=4,p:=old.1.q1,q:=old.1.z,i:=i-1}
    else {owner:=x,part:=5,p:=f,i:=i-1,j:=j-1}
  (v,old.2+1)
def horizontalEdgeQ (F : Frame) (x m f i j : ℕ) : Query Code :=
  let old := faceAtQ F.faces f
  (if j=0 then {owner:=x,p:=old.1.q0,i:=i}
   else if j=m then {owner:=x,part:=1,p:=old.1.q1,q:=old.1.z,i:=i}
   else {owner:=x,part:=2,p:=f,i:=i,j:=j-1},old.2+1)
def verticalEdgeQ (F : Frame) (x m f i j : ℕ) : Query Code :=
  let old := faceAtQ F.faces f
  (if i=0 then {owner:=x,p:=old.1.q1,i:=j}
   else if i=m then {owner:=x,part:=1,p:=old.1.q0,q:=old.1.z,i:=j}
   else {owner:=x,part:=3,p:=f,i:=i-1,j:=j},old.2+1)
def segmentVertexQ (x m : ℕ) (e : Code) (endpoint : ℕ) : Query Code :=
  let pos := e.i+endpoint
  (if pos=0 then
     if e.part=0 then {owner:=x} else {owner:=x,part:=1,p:=e.p}
   else if pos=m then
     if e.part=0 then {owner:=x,part:=1,p:=e.p} else {owner:=x,part:=2,p:=e.q}
   else if e.part=0 then {owner:=x,part:=3,p:=e.p,i:=pos-1}
   else {owner:=x,part:=4,p:=e.p,q:=e.q,i:=pos-1},1)
def doubleEdgeVertexQ (F : Frame) (m : ℕ) (e : Code) (endpoint : ℕ) : Query Code :=
  if e.part≥4 then
    (if e.part=4 then {owner:=e.owner,copy:=endpoint,part:=1,p:=e.p}
     else if e.part=5 then {owner:=e.owner,copy:=endpoint,part:=2,p:=e.p}
     else {owner:=e.owner,copy:=endpoint,part:=4,p:=e.p,q:=e.q,i:=e.i},1)
  else
    let v := if e.part=0 ∨ e.part=1 then segmentVertexQ e.owner m e endpoint
      else if e.part=2 then gridVertexQ F e.owner m e.p (e.i+endpoint) (e.j+1)
      else gridVertexQ F e.owner m e.p (e.i+1) (e.j+endpoint)
    ({v.1 with copy:=e.copy},v.2+1)
def qDoubleEdgeVertexQ (m : ℕ) (e : Code) (endpoint : ℕ) : Query Code :=
  if e.part=1 then ({family:=1,owner:=e.owner,copy:=endpoint,part:=1,p:=e.p},1)
  else
    let pos := e.i+endpoint
    (if pos=0 then {family:=1,owner:=e.owner,copy:=e.copy}
     else if pos=m then {family:=1,owner:=e.owner,copy:=e.copy,part:=1,p:=e.p}
     else {family:=1,owner:=e.owner,copy:=e.copy,part:=2,p:=e.p,i:=pos-1},1)
def qEdgeImageQ (x : ℕ) (e : Code) : Query Code :=
  (if e.part=0 then {owner:=x,copy:=e.copy,part:=1,p:=e.owner,q:=e.p,i:=e.i}
   else {owner:=x,part:=5,p:=e.p},1)
def bridgeOfVertexQ (v : Code) : Query Code :=
  ({owner:=v.owner,part:=(if v.part=1 then 4 else if v.part=2 then 5 else 6),
    p:=v.p,q:=v.q,i:=v.i},1)
def rxLocalFaceCodesQ (F : Frame) (m : ℕ) : Query (List Code) :=
  loopQ F.nx (fun x =>
    let fs := doubleFacesQ F x m
    let out := flatMapQ (fun f => flatMapQ (fun a =>
      mapQ (fun b => emitQ {f with k:=a,l:=b}) [0,1]) [0,1]) fs.1
    (out.1,fs.2+out.2))
def rxGlueFaceCodesQ (F : Frame) (m : ℕ) : Query (List Code) :=
  loopQ F.nx (fun x =>
    let qs := starQsQ F x
    let out := flatMapQ (fun q =>
      let es := qDoubleEdgesQ F q m
      let out := flatMapQ (fun e => mapQ (fun a =>
        emitQ {family:=1,owner:=x,copy:=e.copy,part:=e.part,p:=q,q:=e.p,i:=e.i,k:=a}) [0,1]) es.1
      (out.1,es.2+out.2)) qs.1
    (out.1,qs.2+out.2))
def rxOldFaceCodesQ (F : Frame) : Query (List Code) :=
  loopQ F.nf (fun f => mapQ (fun c => emitQ {family:=2,owner:=f,copy:=c}) [0,1])
def rxFaceCodesQ (F : Frame) (m : ℕ) : Query (List Code) :=
  collectQ [rxLocalFaceCodesQ F m,rxGlueFaceCodesQ F m,rxOldFaceCodesQ F]
def localFaceEndpointsQ (F : Frame) (m : ℕ) (f : Code) : Query FaceCodes :=
  let z : Code := {f with k:=0,l:=0}
  if f.part=0 then
    let x := gridVertexQ F f.owner m f.p (f.i+f.k) (f.j+f.l)
    let q0 := horizontalEdgeQ F f.owner m f.p f.i (f.j+f.l)
    let q1 := verticalEdgeQ F f.owner m f.p (f.i+f.k) f.j
    (⟨{x.1 with copy:=f.copy},z,{q0.1 with copy:=f.copy},{q1.1 with copy:=f.copy}⟩,
      x.2+q0.2+q1.2+4)
  else
    let edge : Code := {owner:=f.owner,copy:=f.k,part:=1,p:=f.p,q:=f.q,i:=f.i}
    let x := doubleEdgeVertexQ F m edge f.l
    let q1 := bridgeOfVertexQ x.1
    (⟨x.1,z,edge,q1.1⟩,x.2+q1.2+2)
def glueFaceEndpointsQ (F : Frame) (m : ℕ) (f : Code) : Query FaceCodes :=
  let e : Code := {family:=1,owner:=f.p,copy:=f.copy,part:=f.part,p:=f.q,i:=f.i}
  let image := qEdgeImageQ f.owner e
  let x := doubleEdgeVertexQ F m image.1 f.k
  let q1 := qDoubleEdgeVertexQ m e f.k
  (⟨x.1,e,image.1,q1.1⟩,image.2+x.2+q1.2+2)
def oldFaceEndpointsQ (F : Frame) (f : Code) : Query FaceCodes :=
  let old := faceAtQ F.faces f.owner
  (⟨{owner:=old.1.x,copy:=f.copy,part:=2,p:=old.1.z},
    {family:=2,owner:=old.1.z,copy:=f.copy},
    {family:=1,owner:=old.1.q0,copy:=f.copy,part:=1,p:=old.1.z},
    {family:=1,owner:=old.1.q1,copy:=f.copy,part:=1,p:=old.1.z}⟩,old.2+5)
def faceEndpointsQ (F : Frame) (m : ℕ) (f : Code) : Query FaceCodes :=
  let out := if f.family=0 then localFaceEndpointsQ F m f
    else if f.family=1 then glueFaceEndpointsQ F m f else oldFaceEndpointsQ F f
  (out.1,out.2)
def indexFaceQ (xs qs zs : List Code) (code : Code) (f : FaceCodes) : Query FaceRow :=
  let x := handleQ f.x xs
  let z := handleQ f.z zs
  let q0 := handleQ f.q0 qs
  let q1 := handleQ f.q1 qs
  (⟨code,x.1,z.1,q0.1,q1.1⟩,x.2+z.2+q0.2+q1.2+1)
def packFrameQ (xs qs zs : List Code) (fs : List FaceRow) : Query Frame :=
  (⟨xs.length,qs.length,zs.length,fs.length,xs,qs,zs,fs⟩,
    1)
def memCodeQ (c : Code) (as : List Code) : Query Bool :=
  anyQ (equalCodeQ c) as
def dedupQ : List Code → Query (List Code)
  | [] => ([],0)
  | a::as =>
      let tail := dedupQ as
      let found := memCodeQ a tail.1
      (if found.1 then tail.1 else a::tail.1,tail.2+found.2+(if found.1 then 0 else 1))
def rxFrameQ (F : Frame) (m : ℕ) : Query Frame :=
  let rawX := rxXCodesQ F m
  let rawQ := rxQCodesQ F m
  let rawZ := rxZCodesQ F m
  let rawF := rxFaceCodesQ F m
  let xs := dedupQ rawX.1
  let qs := dedupQ rawQ.1
  let zs := dedupQ rawZ.1
  let fc := dedupQ rawF.1
  let rows := mapQ (fun f =>
    let points := faceEndpointsQ F m f
    let out := indexFaceQ xs.1 qs.1 zs.1 f points.1
    (out.1,points.2+out.2)) fc.1
  let out := packFrameQ xs.1 qs.1 zs.1 rows.1
  (out.1,rawX.2+rawQ.2+rawZ.2+rawF.2+xs.2+qs.2+zs.2+fc.2+rows.2+out.2+4)
def transposeFrameQ (F : Frame) : Query Frame :=
  let rows := mapQ (fun f => (⟨f.code,f.z,f.x,f.q0,f.q1⟩,1)) F.faces
  (⟨F.nz,F.nq,F.nx,F.nf,F.zs,F.qs,F.xs,rows.1⟩,rows.2+1)
def rzFrameQ (F : Frame) (m : ℕ) : Query Frame :=
  let input := transposeFrameQ F
  let next := rxFrameQ input.1 m
  let output := transposeFrameQ next.1
  (output.1,input.2+next.2+output.2)
def nextFrameQ (S : OddScale) (n : ℕ) (F : Frame) : Query Frame :=
  let out := if n%2=0 then rxFrameQ F S.half else rzFrameQ F S.half
  (out.1,out.2)
def lastFrameQ : List Frame → Query Frame
  | [] => (seedFrame,0)
  | [f] => (f,0)
  | _::f::fs => let r := lastFrameQ (f::fs); (r.1,r.2)
def historyQ (S : OddScale) : ℕ → Query (List Frame)
  | 0 => ([seedFrameQ.1],seedFrameQ.2+1)
  | n+1 =>
      let before := historyQ S n
      let last := lastFrameQ before.1
      let next := nextFrameQ S n last.1
      let out := appendQ before.1 [next.1]
      (out.1,before.2+last.2+next.2+out.2+1)
def generateQ (S : OddScale) (n : ℕ) : Query Frame :=
  let frames := historyQ S n
  let final := lastFrameQ frames.1
  (final.1,frames.2+final.2)
def denseXQQ (F : Frame) : Query (List (ℕ × ℕ × Bool)) :=
  loopQ F.nx (fun x =>
    let qs := rangeQ F.nq
    let out := mapQ (fun q => let hit := xqQ F x q; ((x,q,hit.1),hit.2+1)) qs.1
    (out.1,qs.2+out.2))
def denseQZQ (F : Frame) : Query (List (ℕ × ℕ × Bool)) :=
  loopQ F.nq (fun q =>
    let zs := rangeQ F.nz
    let out := mapQ (fun z => let hit := qzQ F q z; ((q,z,hit.1),hit.2+1)) zs.1
    (out.1,zs.2+out.2))
def vertexCodesQ (F : Frame) : Query (List Code) :=
  let raw := collectQ [
    loopQ F.nx (fun x => singletonQ {owner:=x}),
    loopQ F.nq (fun q => singletonQ {family:=1,owner:=q}),
    loopQ F.nz (fun z => singletonQ {family:=2,owner:=z})]
  let unique := dedupQ raw.1
  (unique.1,raw.2+unique.2)
def edgeCodesQ (F : Frame) : Query (List Code) :=
  let a := denseXQQ F
  let b := denseQZQ F
  let ax := filterQ (fun t => (t.2.2,0)) a.1
  let bz := filterQ (fun t => (t.2.2,0)) b.1
  let left := mapQ (fun t => emitQ {owner:=t.1,p:=t.2.1}) ax.1
  let right := mapQ (fun t => emitQ {family:=1,owner:=t.1,p:=t.2.1}) bz.1
  let out := collectQ [left,right]
  let unique := dedupQ out.1
  (unique.1,a.2+b.2+ax.2+bz.2+out.2+unique.2)
def edgeVertexTestQ (e v : Code) : Query Bool :=
  (if e.family=0 then
     decide ((v.family=0 ∧ v.owner=e.owner) ∨ (v.family=1 ∧ v.owner=e.p))
   else decide ((v.family=1 ∧ v.owner=e.owner) ∨ (v.family=2 ∧ v.owner=e.p)),0)
def faceEdgeTestQ (f : FaceRow) (e : Code) : Query Bool :=
  (if e.family=0 then decide (e.owner=f.x ∧ (e.p=f.q0 ∨ e.p=f.q1))
   else decide (e.p=f.z ∧ (e.owner=f.q0 ∨ e.owner=f.q1)),0)
def cellularBoundary1Q (vertices edges : List Code) : Query (List (ℕ × ℕ × Bool)) :=
  let ei := rangeQ edges.length
  let vi := rangeQ vertices.length
  let out := flatMapQ (fun e => mapQ (fun v =>
    let ec := edges[e]?.getD {}
    let vc := vertices[v]?.getD {}
    let hit := edgeVertexTestQ ec vc
    ((v,e,hit.1),hit.2+1)) vi.1) ei.1
  (out.1,ei.2+vi.2+out.2)
def cellularBoundary2Q (F : Frame) (edges : List Code) : Query (List (ℕ × ℕ × Bool)) :=
  let fi := rangeQ F.nf
  let ei := rangeQ edges.length
  let out := flatMapQ (fun f =>
    let row := faceAtQ F.faces f
    let cells := mapQ (fun e =>
      let ec := edges[e]?.getD {}
      let hit := faceEdgeTestQ row.1 ec
      ((e,f,hit.1),hit.2+1)) ei.1
    (cells.1,row.2+cells.2)) fi.1
  (out.1,fi.2+ei.2+out.2)
def runQ (S : OddScale) (n : ℕ) : Query Output :=
  let frame := generateQ S n
  let a := denseXQQ frame.1
  let b := denseQZQ frame.1
  let vertices := vertexCodesQ frame.1
  let edges := edgeCodesQ frame.1
  let boundary1 := cellularBoundary1Q vertices.1 edges.1
  let boundary2 := cellularBoundary2Q frame.1 edges.1
  (⟨frame.1,a.1,b.1,vertices.1,edges.1,boundary1.1,boundary2.1⟩,
    frame.2+a.2+b.2+vertices.2+edges.2+boundary1.2+boundary2.2+1)
def seedRowsQ : Query (List SeedRow) :=
  let rows := collectQ [
    let ids := rangeQ 2
    let out := mapQ (fun i => (⟨0,i,0,(0,0,0)⟩,1)) ids.1
    (out.1,ids.2+out.2),
    let ids := rangeQ 5
    let out := mapQ (fun i => (⟨1,i,0,(0,0,0)⟩,1)) ids.1
    (out.1,ids.2+out.2),
    let ids := rangeQ 2
    let out := mapQ (fun i => (⟨2,i,0,(0,0,0)⟩,1)) ids.1
    (out.1,ids.2+out.2)]
  (rows.1,rows.2)
def triangleCodesQ (F : Frame) : Query (List Code) :=
  let raw := loopQ F.nf (fun f => mapQ (fun d => emitQ {family:=3,owner:=f,copy:=d}) [0,1])
  let unique := dedupQ raw.1
  (unique.1,raw.2+unique.2)
def setupQ (S : OddScale) (n : ℕ) : Query SetupOutput :=
  let data := runQ S n
  let triangles := triangleCodesQ data.1.frame
  let initial := seedRowsQ
  (⟨data.1,triangles.1,initial.1⟩,data.2+triangles.2+initial.2+1)
end Allocation
theorem allocation_map_value {A B : Type*} (f : A → Query B) (xs : List A) :
    (Allocation.mapQ f xs).1=xs.map (fun a => (f a).1) := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [Allocation.mapQ,List.map_cons,ih]
theorem allocation_filter_value {A : Type*} (f : A → Query Bool) (xs : List A) :
    (Allocation.filterQ f xs).1=xs.filter (fun a => (f a).1) := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
      cases h : (f a).1 <;> simp [Allocation.filterQ,ih,h]
theorem allocation_range_value (n : ℕ) : (Allocation.rangeQ n).1=(rangeQ n).1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Allocation.rangeQ,rangeQ,ih]
theorem allocation_flat_value {A B : Type*} (f : A → Query (List B)) (xs : List A) :
    (Allocation.flatMapQ f xs).1=xs.flatMap (fun a => (f a).1) := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [Allocation.flatMapQ,Allocation.appendQ,List.flatMap_cons,ih]
theorem allocation_flatten_value {A : Type*} (xs : List (List A)) :
    (Allocation.flattenQ xs).1=xs.flatten := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [Allocation.flattenQ,Allocation.appendQ,List.flatten_cons,ih]
theorem allocation_any_value {A : Type*} (p : A → Query Bool) (xs : List A) :
    (Allocation.anyQ p xs).1=(anyQ p xs).1 := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [Allocation.anyQ,anyQ,ih]
theorem allocation_handle_value (c : Code) (xs : List Code) :
    (Allocation.handleQ c xs).1=(handleQ c xs).1 := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
      by_cases h : c=a
      · simp only [Allocation.handleQ,handleQ,Allocation.equalCodeQ,equalCodeQ,h,
          decide_true,ite_true]
      · simp only [Allocation.handleQ,handleQ,Allocation.equalCodeQ,equalCodeQ,h,
          decide_false,Bool.false_eq_true,ite_false,ih]
theorem allocation_faceAt_value (fs : List FaceRow) (i : ℕ) :
    (Allocation.faceAtQ fs i).1=(faceAtQ fs i).1 := by
  induction fs generalizing i with
  | nil => rfl
  | cons f fs ih => cases i <;> simp only [Allocation.faceAtQ,faceAtQ,ih]
theorem allocation_last_value (fs : List Frame) :
    (Allocation.lastFrameQ fs).1=(lastFrameQ fs).1 := by
  induction fs with
  | nil => rfl
  | cons f fs ih => cases fs <;> simp only [Allocation.lastFrameQ,lastFrameQ,ih]
theorem allocation_map_le {A B : Type*}
    (f g : A → Query B) (xs : List A) (hc : ∀a,(f a).2≤(g a).2) :
    (Allocation.mapQ f xs).2≤(mapQ g xs).2 := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [Allocation.mapQ,mapQ]; have := hc a; omega
theorem allocation_filter_le {A : Type*}
    (f g : A → Query Bool) (xs : List A) (hv : ∀a,(f a).1=(g a).1)
    (hc : ∀a,(f a).2≤(g a).2) : (Allocation.filterQ f xs).2≤(filterQ g xs).2 := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [Allocation.filterQ,filterQ,hv]; have := hc a; omega
theorem allocation_flat_le {A B : Type*}
    (f g : A → Query (List B)) (xs : List A) (hv : ∀a,(f a).1=(g a).1)
    (hc : ∀a,(f a).2≤(g a).2) : (Allocation.flatMapQ f xs).2≤(flatMapQ g xs).2 := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
      simp only [Allocation.flatMapQ,flatMapQ,Allocation.appendQ,appendQ,hv]
      have := hc a; omega
theorem allocation_flatten_le {A : Type*} (xs : List (List A)) :
    (Allocation.flattenQ xs).2≤(flattenQ xs).2 := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [Allocation.flattenQ,flattenQ,Allocation.appendQ,appendQ]; omega
theorem allocation_range_le (n : ℕ) :
    (Allocation.rangeQ n).2≤(rangeQ n).2 := by
  induction n with
  | zero => decide
  | succ n ih => simp only [Allocation.rangeQ,rangeQ,allocation_range_value]; omega
theorem allocation_any_le {A : Type*}
    (f g : A → Query Bool) (xs : List A) (hc : ∀a,(f a).2≤(g a).2) :
    (Allocation.anyQ f xs).2≤(anyQ g xs).2 := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [Allocation.anyQ,anyQ]; have := hc a; omega
theorem allocation_handle_le (c : Code) (xs : List Code) :
    (Allocation.handleQ c xs).2≤(handleQ c xs).2 := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
      by_cases h : c=a <;>
        simp [Allocation.handleQ,handleQ,Allocation.equalCodeQ,equalCodeQ,h] <;> omega
theorem allocation_faceAt_le (fs : List FaceRow) (i : ℕ) :
    (Allocation.faceAtQ fs i).2≤(faceAtQ fs i).2 := by
  induction fs generalizing i with
  | nil => change 0 ≤ 1; omega
  | cons f fs ih =>
      cases i with
      | zero => change 0 ≤ 2; omega
      | succ i =>
          change (Allocation.faceAtQ fs i).2 ≤ (faceAtQ fs i).2+2
          exact (ih i).trans (Nat.le_add_right _ _)
theorem allocation_last_le (fs : List Frame) :
    (Allocation.lastFrameQ fs).2≤(lastFrameQ fs).2 := by
  induction fs with
  | nil => decide
  | cons f fs ih => cases fs <;> simp only [Allocation.lastFrameQ,lastFrameQ] <;> omega
theorem allocation_product_value {A B : Type*} (xs : List A) (ys : List B) :
    (Allocation.productQ xs ys).1=(productQ xs ys).1 := by
  simp only [Allocation.productQ,productQ,allocation_map_value,allocation_flatten_value,
    mapQ_value,flattenQ_value]
theorem allocation_loop_le {A : Type*} (n : ℕ)
    (f g : ℕ → Query (List A)) (hv : ∀i,(f i).1=(g i).1)
    (hc : ∀i,(f i).2≤(g i).2) : (Allocation.loopQ n f).2≤(loopQ n g).2 := by
  have hr := allocation_range_le n
  have hf := allocation_flat_le f g (rangeQ n).1 hv hc
  simpa only [Allocation.loopQ,loopQ,allocation_range_value] using Nat.add_le_add hr hf
theorem allocation_product_le {A B : Type*} (xs : List A) (ys : List B) :
    (Allocation.productQ xs ys).2≤(productQ xs ys).2 := by
  have hinner (x : A) : (Allocation.mapQ (fun y : B => ((x,y),1)) ys).2≤
      (mapQ (fun y : B => ((x,y),1)) ys).2 := allocation_map_le _ _ ys (by intros; rfl)
  have hmap := allocation_map_le
    (fun x : A => Allocation.mapQ (fun y : B => ((x,y),1)) ys)
    (fun x : A => mapQ (fun y : B => ((x,y),1)) ys) xs hinner
  have hflatten := allocation_flatten_le (xs.map (fun x => ys.map (fun y => (x,y))))
  simpa only [Allocation.productQ,productQ,allocation_map_value,mapQ_value] using Nat.add_le_add hmap hflatten
theorem allocation_collect_le {A : Type*} (as bs : List (Query (List A)))
    (hv : as.map Prod.fst=bs.map Prod.fst)
    (hc : (as.map Prod.snd).sum≤(bs.map Prod.snd).sum) :
    (Allocation.collectQ as).2≤(collectQ bs).2 := by
  have left (qs : List (Query (List A))) :
      (Allocation.collectQ qs).2=(qs.map Prod.snd).sum+
        (qs.map (fun q => q.1.length)).sum+qs.length := by
    induction qs with
    | nil => rfl
    | cons q qs ih =>
        simp only [Allocation.collectQ,Allocation.flatMapQ,Allocation.appendQ,
          List.map_cons,List.sum_cons,List.length_cons,id_eq] at ih ⊢
        omega
  have right (qs : List (Query (List A))) :
      (collectQ qs).2=(qs.map Prod.snd).sum+
        (qs.map (fun q => q.1.length)).sum+2*qs.length := by
    induction qs with
    | nil => rfl
    | cons q qs ih =>
        simp only [collectQ,flatMapQ,appendQ,List.map_cons,List.sum_cons,List.length_cons,id_eq] at ih ⊢
        omega
  have hlen : as.length=bs.length := by simpa only [List.length_map] using congrArg List.length hv
  have hsum : (as.map (fun q => q.1.length)).sum=(bs.map (fun q => q.1.length)).sum := by
    simpa only [List.map_map,Function.comp_def] using congrArg (fun xs : List (List A) => (xs.map List.length).sum) hv
  rw [left,right,hlen,hsum]
  omega
theorem native_map_value_congr {A B : Type*} (f g : A → Query B)
    (xs : List A) (hv : ∀a,(f a).1=(g a).1) :
    (Allocation.mapQ f xs).1=(mapQ g xs).1 := by
  rw [allocation_map_value,mapQ_value]
  exact congrArg (fun k : A → B => xs.map k) (funext hv)
theorem native_filter_value_congr {A : Type*} (f g : A → Query Bool)
    (xs : List A) (hv : ∀a,(f a).1=(g a).1) :
    (Allocation.filterQ f xs).1=(filterQ g xs).1 := by
  rw [allocation_filter_value,filterQ_value]
  exact congrArg (fun k : A → Bool => xs.filter k) (funext hv)
theorem native_flat_value_congr {A B : Type*} (f g : A → Query (List B))
    (xs : List A) (hv : ∀a,(f a).1=(g a).1) :
    (Allocation.flatMapQ f xs).1=(flatMapQ g xs).1 := by
  rw [allocation_flat_value,flatMapQ_value]
  exact congrArg (fun k : A → List B => xs.flatMap k) (funext hv)
theorem native_any_value_congr {A : Type*} (f g : A → Query Bool)
    (xs : List A) (hv : ∀a,(f a).1=(g a).1) :
    (Allocation.anyQ f xs).1=(anyQ g xs).1 := by
  rw [allocation_any_value,anyQ_value,anyQ_value]
  exact congrArg (fun k : A → Bool => xs.any k) (funext hv)
theorem native_loop_value_congr {A : Type*} (n : ℕ)
    (f g : ℕ → Query (List A)) (hv : ∀a,(f a).1=(g a).1) :
    (Allocation.loopQ n f).1=(loopQ n g).1 := by
  change (Allocation.flatMapQ f (Allocation.rangeQ n).1).1=
    (flatMapQ g (rangeQ n).1).1
  rw [allocation_range_value]
  exact native_flat_value_congr f g (rangeQ n).1 hv
theorem native_flatMap_fst {A : Type*} (qs : List (Query (List A))) :
    qs.flatMap Prod.fst=(qs.map Prod.fst).flatten := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
      simp only [List.flatMap_cons,List.map_cons,List.flatten_cons,ih]
theorem native_collect_value_congr {A : Type*} (as bs : List (Query (List A)))
    (hv : as.map Prod.fst=bs.map Prod.fst) :
    (Allocation.collectQ as).1=(collectQ bs).1 := by
  change (Allocation.flatMapQ id as).1=(flatMapQ id bs).1
  rw [allocation_flat_value,flatMapQ_value]
  change as.flatMap Prod.fst=bs.flatMap Prod.fst
  rw [native_flatMap_fst,native_flatMap_fst,hv]
theorem native_map_simulation {A B : Type*} (f g : A → Query B) (xs : List A)
    (h : ∀a,(f a).1=(g a).1 ∧ (f a).2≤(g a).2) :
    (Allocation.mapQ f xs).1=(mapQ g xs).1 ∧ (Allocation.mapQ f xs).2≤(mapQ g xs).2 :=
  ⟨native_map_value_congr f g xs (fun a => (h a).1),
    allocation_map_le f g xs (fun a => (h a).2)⟩
theorem native_filter_simulation {A : Type*} (f g : A → Query Bool) (xs : List A)
    (h : ∀a,(f a).1=(g a).1 ∧ (f a).2≤(g a).2) :
    (Allocation.filterQ f xs).1=(filterQ g xs).1 ∧ (Allocation.filterQ f xs).2≤(filterQ g xs).2 :=
  ⟨native_filter_value_congr f g xs (fun a => (h a).1),
    allocation_filter_le f g xs (fun a => (h a).1) (fun a => (h a).2)⟩
theorem native_flat_simulation {A B : Type*} (f g : A → Query (List B)) (xs : List A)
    (h : ∀a,(f a).1=(g a).1 ∧ (f a).2≤(g a).2) :
    (Allocation.flatMapQ f xs).1=(flatMapQ g xs).1 ∧ (Allocation.flatMapQ f xs).2≤(flatMapQ g xs).2 :=
  ⟨native_flat_value_congr f g xs (fun a => (h a).1),
    allocation_flat_le f g xs (fun a => (h a).1) (fun a => (h a).2)⟩
theorem native_any_simulation {A : Type*} (f g : A → Query Bool) (xs : List A)
    (h : ∀a,(f a).1=(g a).1 ∧ (f a).2≤(g a).2) :
    (Allocation.anyQ f xs).1=(anyQ g xs).1 ∧ (Allocation.anyQ f xs).2≤(anyQ g xs).2 :=
  ⟨native_any_value_congr f g xs (fun a => (h a).1),
    allocation_any_le f g xs (fun a => (h a).2)⟩
theorem native_loop_simulation {A : Type*} (n : ℕ) (f g : ℕ → Query (List A))
    (h : ∀a,(f a).1=(g a).1 ∧ (f a).2≤(g a).2) :
    (Allocation.loopQ n f).1=(loopQ n g).1 ∧ (Allocation.loopQ n f).2≤(loopQ n g).2 :=
  ⟨native_loop_value_congr n f g (fun a => (h a).1),
    allocation_loop_le n f g (fun a => (h a).1) (fun a => (h a).2)⟩
theorem native_collect_simulation {A : Type*} (as bs : List (Query (List A)))
    (hv : as.map Prod.fst=bs.map Prod.fst)
    (hc : (as.map Prod.snd).sum≤(bs.map Prod.snd).sum) :
    (Allocation.collectQ as).1=(collectQ bs).1 ∧ (Allocation.collectQ as).2≤(collectQ bs).2 :=
  ⟨native_collect_value_congr as bs hv,allocation_collect_le as bs hv hc⟩
theorem allocation_appendQ_value {A : Type*} (a b : List A) :
    (Allocation.appendQ a b).1=(appendQ a b).1 := by
  simp only [Allocation.appendQ, appendQ]
attribute [local simp] allocation_appendQ_value
theorem allocation_equalCodeQ_value (a b : Code) :
    (Allocation.equalCodeQ a b).1=(equalCodeQ a b).1 := by
  simp only [Allocation.equalCodeQ, equalCodeQ]
attribute [local simp] allocation_equalCodeQ_value
theorem allocation_equalCodeQ_le (a b : Code) :
    (Allocation.equalCodeQ a b).2≤(equalCodeQ a b).2 := by
  exact Nat.zero_le _
theorem allocation_xqFaceTestQ_value (x q : ℕ) (f : FaceRow) :
    (Allocation.xqFaceTestQ x q f).1=(xqFaceTestQ x q f).1 := by
  simp only [Allocation.xqFaceTestQ, xqFaceTestQ]
attribute [local simp] allocation_xqFaceTestQ_value
theorem allocation_xqFaceTestQ_le (x q : ℕ) (f : FaceRow) :
    (Allocation.xqFaceTestQ x q f).2≤(xqFaceTestQ x q f).2 := by
  exact Nat.zero_le _
theorem allocation_qzFaceTestQ_value (q z : ℕ) (f : FaceRow) :
    (Allocation.qzFaceTestQ q z f).1=(qzFaceTestQ q z f).1 := by
  simp only [Allocation.qzFaceTestQ, qzFaceTestQ]
attribute [local simp] allocation_qzFaceTestQ_value
theorem allocation_qzFaceTestQ_le (q z : ℕ) (f : FaceRow) :
    (Allocation.qzFaceTestQ q z f).2≤(qzFaceTestQ q z f).2 := by
  exact Nat.zero_le _
theorem native_xqQ_simulation (F : Frame) (x q : ℕ) :
    (Allocation.xqQ F x q).1=(xqQ F x q).1 ∧ (Allocation.xqQ F x q).2≤(xqQ F x q).2 := by
  unfold Allocation.xqQ xqQ
  apply native_any_simulation
  intro v
  exact ⟨allocation_xqFaceTestQ_value x q v, allocation_xqFaceTestQ_le x q v⟩
theorem allocation_xqQ_value (F : Frame) (x q : ℕ) :
    (Allocation.xqQ F x q).1=(xqQ F x q).1 := by
  exact (native_xqQ_simulation F x q).1
attribute [local simp] allocation_xqQ_value
theorem allocation_xqQ_le (F : Frame) (x q : ℕ) :
    (Allocation.xqQ F x q).2≤(xqQ F x q).2 := by
  exact (native_xqQ_simulation F x q).2
theorem native_qzQ_simulation (F : Frame) (q z : ℕ) :
    (Allocation.qzQ F q z).1=(qzQ F q z).1 ∧ (Allocation.qzQ F q z).2≤(qzQ F q z).2 := by
  unfold Allocation.qzQ qzQ
  apply native_any_simulation
  intro v
  exact ⟨allocation_qzFaceTestQ_value q z v, allocation_qzFaceTestQ_le q z v⟩
theorem allocation_qzQ_value (F : Frame) (q z : ℕ) :
    (Allocation.qzQ F q z).1=(qzQ F q z).1 := by
  exact (native_qzQ_simulation F q z).1
attribute [local simp] allocation_qzQ_value
theorem allocation_qzQ_le (F : Frame) (q z : ℕ) :
    (Allocation.qzQ F q z).2≤(qzQ F q z).2 := by
  exact (native_qzQ_simulation F q z).2
theorem allocation_seedFrameQ_value  :
    (Allocation.seedFrameQ).1=(seedFrameQ).1 := by
  simp only [Allocation.seedFrameQ, seedFrameQ]
attribute [local simp] allocation_seedFrameQ_value
theorem allocation_emitQ_value (c : Code) :
    (Allocation.emitQ c).1=(emitQ c).1 := by
  simp only [Allocation.emitQ, emitQ]
attribute [local simp] allocation_emitQ_value
theorem allocation_emitQ_le (c : Code) :
    (Allocation.emitQ c).2≤(emitQ c).2 := by
  change 1 ≤ 32
  decide
theorem allocation_singletonQ_value (c : Code) :
    (Allocation.singletonQ c).1=(singletonQ c).1 := by
  simp only [Allocation.singletonQ, singletonQ]
attribute [local simp] allocation_singletonQ_value
theorem allocation_singletonQ_le (c : Code) :
    (Allocation.singletonQ c).2≤(singletonQ c).2 := by
  change 2 ≤ 33
  decide
theorem native_mapCodesQ_simulation (f : Code → Code) (xs : List Code) :
    (Allocation.mapCodesQ f xs).1=(mapCodesQ f xs).1 ∧ (Allocation.mapCodesQ f xs).2≤(mapCodesQ f xs).2 := by
  unfold Allocation.mapCodesQ mapCodesQ
  apply native_map_simulation
  intro c
  exact ⟨allocation_emitQ_value (f c), allocation_emitQ_le (f c)⟩
theorem allocation_mapCodesQ_value (f : Code → Code) (xs : List Code) :
    (Allocation.mapCodesQ f xs).1=(mapCodesQ f xs).1 := by
  exact (native_mapCodesQ_simulation f xs).1
attribute [local simp] allocation_mapCodesQ_value
theorem allocation_mapCodesQ_le (f : Code → Code) (xs : List Code) :
    (Allocation.mapCodesQ f xs).2≤(mapCodesQ f xs).2 := by
  exact (native_mapCodesQ_simulation f xs).2
theorem native_facesAtXQ_simulation (F : Frame) (x : ℕ) :
    (Allocation.facesAtXQ F x).1=(facesAtXQ F x).1 ∧ (Allocation.facesAtXQ F x).2≤(facesAtXQ F x).2 := by
  unfold Allocation.facesAtXQ facesAtXQ
  let idsA := Allocation.rangeQ F.nf
  let idsR := rangeQ F.nf
  have h_ids : idsA.1=idsR.1 ∧ idsA.2≤ idsR.2 := by
    change (Allocation.rangeQ F.nf).1=(rangeQ F.nf).1 ∧ (Allocation.rangeQ F.nf).2≤(rangeQ F.nf).2
    exact ⟨allocation_range_value F.nf, allocation_range_le F.nf⟩
  let rowsA := Allocation.mapQ (fun i => ((i,F.faces[i]?.getD ⟨{},0,0,0,0⟩),1)) idsA.1
  let rowsR := mapQ (fun i => ((i,F.faces[i]?.getD ⟨{},0,0,0,0⟩),2*i+3)) idsR.1
  have h_rows : rowsA.1=rowsR.1 ∧ rowsA.2≤rowsR.2 := by
    change (Allocation.mapQ (fun i => ((i,F.faces[i]?.getD ⟨{},0,0,0,0⟩),1)) idsA.1).1=(mapQ (fun i => ((i,F.faces[i]?.getD ⟨{},0,0,0,0⟩),2*i+3)) idsR.1).1 ∧ (Allocation.mapQ (fun i => ((i,F.faces[i]?.getD ⟨{},0,0,0,0⟩),1)) idsA.1).2≤(mapQ (fun i => ((i,F.faces[i]?.getD ⟨{},0,0,0,0⟩),2*i+3)) idsR.1).2
    rw [h_ids.1]
    apply native_map_simulation
    intro i
    constructor
    · change (i,F.faces[i]?.getD ⟨{},0,0,0,0⟩)=(i,F.faces[i]?.getD ⟨{},0,0,0,0⟩)
      rfl
    · change 1≤2*i+3
      omega
  let outA := Allocation.filterQ (fun r => (decide (r.2.x=x),0)) rowsA.1
  let outR := filterQ (fun r => (decide (r.2.x=x),3)) rowsR.1
  have h_out : outA.1=outR.1 ∧ outA.2≤outR.2 := by
    change (Allocation.filterQ (fun r => (decide (r.2.x=x),0)) rowsA.1).1=(filterQ (fun r => (decide (r.2.x=x),3)) rowsR.1).1 ∧ (Allocation.filterQ (fun r => (decide (r.2.x=x),0)) rowsA.1).2≤(filterQ (fun r => (decide (r.2.x=x),3)) rowsR.1).2
    rw [h_rows.1]
    apply native_filter_simulation
    intro r
    constructor
    · change decide (r.2.x=x)=decide (r.2.x=x)
      rfl
    · change 0≤3
      omega
  constructor
  · change outA.1=outR.1
    simpa only [h_out.1]
  · change idsA.2+rowsA.2+outA.2≤ idsR.2+rowsR.2+outR.2
    have hc0 := h_ids.2
    have hc1 := h_rows.2
    have hc2 := h_out.2
    omega
theorem allocation_facesAtXQ_value (F : Frame) (x : ℕ) :
    (Allocation.facesAtXQ F x).1=(facesAtXQ F x).1 := by
  exact (native_facesAtXQ_simulation F x).1
attribute [local simp] allocation_facesAtXQ_value
theorem allocation_facesAtXQ_le (F : Frame) (x : ℕ) :
    (Allocation.facesAtXQ F x).2≤(facesAtXQ F x).2 := by
  exact (native_facesAtXQ_simulation F x).2
theorem native_starQsQ_simulation (F : Frame) (x : ℕ) :
    (Allocation.starQsQ F x).1=(starQsQ F x).1 ∧ (Allocation.starQsQ F x).2≤(starQsQ F x).2 := by
  unfold Allocation.starQsQ starQsQ
  let idsA := Allocation.rangeQ F.nq
  let idsR := rangeQ F.nq
  have h_ids : idsA.1=idsR.1 ∧ idsA.2≤ idsR.2 := by
    change (Allocation.rangeQ F.nq).1=(rangeQ F.nq).1 ∧ (Allocation.rangeQ F.nq).2≤(rangeQ F.nq).2
    exact ⟨allocation_range_value F.nq, allocation_range_le F.nq⟩
  let outA := Allocation.filterQ (Allocation.xqQ F x) idsA.1
  let outR := filterQ (xqQ F x) idsR.1
  have h_out : outA.1=outR.1 ∧ outA.2≤outR.2 := by
    change (Allocation.filterQ (Allocation.xqQ F x) idsA.1).1=(filterQ (xqQ F x) idsR.1).1 ∧ (Allocation.filterQ (Allocation.xqQ F x) idsA.1).2≤(filterQ (xqQ F x) idsR.1).2
    rw [h_ids.1]
    apply native_filter_simulation
    intro v
    exact ⟨allocation_xqQ_value F x v, allocation_xqQ_le F x v⟩
  constructor
  · change outA.1=outR.1
    simpa only [h_out.1]
  · change idsA.2+outA.2≤ idsR.2+outR.2
    have hc0 := h_ids.2
    have hc1 := h_out.2
    omega
theorem allocation_starQsQ_value (F : Frame) (x : ℕ) :
    (Allocation.starQsQ F x).1=(starQsQ F x).1 := by
  exact (native_starQsQ_simulation F x).1
attribute [local simp] allocation_starQsQ_value
theorem allocation_starQsQ_le (F : Frame) (x : ℕ) :
    (Allocation.starQsQ F x).2≤(starQsQ F x).2 := by
  exact (native_starQsQ_simulation F x).2
theorem native_starZsQ_simulation (F : Frame) (x : ℕ) :
    (Allocation.starZsQ F x).1=(starZsQ F x).1 ∧ (Allocation.starZsQ F x).2≤(starZsQ F x).2 := by
  unfold Allocation.starZsQ starZsQ
  let idsA := Allocation.rangeQ F.nz
  let idsR := rangeQ F.nz
  have h_ids : idsA.1=idsR.1 ∧ idsA.2≤ idsR.2 := by
    change (Allocation.rangeQ F.nz).1=(rangeQ F.nz).1 ∧ (Allocation.rangeQ F.nz).2≤(rangeQ F.nz).2
    exact ⟨allocation_range_value F.nz, allocation_range_le F.nz⟩
  let outA := Allocation.filterQ (fun z => Allocation.anyQ (fun f : FaceRow =>
    (decide (f.x=x ∧ f.z=z),0)) F.faces) idsA.1
  let outR := filterQ (fun z => anyQ (fun f : FaceRow =>
    (decide (f.x=x ∧ f.z=z),5)) F.faces) idsR.1
  have h_out : outA.1=outR.1 ∧ outA.2≤outR.2 := by
    change (Allocation.filterQ (fun z => Allocation.anyQ (fun f : FaceRow =>
    (decide (f.x=x ∧ f.z=z),0)) F.faces) idsA.1).1=(filterQ (fun z => anyQ (fun f : FaceRow =>
    (decide (f.x=x ∧ f.z=z),5)) F.faces) idsR.1).1 ∧ (Allocation.filterQ (fun z => Allocation.anyQ (fun f : FaceRow =>
    (decide (f.x=x ∧ f.z=z),0)) F.faces) idsA.1).2≤(filterQ (fun z => anyQ (fun f : FaceRow =>
    (decide (f.x=x ∧ f.z=z),5)) F.faces) idsR.1).2
    rw [h_ids.1]
    apply native_filter_simulation
    intro z
    apply native_any_simulation
    intro f
    constructor
    · change decide (f.x=x ∧ f.z=z)=decide (f.x=x ∧ f.z=z)
      rfl
    · change 0≤5
      omega
  constructor
  · change outA.1=outR.1
    simpa only [h_out.1]
  · change idsA.2+outA.2≤ idsR.2+outR.2
    have hc0 := h_ids.2
    have hc1 := h_out.2
    omega
theorem allocation_starZsQ_value (F : Frame) (x : ℕ) :
    (Allocation.starZsQ F x).1=(starZsQ F x).1 := by
  exact (native_starZsQ_simulation F x).1
attribute [local simp] allocation_starZsQ_value
theorem allocation_starZsQ_le (F : Frame) (x : ℕ) :
    (Allocation.starZsQ F x).2≤(starZsQ F x).2 := by
  exact (native_starZsQ_simulation F x).2
theorem native_starSidesQ_simulation (F : Frame) (x : ℕ) :
    (Allocation.starSidesQ F x).1=(starSidesQ F x).1 ∧ (Allocation.starSidesQ F x).2≤(starSidesQ F x).2 := by
  unfold Allocation.starSidesQ starSidesQ
  let qsA := Allocation.rangeQ F.nq
  let qsR := rangeQ F.nq
  have h_qs : qsA.1=qsR.1 ∧ qsA.2≤qsR.2 := by
    change (Allocation.rangeQ F.nq).1=(rangeQ F.nq).1 ∧ (Allocation.rangeQ F.nq).2≤(rangeQ F.nq).2
    exact ⟨allocation_range_value F.nq, allocation_range_le F.nq⟩
  let zsA := Allocation.rangeQ F.nz
  let zsR := rangeQ F.nz
  have h_zs : zsA.1=zsR.1 ∧ zsA.2≤zsR.2 := by
    change (Allocation.rangeQ F.nz).1=(rangeQ F.nz).1 ∧ (Allocation.rangeQ F.nz).2≤(rangeQ F.nz).2
    exact ⟨allocation_range_value F.nz, allocation_range_le F.nz⟩
  let pairsA := Allocation.productQ qsA.1 zsA.1
  let pairsR := productQ qsR.1 zsR.1
  have h_pairs : pairsA.1=pairsR.1 ∧ pairsA.2≤pairsR.2 := by
    change (Allocation.productQ qsA.1 zsA.1).1=(productQ qsR.1 zsR.1).1 ∧ (Allocation.productQ qsA.1 zsA.1).2≤(productQ qsR.1 zsR.1).2
    rw [h_qs.1, h_zs.1]
    exact ⟨allocation_product_value qsR.1 zsR.1, allocation_product_le qsR.1 zsR.1⟩
  let outA := Allocation.filterQ (fun e => Allocation.anyQ (fun f : FaceRow =>
    (decide (f.x=x ∧ f.z=e.2 ∧ (f.q0=e.1 ∨ f.q1=e.1)),0)) F.faces) pairsA.1
  let outR := filterQ (fun e => anyQ (fun f : FaceRow =>
    (decide (f.x=x ∧ f.z=e.2 ∧ (f.q0=e.1 ∨ f.q1=e.1)),10)) F.faces) pairsR.1
  have h_out : outA.1=outR.1 ∧ outA.2≤outR.2 := by
    change (Allocation.filterQ (fun e => Allocation.anyQ (fun f : FaceRow =>
    (decide (f.x=x ∧ f.z=e.2 ∧ (f.q0=e.1 ∨ f.q1=e.1)),0)) F.faces) pairsA.1).1=(filterQ (fun e => anyQ (fun f : FaceRow =>
    (decide (f.x=x ∧ f.z=e.2 ∧ (f.q0=e.1 ∨ f.q1=e.1)),10)) F.faces) pairsR.1).1 ∧ (Allocation.filterQ (fun e => Allocation.anyQ (fun f : FaceRow =>
    (decide (f.x=x ∧ f.z=e.2 ∧ (f.q0=e.1 ∨ f.q1=e.1)),0)) F.faces) pairsA.1).2≤(filterQ (fun e => anyQ (fun f : FaceRow =>
    (decide (f.x=x ∧ f.z=e.2 ∧ (f.q0=e.1 ∨ f.q1=e.1)),10)) F.faces) pairsR.1).2
    rw [h_pairs.1]
    apply native_filter_simulation
    intro e
    apply native_any_simulation
    intro f
    constructor
    · change decide (f.x=x ∧ f.z=e.2 ∧ (f.q0=e.1 ∨ f.q1=e.1))=decide (f.x=x ∧ f.z=e.2 ∧ (f.q0=e.1 ∨ f.q1=e.1))
      rfl
    · change 0≤10
      omega
  constructor
  · change outA.1=outR.1
    simpa only [h_out.1]
  · change qsA.2+zsA.2+pairsA.2+outA.2≤qsR.2+zsR.2+pairsR.2+outR.2
    have hc0 := h_qs.2
    have hc1 := h_zs.2
    have hc2 := h_pairs.2
    have hc3 := h_out.2
    omega
theorem allocation_starSidesQ_value (F : Frame) (x : ℕ) :
    (Allocation.starSidesQ F x).1=(starSidesQ F x).1 := by
  exact (native_starSidesQ_simulation F x).1
attribute [local simp] allocation_starSidesQ_value
theorem allocation_starSidesQ_le (F : Frame) (x : ℕ) :
    (Allocation.starSidesQ F x).2≤(starSidesQ F x).2 := by
  exact (native_starSidesQ_simulation F x).2
theorem native_subVerticesQ_simulation (F : Frame) (x m : ℕ) :
    (Allocation.subVerticesQ F x m).1=(subVerticesQ F x m).1 ∧ (Allocation.subVerticesQ F x m).2≤(subVerticesQ F x m).2 := by
  unfold Allocation.subVerticesQ subVerticesQ
  let qsA := Allocation.starQsQ F x
  let qsR := starQsQ F x
  have h_qs : qsA.1=qsR.1 ∧ qsA.2≤qsR.2 := by
    change (Allocation.starQsQ F x).1=(starQsQ F x).1 ∧ (Allocation.starQsQ F x).2≤(starQsQ F x).2
    exact ⟨allocation_starQsQ_value F x, allocation_starQsQ_le F x⟩
  let zsA := Allocation.starZsQ F x
  let zsR := starZsQ F x
  have h_zs : zsA.1=zsR.1 ∧ zsA.2≤zsR.2 := by
    change (Allocation.starZsQ F x).1=(starZsQ F x).1 ∧ (Allocation.starZsQ F x).2≤(starZsQ F x).2
    exact ⟨allocation_starZsQ_value F x, allocation_starZsQ_le F x⟩
  let sidesA := Allocation.starSidesQ F x
  let sidesR := starSidesQ F x
  have h_sides : sidesA.1=sidesR.1 ∧ sidesA.2≤ sidesR.2 := by
    change (Allocation.starSidesQ F x).1=(starSidesQ F x).1 ∧ (Allocation.starSidesQ F x).2≤(starSidesQ F x).2
    exact ⟨allocation_starSidesQ_value F x, allocation_starSidesQ_le F x⟩
  let facesA := Allocation.facesAtXQ F x
  let facesR := facesAtXQ F x
  have h_faces : facesA.1=facesR.1 ∧ facesA.2≤facesR.2 := by
    change (Allocation.facesAtXQ F x).1=(facesAtXQ F x).1 ∧ (Allocation.facesAtXQ F x).2≤(facesAtXQ F x).2
    exact ⟨allocation_facesAtXQ_value F x, allocation_facesAtXQ_le F x⟩
  let qvA := Allocation.mapQ (fun q => Allocation.emitQ {owner:=x,part:=1,p:=q}) qsA.1
  let qvR := mapQ (fun q => emitQ {owner:=x,part:=1,p:=q}) qsR.1
  have h_qv : qvA.1=qvR.1 ∧ qvA.2≤qvR.2 := by
    change (Allocation.mapQ (fun q => Allocation.emitQ {owner:=x,part:=1,p:=q}) qsA.1).1=(mapQ (fun q => emitQ {owner:=x,part:=1,p:=q}) qsR.1).1 ∧ (Allocation.mapQ (fun q => Allocation.emitQ {owner:=x,part:=1,p:=q}) qsA.1).2≤(mapQ (fun q => emitQ {owner:=x,part:=1,p:=q}) qsR.1).2
    rw [h_qs.1]
    apply native_map_simulation
    intro q
    exact ⟨allocation_emitQ_value {owner:=x,part:=1,p:=q}, allocation_emitQ_le {owner:=x,part:=1,p:=q}⟩
  let zvA := Allocation.mapQ (fun z => Allocation.emitQ {owner:=x,part:=2,p:=z}) zsA.1
  let zvR := mapQ (fun z => emitQ {owner:=x,part:=2,p:=z}) zsR.1
  have h_zv : zvA.1=zvR.1 ∧ zvA.2≤zvR.2 := by
    change (Allocation.mapQ (fun z => Allocation.emitQ {owner:=x,part:=2,p:=z}) zsA.1).1=(mapQ (fun z => emitQ {owner:=x,part:=2,p:=z}) zsR.1).1 ∧ (Allocation.mapQ (fun z => Allocation.emitQ {owner:=x,part:=2,p:=z}) zsA.1).2≤(mapQ (fun z => emitQ {owner:=x,part:=2,p:=z}) zsR.1).2
    rw [h_zs.1]
    apply native_map_simulation
    intro z
    exact ⟨allocation_emitQ_value {owner:=x,part:=2,p:=z}, allocation_emitQ_le {owner:=x,part:=2,p:=z}⟩
  let radialA := Allocation.flatMapQ (fun q => Allocation.loopQ (m-1) (fun i =>
    Allocation.singletonQ {owner:=x,part:=3,p:=q,i:=i})) qsA.1
  let radialR := flatMapQ (fun q => loopQ (m-1) (fun i =>
    singletonQ {owner:=x,part:=3,p:=q,i:=i})) qsR.1
  have h_radial : radialA.1=radialR.1 ∧ radialA.2≤radialR.2 := by
    change (Allocation.flatMapQ (fun q => Allocation.loopQ (m-1) (fun i =>
    Allocation.singletonQ {owner:=x,part:=3,p:=q,i:=i})) qsA.1).1=(flatMapQ (fun q => loopQ (m-1) (fun i =>
    singletonQ {owner:=x,part:=3,p:=q,i:=i})) qsR.1).1 ∧ (Allocation.flatMapQ (fun q => Allocation.loopQ (m-1) (fun i =>
    Allocation.singletonQ {owner:=x,part:=3,p:=q,i:=i})) qsA.1).2≤(flatMapQ (fun q => loopQ (m-1) (fun i =>
    singletonQ {owner:=x,part:=3,p:=q,i:=i})) qsR.1).2
    rw [h_qs.1]
    apply native_flat_simulation
    intro q
    apply native_loop_simulation
    intro i
    exact ⟨allocation_singletonQ_value {owner:=x,part:=3,p:=q,i:=i}, allocation_singletonQ_le {owner:=x,part:=3,p:=q,i:=i}⟩
  let sideA := Allocation.flatMapQ (fun e => Allocation.loopQ (m-1) (fun i =>
    Allocation.singletonQ {owner:=x,part:=4,p:=e.1,q:=e.2,i:=i})) sidesA.1
  let sideR := flatMapQ (fun e => loopQ (m-1) (fun i =>
    singletonQ {owner:=x,part:=4,p:=e.1,q:=e.2,i:=i})) sidesR.1
  have h_side : sideA.1=sideR.1 ∧ sideA.2≤ sideR.2 := by
    change (Allocation.flatMapQ (fun e => Allocation.loopQ (m-1) (fun i =>
    Allocation.singletonQ {owner:=x,part:=4,p:=e.1,q:=e.2,i:=i})) sidesA.1).1=(flatMapQ (fun e => loopQ (m-1) (fun i =>
    singletonQ {owner:=x,part:=4,p:=e.1,q:=e.2,i:=i})) sidesR.1).1 ∧ (Allocation.flatMapQ (fun e => Allocation.loopQ (m-1) (fun i =>
    Allocation.singletonQ {owner:=x,part:=4,p:=e.1,q:=e.2,i:=i})) sidesA.1).2≤(flatMapQ (fun e => loopQ (m-1) (fun i =>
    singletonQ {owner:=x,part:=4,p:=e.1,q:=e.2,i:=i})) sidesR.1).2
    rw [h_sides.1]
    apply native_flat_simulation
    intro e
    apply native_loop_simulation
    intro i
    exact ⟨allocation_singletonQ_value {owner:=x,part:=4,p:=e.1,q:=e.2,i:=i}, allocation_singletonQ_le {owner:=x,part:=4,p:=e.1,q:=e.2,i:=i}⟩
  let bulkA := Allocation.flatMapQ (fun f => Allocation.loopQ (m-1) (fun i => Allocation.loopQ (m-1) (fun j =>
    Allocation.singletonQ {owner:=x,part:=5,p:=f.1,i:=i,j:=j}))) facesA.1
  let bulkR := flatMapQ (fun f => loopQ (m-1) (fun i => loopQ (m-1) (fun j =>
    singletonQ {owner:=x,part:=5,p:=f.1,i:=i,j:=j}))) facesR.1
  have h_bulk : bulkA.1=bulkR.1 ∧ bulkA.2≤bulkR.2 := by
    change (Allocation.flatMapQ (fun f => Allocation.loopQ (m-1) (fun i => Allocation.loopQ (m-1) (fun j =>
    Allocation.singletonQ {owner:=x,part:=5,p:=f.1,i:=i,j:=j}))) facesA.1).1=(flatMapQ (fun f => loopQ (m-1) (fun i => loopQ (m-1) (fun j =>
    singletonQ {owner:=x,part:=5,p:=f.1,i:=i,j:=j}))) facesR.1).1 ∧ (Allocation.flatMapQ (fun f => Allocation.loopQ (m-1) (fun i => Allocation.loopQ (m-1) (fun j =>
    Allocation.singletonQ {owner:=x,part:=5,p:=f.1,i:=i,j:=j}))) facesA.1).2≤(flatMapQ (fun f => loopQ (m-1) (fun i => loopQ (m-1) (fun j =>
    singletonQ {owner:=x,part:=5,p:=f.1,i:=i,j:=j}))) facesR.1).2
    rw [h_faces.1]
    apply native_flat_simulation
    intro f
    apply native_loop_simulation
    intro i
    apply native_loop_simulation
    intro j
    exact ⟨allocation_singletonQ_value {owner:=x,part:=5,p:=f.1,i:=i,j:=j}, allocation_singletonQ_le {owner:=x,part:=5,p:=f.1,i:=i,j:=j}⟩
  let outA := Allocation.collectQ [Allocation.singletonQ {owner:=x},qvA,zvA,radialA,sideA,bulkA]
  let outR := collectQ [singletonQ {owner:=x},qvR,zvR,radialR,sideR,bulkR]
  have h_out : outA.1=outR.1 ∧ outA.2≤outR.2 := by
    change (Allocation.collectQ [Allocation.singletonQ {owner:=x},qvA,zvA,radialA,sideA,bulkA]).1=(collectQ [singletonQ {owner:=x},qvR,zvR,radialR,sideR,bulkR]).1 ∧ (Allocation.collectQ [Allocation.singletonQ {owner:=x},qvA,zvA,radialA,sideA,bulkA]).2≤(collectQ [singletonQ {owner:=x},qvR,zvR,radialR,sideR,bulkR]).2
    have hi0 : (Allocation.singletonQ {owner:=x}).1=(singletonQ {owner:=x}).1 ∧ (Allocation.singletonQ {owner:=x}).2≤(singletonQ {owner:=x}).2 := by
      exact ⟨allocation_singletonQ_value {owner:=x}, allocation_singletonQ_le {owner:=x}⟩
    have hi1 : (qvA).1=(qvR).1 ∧ (qvA).2≤(qvR).2 := by
      exact h_qv
    have hi2 : (zvA).1=(zvR).1 ∧ (zvA).2≤(zvR).2 := by
      exact h_zv
    have hi3 : (radialA).1=(radialR).1 ∧ (radialA).2≤(radialR).2 := by
      exact h_radial
    have hi4 : (sideA).1=(sideR).1 ∧ (sideA).2≤(sideR).2 := by
      exact h_side
    have hi5 : (bulkA).1=(bulkR).1 ∧ (bulkA).2≤(bulkR).2 := by
      exact h_bulk
    apply native_collect_simulation
    · change [(Allocation.singletonQ {owner:=x}).1, (qvA).1, (zvA).1, (radialA).1, (sideA).1, (bulkA).1]=[(singletonQ {owner:=x}).1, (qvR).1, (zvR).1, (radialR).1, (sideR).1, (bulkR).1]
      exact congrArg₂ List.cons hi0.1 (congrArg₂ List.cons hi1.1 (congrArg₂ List.cons hi2.1 (congrArg₂ List.cons hi3.1 (congrArg₂ List.cons hi4.1 (congrArg₂ List.cons hi5.1 (rfl))))))
    · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      have hc0 := hi0.2
      have hc1 := hi1.2
      have hc2 := hi2.2
      have hc3 := hi3.2
      have hc4 := hi4.2
      have hc5 := hi5.2
      omega
  constructor
  · change outA.1=outR.1
    simpa only [h_out.1]
  · change qsA.2+zsA.2+sidesA.2+facesA.2+outA.2≤qsR.2+zsR.2+sidesR.2+facesR.2+outR.2
    have hc0 := h_qs.2
    have hc1 := h_zs.2
    have hc2 := h_sides.2
    have hc3 := h_faces.2
    have hc4 := h_out.2
    omega
theorem allocation_subVerticesQ_value (F : Frame) (x m : ℕ) :
    (Allocation.subVerticesQ F x m).1=(subVerticesQ F x m).1 := by
  exact (native_subVerticesQ_simulation F x m).1
attribute [local simp] allocation_subVerticesQ_value
theorem allocation_subVerticesQ_le (F : Frame) (x m : ℕ) :
    (Allocation.subVerticesQ F x m).2≤(subVerticesQ F x m).2 := by
  exact (native_subVerticesQ_simulation F x m).2
theorem native_subEdgesQ_simulation (F : Frame) (x m : ℕ) :
    (Allocation.subEdgesQ F x m).1=(subEdgesQ F x m).1 ∧ (Allocation.subEdgesQ F x m).2≤(subEdgesQ F x m).2 := by
  unfold Allocation.subEdgesQ subEdgesQ
  let qsA := Allocation.starQsQ F x
  let qsR := starQsQ F x
  have h_qs : qsA.1=qsR.1 ∧ qsA.2≤qsR.2 := by
    change (Allocation.starQsQ F x).1=(starQsQ F x).1 ∧ (Allocation.starQsQ F x).2≤(starQsQ F x).2
    exact ⟨allocation_starQsQ_value F x, allocation_starQsQ_le F x⟩
  let sidesA := Allocation.starSidesQ F x
  let sidesR := starSidesQ F x
  have h_sides : sidesA.1=sidesR.1 ∧ sidesA.2≤ sidesR.2 := by
    change (Allocation.starSidesQ F x).1=(starSidesQ F x).1 ∧ (Allocation.starSidesQ F x).2≤(starSidesQ F x).2
    exact ⟨allocation_starSidesQ_value F x, allocation_starSidesQ_le F x⟩
  let facesA := Allocation.facesAtXQ F x
  let facesR := facesAtXQ F x
  have h_faces : facesA.1=facesR.1 ∧ facesA.2≤facesR.2 := by
    change (Allocation.facesAtXQ F x).1=(facesAtXQ F x).1 ∧ (Allocation.facesAtXQ F x).2≤(facesAtXQ F x).2
    exact ⟨allocation_facesAtXQ_value F x, allocation_facesAtXQ_le F x⟩
  let radialA := Allocation.flatMapQ (fun q => Allocation.loopQ m (fun i =>
    Allocation.singletonQ {owner:=x,p:=q,i:=i})) qsA.1
  let radialR := flatMapQ (fun q => loopQ m (fun i =>
    singletonQ {owner:=x,p:=q,i:=i})) qsR.1
  have h_radial : radialA.1=radialR.1 ∧ radialA.2≤radialR.2 := by
    change (Allocation.flatMapQ (fun q => Allocation.loopQ m (fun i =>
    Allocation.singletonQ {owner:=x,p:=q,i:=i})) qsA.1).1=(flatMapQ (fun q => loopQ m (fun i =>
    singletonQ {owner:=x,p:=q,i:=i})) qsR.1).1 ∧ (Allocation.flatMapQ (fun q => Allocation.loopQ m (fun i =>
    Allocation.singletonQ {owner:=x,p:=q,i:=i})) qsA.1).2≤(flatMapQ (fun q => loopQ m (fun i =>
    singletonQ {owner:=x,p:=q,i:=i})) qsR.1).2
    rw [h_qs.1]
    apply native_flat_simulation
    intro q
    apply native_loop_simulation
    intro i
    exact ⟨allocation_singletonQ_value {owner:=x,p:=q,i:=i}, allocation_singletonQ_le {owner:=x,p:=q,i:=i}⟩
  let sideA := Allocation.flatMapQ (fun e => Allocation.loopQ m (fun i =>
    Allocation.singletonQ {owner:=x,part:=1,p:=e.1,q:=e.2,i:=i})) sidesA.1
  let sideR := flatMapQ (fun e => loopQ m (fun i =>
    singletonQ {owner:=x,part:=1,p:=e.1,q:=e.2,i:=i})) sidesR.1
  have h_side : sideA.1=sideR.1 ∧ sideA.2≤ sideR.2 := by
    change (Allocation.flatMapQ (fun e => Allocation.loopQ m (fun i =>
    Allocation.singletonQ {owner:=x,part:=1,p:=e.1,q:=e.2,i:=i})) sidesA.1).1=(flatMapQ (fun e => loopQ m (fun i =>
    singletonQ {owner:=x,part:=1,p:=e.1,q:=e.2,i:=i})) sidesR.1).1 ∧ (Allocation.flatMapQ (fun e => Allocation.loopQ m (fun i =>
    Allocation.singletonQ {owner:=x,part:=1,p:=e.1,q:=e.2,i:=i})) sidesA.1).2≤(flatMapQ (fun e => loopQ m (fun i =>
    singletonQ {owner:=x,part:=1,p:=e.1,q:=e.2,i:=i})) sidesR.1).2
    rw [h_sides.1]
    apply native_flat_simulation
    intro e
    apply native_loop_simulation
    intro i
    exact ⟨allocation_singletonQ_value {owner:=x,part:=1,p:=e.1,q:=e.2,i:=i}, allocation_singletonQ_le {owner:=x,part:=1,p:=e.1,q:=e.2,i:=i}⟩
  let horizontalA := Allocation.flatMapQ (fun f => Allocation.loopQ m (fun i => Allocation.loopQ (m-1) (fun j =>
    Allocation.singletonQ {owner:=x,part:=2,p:=f.1,i:=i,j:=j}))) facesA.1
  let horizontalR := flatMapQ (fun f => loopQ m (fun i => loopQ (m-1) (fun j =>
    singletonQ {owner:=x,part:=2,p:=f.1,i:=i,j:=j}))) facesR.1
  have h_horizontal : horizontalA.1=horizontalR.1 ∧ horizontalA.2≤horizontalR.2 := by
    change (Allocation.flatMapQ (fun f => Allocation.loopQ m (fun i => Allocation.loopQ (m-1) (fun j =>
    Allocation.singletonQ {owner:=x,part:=2,p:=f.1,i:=i,j:=j}))) facesA.1).1=(flatMapQ (fun f => loopQ m (fun i => loopQ (m-1) (fun j =>
    singletonQ {owner:=x,part:=2,p:=f.1,i:=i,j:=j}))) facesR.1).1 ∧ (Allocation.flatMapQ (fun f => Allocation.loopQ m (fun i => Allocation.loopQ (m-1) (fun j =>
    Allocation.singletonQ {owner:=x,part:=2,p:=f.1,i:=i,j:=j}))) facesA.1).2≤(flatMapQ (fun f => loopQ m (fun i => loopQ (m-1) (fun j =>
    singletonQ {owner:=x,part:=2,p:=f.1,i:=i,j:=j}))) facesR.1).2
    rw [h_faces.1]
    apply native_flat_simulation
    intro f
    apply native_loop_simulation
    intro i
    apply native_loop_simulation
    intro j
    exact ⟨allocation_singletonQ_value {owner:=x,part:=2,p:=f.1,i:=i,j:=j}, allocation_singletonQ_le {owner:=x,part:=2,p:=f.1,i:=i,j:=j}⟩
  let verticalA := Allocation.flatMapQ (fun f => Allocation.loopQ (m-1) (fun i => Allocation.loopQ m (fun j =>
    Allocation.singletonQ {owner:=x,part:=3,p:=f.1,i:=i,j:=j}))) facesA.1
  let verticalR := flatMapQ (fun f => loopQ (m-1) (fun i => loopQ m (fun j =>
    singletonQ {owner:=x,part:=3,p:=f.1,i:=i,j:=j}))) facesR.1
  have h_vertical : verticalA.1=verticalR.1 ∧ verticalA.2≤verticalR.2 := by
    change (Allocation.flatMapQ (fun f => Allocation.loopQ (m-1) (fun i => Allocation.loopQ m (fun j =>
    Allocation.singletonQ {owner:=x,part:=3,p:=f.1,i:=i,j:=j}))) facesA.1).1=(flatMapQ (fun f => loopQ (m-1) (fun i => loopQ m (fun j =>
    singletonQ {owner:=x,part:=3,p:=f.1,i:=i,j:=j}))) facesR.1).1 ∧ (Allocation.flatMapQ (fun f => Allocation.loopQ (m-1) (fun i => Allocation.loopQ m (fun j =>
    Allocation.singletonQ {owner:=x,part:=3,p:=f.1,i:=i,j:=j}))) facesA.1).2≤(flatMapQ (fun f => loopQ (m-1) (fun i => loopQ m (fun j =>
    singletonQ {owner:=x,part:=3,p:=f.1,i:=i,j:=j}))) facesR.1).2
    rw [h_faces.1]
    apply native_flat_simulation
    intro f
    apply native_loop_simulation
    intro i
    apply native_loop_simulation
    intro j
    exact ⟨allocation_singletonQ_value {owner:=x,part:=3,p:=f.1,i:=i,j:=j}, allocation_singletonQ_le {owner:=x,part:=3,p:=f.1,i:=i,j:=j}⟩
  let outA := Allocation.collectQ [radialA,sideA,horizontalA,verticalA]
  let outR := collectQ [radialR,sideR,horizontalR,verticalR]
  have h_out : outA.1=outR.1 ∧ outA.2≤outR.2 := by
    change (Allocation.collectQ [radialA,sideA,horizontalA,verticalA]).1=(collectQ [radialR,sideR,horizontalR,verticalR]).1 ∧ (Allocation.collectQ [radialA,sideA,horizontalA,verticalA]).2≤(collectQ [radialR,sideR,horizontalR,verticalR]).2
    have hi0 : (radialA).1=(radialR).1 ∧ (radialA).2≤(radialR).2 := by
      exact h_radial
    have hi1 : (sideA).1=(sideR).1 ∧ (sideA).2≤(sideR).2 := by
      exact h_side
    have hi2 : (horizontalA).1=(horizontalR).1 ∧ (horizontalA).2≤(horizontalR).2 := by
      exact h_horizontal
    have hi3 : (verticalA).1=(verticalR).1 ∧ (verticalA).2≤(verticalR).2 := by
      exact h_vertical
    apply native_collect_simulation
    · change [(radialA).1, (sideA).1, (horizontalA).1, (verticalA).1]=[(radialR).1, (sideR).1, (horizontalR).1, (verticalR).1]
      exact congrArg₂ List.cons hi0.1 (congrArg₂ List.cons hi1.1 (congrArg₂ List.cons hi2.1 (congrArg₂ List.cons hi3.1 (rfl))))
    · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      have hc0 := hi0.2
      have hc1 := hi1.2
      have hc2 := hi2.2
      have hc3 := hi3.2
      omega
  constructor
  · change outA.1=outR.1
    simpa only [h_out.1]
  · change qsA.2+sidesA.2+facesA.2+outA.2≤qsR.2+sidesR.2+facesR.2+outR.2
    have hc0 := h_qs.2
    have hc1 := h_sides.2
    have hc2 := h_faces.2
    have hc3 := h_out.2
    omega
theorem allocation_subEdgesQ_value (F : Frame) (x m : ℕ) :
    (Allocation.subEdgesQ F x m).1=(subEdgesQ F x m).1 := by
  exact (native_subEdgesQ_simulation F x m).1
attribute [local simp] allocation_subEdgesQ_value
theorem allocation_subEdgesQ_le (F : Frame) (x m : ℕ) :
    (Allocation.subEdgesQ F x m).2≤(subEdgesQ F x m).2 := by
  exact (native_subEdgesQ_simulation F x m).2
theorem native_subFacesQ_simulation (F : Frame) (x m : ℕ) :
    (Allocation.subFacesQ F x m).1=(subFacesQ F x m).1 ∧ (Allocation.subFacesQ F x m).2≤(subFacesQ F x m).2 := by
  unfold Allocation.subFacesQ subFacesQ
  let facesA := Allocation.facesAtXQ F x
  let facesR := facesAtXQ F x
  have h_faces : facesA.1=facesR.1 ∧ facesA.2≤facesR.2 := by
    change (Allocation.facesAtXQ F x).1=(facesAtXQ F x).1 ∧ (Allocation.facesAtXQ F x).2≤(facesAtXQ F x).2
    exact ⟨allocation_facesAtXQ_value F x, allocation_facesAtXQ_le F x⟩
  let outA := Allocation.flatMapQ (fun f => Allocation.loopQ m (fun i => Allocation.loopQ m (fun j =>
    Allocation.singletonQ {owner:=x,p:=f.1,i:=i,j:=j}))) facesA.1
  let outR := flatMapQ (fun f => loopQ m (fun i => loopQ m (fun j =>
    singletonQ {owner:=x,p:=f.1,i:=i,j:=j}))) facesR.1
  have h_out : outA.1=outR.1 ∧ outA.2≤outR.2 := by
    change (Allocation.flatMapQ (fun f => Allocation.loopQ m (fun i => Allocation.loopQ m (fun j =>
    Allocation.singletonQ {owner:=x,p:=f.1,i:=i,j:=j}))) facesA.1).1=(flatMapQ (fun f => loopQ m (fun i => loopQ m (fun j =>
    singletonQ {owner:=x,p:=f.1,i:=i,j:=j}))) facesR.1).1 ∧ (Allocation.flatMapQ (fun f => Allocation.loopQ m (fun i => Allocation.loopQ m (fun j =>
    Allocation.singletonQ {owner:=x,p:=f.1,i:=i,j:=j}))) facesA.1).2≤(flatMapQ (fun f => loopQ m (fun i => loopQ m (fun j =>
    singletonQ {owner:=x,p:=f.1,i:=i,j:=j}))) facesR.1).2
    rw [h_faces.1]
    apply native_flat_simulation
    intro f
    apply native_loop_simulation
    intro i
    apply native_loop_simulation
    intro j
    exact ⟨allocation_singletonQ_value {owner:=x,p:=f.1,i:=i,j:=j}, allocation_singletonQ_le {owner:=x,p:=f.1,i:=i,j:=j}⟩
  constructor
  · change outA.1=outR.1
    simpa only [h_out.1]
  · change facesA.2+outA.2≤facesR.2+outR.2
    have hc0 := h_faces.2
    have hc1 := h_out.2
    omega
theorem allocation_subFacesQ_value (F : Frame) (x m : ℕ) :
    (Allocation.subFacesQ F x m).1=(subFacesQ F x m).1 := by
  exact (native_subFacesQ_simulation F x m).1
attribute [local simp] allocation_subFacesQ_value
theorem allocation_subFacesQ_le (F : Frame) (x m : ℕ) :
    (Allocation.subFacesQ F x m).2≤(subFacesQ F x m).2 := by
  exact (native_subFacesQ_simulation F x m).2
theorem native_doubleVerticesQ_simulation (F : Frame) (x m : ℕ) :
    (Allocation.doubleVerticesQ F x m).1=(doubleVerticesQ F x m).1 ∧ (Allocation.doubleVerticesQ F x m).2≤(doubleVerticesQ F x m).2 := by
  unfold Allocation.doubleVerticesQ doubleVerticesQ
  let cellsA := Allocation.subVerticesQ F x m
  let cellsR := subVerticesQ F x m
  have h_cells : cellsA.1=cellsR.1 ∧ cellsA.2≤cellsR.2 := by
    change (Allocation.subVerticesQ F x m).1=(subVerticesQ F x m).1 ∧ (Allocation.subVerticesQ F x m).2≤(subVerticesQ F x m).2
    exact ⟨allocation_subVerticesQ_value F x m, allocation_subVerticesQ_le F x m⟩
  let copiesA := Allocation.flatMapQ (fun c => Allocation.mapCodesQ (fun v => {v with copy:=c}) cellsA.1) [0,1]
  let copiesR := flatMapQ (fun c => mapCodesQ (fun v => {v with copy:=c}) cellsR.1) [0,1]
  have h_copies : copiesA.1=copiesR.1 ∧ copiesA.2≤copiesR.2 := by
    change (Allocation.flatMapQ (fun c => Allocation.mapCodesQ (fun v => {v with copy:=c}) cellsA.1) [0,1]).1=(flatMapQ (fun c => mapCodesQ (fun v => {v with copy:=c}) cellsR.1) [0,1]).1 ∧ (Allocation.flatMapQ (fun c => Allocation.mapCodesQ (fun v => {v with copy:=c}) cellsA.1) [0,1]).2≤(flatMapQ (fun c => mapCodesQ (fun v => {v with copy:=c}) cellsR.1) [0,1]).2
    rw [h_cells.1]
    apply native_flat_simulation
    intro c
    exact ⟨allocation_mapCodesQ_value (fun v => {v with copy:=c}) cellsR.1, allocation_mapCodesQ_le (fun v => {v with copy:=c}) cellsR.1⟩
  constructor
  · change copiesA.1=copiesR.1
    simpa only [h_copies.1]
  · change cellsA.2+copiesA.2≤cellsR.2+copiesR.2
    have hc0 := h_cells.2
    have hc1 := h_copies.2
    omega
theorem allocation_doubleVerticesQ_value (F : Frame) (x m : ℕ) :
    (Allocation.doubleVerticesQ F x m).1=(doubleVerticesQ F x m).1 := by
  exact (native_doubleVerticesQ_simulation F x m).1
attribute [local simp] allocation_doubleVerticesQ_value
theorem allocation_doubleVerticesQ_le (F : Frame) (x m : ℕ) :
    (Allocation.doubleVerticesQ F x m).2≤(doubleVerticesQ F x m).2 := by
  exact (native_doubleVerticesQ_simulation F x m).2
theorem native_doubleEdgesQ_simulation (F : Frame) (x m : ℕ) :
    (Allocation.doubleEdgesQ F x m).1=(doubleEdgesQ F x m).1 ∧ (Allocation.doubleEdgesQ F x m).2≤(doubleEdgesQ F x m).2 := by
  unfold Allocation.doubleEdgesQ doubleEdgesQ
  let edgesA := Allocation.subEdgesQ F x m
  let edgesR := subEdgesQ F x m
  have h_edges : edgesA.1=edgesR.1 ∧ edgesA.2≤edgesR.2 := by
    change (Allocation.subEdgesQ F x m).1=(subEdgesQ F x m).1 ∧ (Allocation.subEdgesQ F x m).2≤(subEdgesQ F x m).2
    exact ⟨allocation_subEdgesQ_value F x m, allocation_subEdgesQ_le F x m⟩
  let verticesA := Allocation.subVerticesQ F x m
  let verticesR := subVerticesQ F x m
  have h_vertices : verticesA.1=verticesR.1 ∧ verticesA.2≤verticesR.2 := by
    change (Allocation.subVerticesQ F x m).1=(subVerticesQ F x m).1 ∧ (Allocation.subVerticesQ F x m).2≤(subVerticesQ F x m).2
    exact ⟨allocation_subVerticesQ_value F x m, allocation_subVerticesQ_le F x m⟩
  let endsA := Allocation.flatMapQ (fun c => Allocation.mapCodesQ (fun e => {e with copy:=c}) edgesA.1) [0,1]
  let endsR := flatMapQ (fun c => mapCodesQ (fun e => {e with copy:=c}) edgesR.1) [0,1]
  have h_ends : endsA.1=endsR.1 ∧ endsA.2≤endsR.2 := by
    change (Allocation.flatMapQ (fun c => Allocation.mapCodesQ (fun e => {e with copy:=c}) edgesA.1) [0,1]).1=(flatMapQ (fun c => mapCodesQ (fun e => {e with copy:=c}) edgesR.1) [0,1]).1 ∧ (Allocation.flatMapQ (fun c => Allocation.mapCodesQ (fun e => {e with copy:=c}) edgesA.1) [0,1]).2≤(flatMapQ (fun c => mapCodesQ (fun e => {e with copy:=c}) edgesR.1) [0,1]).2
    rw [h_edges.1]
    apply native_flat_simulation
    intro c
    exact ⟨allocation_mapCodesQ_value (fun e => {e with copy:=c}) edgesR.1, allocation_mapCodesQ_le (fun e => {e with copy:=c}) edgesR.1⟩
  let boundaryA := Allocation.filterQ (fun v => (decide (v.part=1 ∨ v.part=2 ∨ v.part=4),0)) verticesA.1
  let boundaryR := filterQ (fun v => (decide (v.part=1 ∨ v.part=2 ∨ v.part=4),7)) verticesR.1
  have h_boundary : boundaryA.1=boundaryR.1 ∧ boundaryA.2≤boundaryR.2 := by
    change (Allocation.filterQ (fun v => (decide (v.part=1 ∨ v.part=2 ∨ v.part=4),0)) verticesA.1).1=(filterQ (fun v => (decide (v.part=1 ∨ v.part=2 ∨ v.part=4),7)) verticesR.1).1 ∧ (Allocation.filterQ (fun v => (decide (v.part=1 ∨ v.part=2 ∨ v.part=4),0)) verticesA.1).2≤(filterQ (fun v => (decide (v.part=1 ∨ v.part=2 ∨ v.part=4),7)) verticesR.1).2
    rw [h_vertices.1]
    apply native_filter_simulation
    intro v
    constructor
    · change decide (v.part=1 ∨ v.part=2 ∨ v.part=4)=decide (v.part=1 ∨ v.part=2 ∨ v.part=4)
      rfl
    · change 0≤7
      omega
  let bridgeA := Allocation.mapCodesQ (fun v =>
    {v with part:=if v.part=1 then 4 else if v.part=2 then 5 else 6}) boundaryA.1
  let bridgeR := mapCodesQ (fun v =>
    {v with part:=if v.part=1 then 4 else if v.part=2 then 5 else 6}) boundaryR.1
  have h_bridge : bridgeA.1=bridgeR.1 ∧ bridgeA.2≤bridgeR.2 := by
    change (Allocation.mapCodesQ (fun v =>
    {v with part:=if v.part=1 then 4 else if v.part=2 then 5 else 6}) boundaryA.1).1=(mapCodesQ (fun v =>
    {v with part:=if v.part=1 then 4 else if v.part=2 then 5 else 6}) boundaryR.1).1 ∧ (Allocation.mapCodesQ (fun v =>
    {v with part:=if v.part=1 then 4 else if v.part=2 then 5 else 6}) boundaryA.1).2≤(mapCodesQ (fun v =>
    {v with part:=if v.part=1 then 4 else if v.part=2 then 5 else 6}) boundaryR.1).2
    rw [h_boundary.1]
    exact ⟨allocation_mapCodesQ_value (fun v =>
    {v with part:=if v.part=1 then 4 else if v.part=2 then 5 else 6}) boundaryR.1, allocation_mapCodesQ_le (fun v =>
    {v with part:=if v.part=1 then 4 else if v.part=2 then 5 else 6}) boundaryR.1⟩
  let outA := Allocation.collectQ [endsA,bridgeA]
  let outR := collectQ [endsR,bridgeR]
  have h_out : outA.1=outR.1 ∧ outA.2≤outR.2 := by
    change (Allocation.collectQ [endsA,bridgeA]).1=(collectQ [endsR,bridgeR]).1 ∧ (Allocation.collectQ [endsA,bridgeA]).2≤(collectQ [endsR,bridgeR]).2
    have hi0 : (endsA).1=(endsR).1 ∧ (endsA).2≤(endsR).2 := by
      exact h_ends
    have hi1 : (bridgeA).1=(bridgeR).1 ∧ (bridgeA).2≤(bridgeR).2 := by
      exact h_bridge
    apply native_collect_simulation
    · change [(endsA).1, (bridgeA).1]=[(endsR).1, (bridgeR).1]
      exact congrArg₂ List.cons hi0.1 (congrArg₂ List.cons hi1.1 (rfl))
    · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      have hc0 := hi0.2
      have hc1 := hi1.2
      omega
  constructor
  · change outA.1=outR.1
    simpa only [h_out.1]
  · change edgesA.2+verticesA.2+boundaryA.2+outA.2≤edgesR.2+verticesR.2+boundaryR.2+outR.2
    have hc0 := h_edges.2
    have hc1 := h_vertices.2
    have hc2 := h_boundary.2
    have hc3 := h_out.2
    omega
theorem allocation_doubleEdgesQ_value (F : Frame) (x m : ℕ) :
    (Allocation.doubleEdgesQ F x m).1=(doubleEdgesQ F x m).1 := by
  exact (native_doubleEdgesQ_simulation F x m).1
attribute [local simp] allocation_doubleEdgesQ_value
theorem allocation_doubleEdgesQ_le (F : Frame) (x m : ℕ) :
    (Allocation.doubleEdgesQ F x m).2≤(doubleEdgesQ F x m).2 := by
  exact (native_doubleEdgesQ_simulation F x m).2
theorem native_doubleFacesQ_simulation (F : Frame) (x m : ℕ) :
    (Allocation.doubleFacesQ F x m).1=(doubleFacesQ F x m).1 ∧ (Allocation.doubleFacesQ F x m).2≤(doubleFacesQ F x m).2 := by
  unfold Allocation.doubleFacesQ doubleFacesQ
  let facesA := Allocation.subFacesQ F x m
  let facesR := subFacesQ F x m
  have h_faces : facesA.1=facesR.1 ∧ facesA.2≤facesR.2 := by
    change (Allocation.subFacesQ F x m).1=(subFacesQ F x m).1 ∧ (Allocation.subFacesQ F x m).2≤(subFacesQ F x m).2
    exact ⟨allocation_subFacesQ_value F x m, allocation_subFacesQ_le F x m⟩
  let sidesA := Allocation.starSidesQ F x
  let sidesR := starSidesQ F x
  have h_sides : sidesA.1=sidesR.1 ∧ sidesA.2≤ sidesR.2 := by
    change (Allocation.starSidesQ F x).1=(starSidesQ F x).1 ∧ (Allocation.starSidesQ F x).2≤(starSidesQ F x).2
    exact ⟨allocation_starSidesQ_value F x, allocation_starSidesQ_le F x⟩
  let endsA := Allocation.flatMapQ (fun c => Allocation.mapCodesQ (fun f => {f with copy:=c}) facesA.1) [0,1]
  let endsR := flatMapQ (fun c => mapCodesQ (fun f => {f with copy:=c}) facesR.1) [0,1]
  have h_ends : endsA.1=endsR.1 ∧ endsA.2≤endsR.2 := by
    change (Allocation.flatMapQ (fun c => Allocation.mapCodesQ (fun f => {f with copy:=c}) facesA.1) [0,1]).1=(flatMapQ (fun c => mapCodesQ (fun f => {f with copy:=c}) facesR.1) [0,1]).1 ∧ (Allocation.flatMapQ (fun c => Allocation.mapCodesQ (fun f => {f with copy:=c}) facesA.1) [0,1]).2≤(flatMapQ (fun c => mapCodesQ (fun f => {f with copy:=c}) facesR.1) [0,1]).2
    rw [h_faces.1]
    apply native_flat_simulation
    intro c
    exact ⟨allocation_mapCodesQ_value (fun f => {f with copy:=c}) facesR.1, allocation_mapCodesQ_le (fun f => {f with copy:=c}) facesR.1⟩
  let rectA := Allocation.flatMapQ (fun e => Allocation.loopQ m (fun i =>
    Allocation.singletonQ {owner:=x,part:=1,p:=e.1,q:=e.2,i:=i})) sidesA.1
  let rectR := flatMapQ (fun e => loopQ m (fun i =>
    singletonQ {owner:=x,part:=1,p:=e.1,q:=e.2,i:=i})) sidesR.1
  have h_rect : rectA.1=rectR.1 ∧ rectA.2≤rectR.2 := by
    change (Allocation.flatMapQ (fun e => Allocation.loopQ m (fun i =>
    Allocation.singletonQ {owner:=x,part:=1,p:=e.1,q:=e.2,i:=i})) sidesA.1).1=(flatMapQ (fun e => loopQ m (fun i =>
    singletonQ {owner:=x,part:=1,p:=e.1,q:=e.2,i:=i})) sidesR.1).1 ∧ (Allocation.flatMapQ (fun e => Allocation.loopQ m (fun i =>
    Allocation.singletonQ {owner:=x,part:=1,p:=e.1,q:=e.2,i:=i})) sidesA.1).2≤(flatMapQ (fun e => loopQ m (fun i =>
    singletonQ {owner:=x,part:=1,p:=e.1,q:=e.2,i:=i})) sidesR.1).2
    rw [h_sides.1]
    apply native_flat_simulation
    intro e
    apply native_loop_simulation
    intro i
    exact ⟨allocation_singletonQ_value {owner:=x,part:=1,p:=e.1,q:=e.2,i:=i}, allocation_singletonQ_le {owner:=x,part:=1,p:=e.1,q:=e.2,i:=i}⟩
  let outA := Allocation.collectQ [endsA,rectA]
  let outR := collectQ [endsR,rectR]
  have h_out : outA.1=outR.1 ∧ outA.2≤outR.2 := by
    change (Allocation.collectQ [endsA,rectA]).1=(collectQ [endsR,rectR]).1 ∧ (Allocation.collectQ [endsA,rectA]).2≤(collectQ [endsR,rectR]).2
    have hi0 : (endsA).1=(endsR).1 ∧ (endsA).2≤(endsR).2 := by
      exact h_ends
    have hi1 : (rectA).1=(rectR).1 ∧ (rectA).2≤(rectR).2 := by
      exact h_rect
    apply native_collect_simulation
    · change [(endsA).1, (rectA).1]=[(endsR).1, (rectR).1]
      exact congrArg₂ List.cons hi0.1 (congrArg₂ List.cons hi1.1 (rfl))
    · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      have hc0 := hi0.2
      have hc1 := hi1.2
      omega
  constructor
  · change outA.1=outR.1
    simpa only [h_out.1]
  · change facesA.2+sidesA.2+outA.2≤facesR.2+sidesR.2+outR.2
    have hc0 := h_faces.2
    have hc1 := h_sides.2
    have hc2 := h_out.2
    omega
theorem allocation_doubleFacesQ_value (F : Frame) (x m : ℕ) :
    (Allocation.doubleFacesQ F x m).1=(doubleFacesQ F x m).1 := by
  exact (native_doubleFacesQ_simulation F x m).1
attribute [local simp] allocation_doubleFacesQ_value
theorem allocation_doubleFacesQ_le (F : Frame) (x m : ℕ) :
    (Allocation.doubleFacesQ F x m).2≤(doubleFacesQ F x m).2 := by
  exact (native_doubleFacesQ_simulation F x m).2
theorem native_qNeighborsQ_simulation (F : Frame) (q : ℕ) :
    (Allocation.qNeighborsQ F q).1=(qNeighborsQ F q).1 ∧ (Allocation.qNeighborsQ F q).2≤(qNeighborsQ F q).2 := by
  unfold Allocation.qNeighborsQ qNeighborsQ
  let idsA := Allocation.rangeQ F.nz
  let idsR := rangeQ F.nz
  have h_ids : idsA.1=idsR.1 ∧ idsA.2≤ idsR.2 := by
    change (Allocation.rangeQ F.nz).1=(rangeQ F.nz).1 ∧ (Allocation.rangeQ F.nz).2≤(rangeQ F.nz).2
    exact ⟨allocation_range_value F.nz, allocation_range_le F.nz⟩
  let outA := Allocation.filterQ (Allocation.qzQ F q) idsA.1
  let outR := filterQ (qzQ F q) idsR.1
  have h_out : outA.1=outR.1 ∧ outA.2≤outR.2 := by
    change (Allocation.filterQ (Allocation.qzQ F q) idsA.1).1=(filterQ (qzQ F q) idsR.1).1 ∧ (Allocation.filterQ (Allocation.qzQ F q) idsA.1).2≤(filterQ (qzQ F q) idsR.1).2
    rw [h_ids.1]
    apply native_filter_simulation
    intro v
    exact ⟨allocation_qzQ_value F q v, allocation_qzQ_le F q v⟩
  constructor
  · change outA.1=outR.1
    simpa only [h_out.1]
  · change idsA.2+outA.2≤ idsR.2+outR.2
    have hc0 := h_ids.2
    have hc1 := h_out.2
    omega
theorem allocation_qNeighborsQ_value (F : Frame) (q : ℕ) :
    (Allocation.qNeighborsQ F q).1=(qNeighborsQ F q).1 := by
  exact (native_qNeighborsQ_simulation F q).1
attribute [local simp] allocation_qNeighborsQ_value
theorem allocation_qNeighborsQ_le (F : Frame) (q : ℕ) :
    (Allocation.qNeighborsQ F q).2≤(qNeighborsQ F q).2 := by
  exact (native_qNeighborsQ_simulation F q).2
theorem native_qDoubleVerticesQ_simulation (F : Frame) (q m : ℕ) :
    (Allocation.qDoubleVerticesQ F q m).1=(qDoubleVerticesQ F q m).1 ∧ (Allocation.qDoubleVerticesQ F q m).2≤(qDoubleVerticesQ F q m).2 := by
  unfold Allocation.qDoubleVerticesQ qDoubleVerticesQ
  let nsA := Allocation.qNeighborsQ F q
  let nsR := qNeighborsQ F q
  have h_ns : nsA.1=nsR.1 ∧ nsA.2≤nsR.2 := by
    change (Allocation.qNeighborsQ F q).1=(qNeighborsQ F q).1 ∧ (Allocation.qNeighborsQ F q).2≤(qNeighborsQ F q).2
    exact ⟨allocation_qNeighborsQ_value F q, allocation_qNeighborsQ_le F q⟩
  let endpointA := Allocation.mapQ (fun z => Allocation.emitQ {owner:=q,part:=1,p:=z}) nsA.1
  let endpointR := mapQ (fun z => emitQ {owner:=q,part:=1,p:=z}) nsR.1
  have h_endpoint : endpointA.1=endpointR.1 ∧ endpointA.2≤endpointR.2 := by
    change (Allocation.mapQ (fun z => Allocation.emitQ {owner:=q,part:=1,p:=z}) nsA.1).1=(mapQ (fun z => emitQ {owner:=q,part:=1,p:=z}) nsR.1).1 ∧ (Allocation.mapQ (fun z => Allocation.emitQ {owner:=q,part:=1,p:=z}) nsA.1).2≤(mapQ (fun z => emitQ {owner:=q,part:=1,p:=z}) nsR.1).2
    rw [h_ns.1]
    apply native_map_simulation
    intro z
    exact ⟨allocation_emitQ_value {owner:=q,part:=1,p:=z}, allocation_emitQ_le {owner:=q,part:=1,p:=z}⟩
  let interiorA := Allocation.flatMapQ (fun z => Allocation.loopQ (m-1) (fun i =>
    Allocation.singletonQ {owner:=q,part:=2,p:=z,i:=i})) nsA.1
  let interiorR := flatMapQ (fun z => loopQ (m-1) (fun i =>
    singletonQ {owner:=q,part:=2,p:=z,i:=i})) nsR.1
  have h_interior : interiorA.1=interiorR.1 ∧ interiorA.2≤ interiorR.2 := by
    change (Allocation.flatMapQ (fun z => Allocation.loopQ (m-1) (fun i =>
    Allocation.singletonQ {owner:=q,part:=2,p:=z,i:=i})) nsA.1).1=(flatMapQ (fun z => loopQ (m-1) (fun i =>
    singletonQ {owner:=q,part:=2,p:=z,i:=i})) nsR.1).1 ∧ (Allocation.flatMapQ (fun z => Allocation.loopQ (m-1) (fun i =>
    Allocation.singletonQ {owner:=q,part:=2,p:=z,i:=i})) nsA.1).2≤(flatMapQ (fun z => loopQ (m-1) (fun i =>
    singletonQ {owner:=q,part:=2,p:=z,i:=i})) nsR.1).2
    rw [h_ns.1]
    apply native_flat_simulation
    intro z
    apply native_loop_simulation
    intro i
    exact ⟨allocation_singletonQ_value {owner:=q,part:=2,p:=z,i:=i}, allocation_singletonQ_le {owner:=q,part:=2,p:=z,i:=i}⟩
  let cellsA := Allocation.collectQ [Allocation.singletonQ {owner:=q},endpointA,interiorA]
  let cellsR := collectQ [singletonQ {owner:=q},endpointR,interiorR]
  have h_cells : cellsA.1=cellsR.1 ∧ cellsA.2≤cellsR.2 := by
    change (Allocation.collectQ [Allocation.singletonQ {owner:=q},endpointA,interiorA]).1=(collectQ [singletonQ {owner:=q},endpointR,interiorR]).1 ∧ (Allocation.collectQ [Allocation.singletonQ {owner:=q},endpointA,interiorA]).2≤(collectQ [singletonQ {owner:=q},endpointR,interiorR]).2
    have hi0 : (Allocation.singletonQ {owner:=q}).1=(singletonQ {owner:=q}).1 ∧ (Allocation.singletonQ {owner:=q}).2≤(singletonQ {owner:=q}).2 := by
      exact ⟨allocation_singletonQ_value {owner:=q}, allocation_singletonQ_le {owner:=q}⟩
    have hi1 : (endpointA).1=(endpointR).1 ∧ (endpointA).2≤(endpointR).2 := by
      exact h_endpoint
    have hi2 : (interiorA).1=(interiorR).1 ∧ (interiorA).2≤(interiorR).2 := by
      exact h_interior
    apply native_collect_simulation
    · change [(Allocation.singletonQ {owner:=q}).1, (endpointA).1, (interiorA).1]=[(singletonQ {owner:=q}).1, (endpointR).1, (interiorR).1]
      exact congrArg₂ List.cons hi0.1 (congrArg₂ List.cons hi1.1 (congrArg₂ List.cons hi2.1 (rfl)))
    · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      have hc0 := hi0.2
      have hc1 := hi1.2
      have hc2 := hi2.2
      omega
  let outA := Allocation.flatMapQ (fun c => Allocation.mapCodesQ (fun v => {v with copy:=c}) cellsA.1) [0,1]
  let outR := flatMapQ (fun c => mapCodesQ (fun v => {v with copy:=c}) cellsR.1) [0,1]
  have h_out : outA.1=outR.1 ∧ outA.2≤outR.2 := by
    change (Allocation.flatMapQ (fun c => Allocation.mapCodesQ (fun v => {v with copy:=c}) cellsA.1) [0,1]).1=(flatMapQ (fun c => mapCodesQ (fun v => {v with copy:=c}) cellsR.1) [0,1]).1 ∧ (Allocation.flatMapQ (fun c => Allocation.mapCodesQ (fun v => {v with copy:=c}) cellsA.1) [0,1]).2≤(flatMapQ (fun c => mapCodesQ (fun v => {v with copy:=c}) cellsR.1) [0,1]).2
    rw [h_cells.1]
    apply native_flat_simulation
    intro c
    exact ⟨allocation_mapCodesQ_value (fun v => {v with copy:=c}) cellsR.1, allocation_mapCodesQ_le (fun v => {v with copy:=c}) cellsR.1⟩
  constructor
  · change outA.1=outR.1
    simpa only [h_out.1]
  · change nsA.2+cellsA.2+outA.2≤nsR.2+cellsR.2+outR.2
    have hc0 := h_ns.2
    have hc1 := h_cells.2
    have hc2 := h_out.2
    omega
theorem allocation_qDoubleVerticesQ_value (F : Frame) (q m : ℕ) :
    (Allocation.qDoubleVerticesQ F q m).1=(qDoubleVerticesQ F q m).1 := by
  exact (native_qDoubleVerticesQ_simulation F q m).1
attribute [local simp] allocation_qDoubleVerticesQ_value
theorem allocation_qDoubleVerticesQ_le (F : Frame) (q m : ℕ) :
    (Allocation.qDoubleVerticesQ F q m).2≤(qDoubleVerticesQ F q m).2 := by
  exact (native_qDoubleVerticesQ_simulation F q m).2
theorem native_qDoubleEdgesQ_simulation (F : Frame) (q m : ℕ) :
    (Allocation.qDoubleEdgesQ F q m).1=(qDoubleEdgesQ F q m).1 ∧ (Allocation.qDoubleEdgesQ F q m).2≤(qDoubleEdgesQ F q m).2 := by
  unfold Allocation.qDoubleEdgesQ qDoubleEdgesQ
  let nsA := Allocation.qNeighborsQ F q
  let nsR := qNeighborsQ F q
  have h_ns : nsA.1=nsR.1 ∧ nsA.2≤nsR.2 := by
    change (Allocation.qNeighborsQ F q).1=(qNeighborsQ F q).1 ∧ (Allocation.qNeighborsQ F q).2≤(qNeighborsQ F q).2
    exact ⟨allocation_qNeighborsQ_value F q, allocation_qNeighborsQ_le F q⟩
  let endsA := Allocation.flatMapQ (fun c => Allocation.flatMapQ (fun z => Allocation.loopQ m (fun i =>
    Allocation.singletonQ {owner:=q,copy:=c,p:=z,i:=i})) nsA.1) [0,1]
  let endsR := flatMapQ (fun c => flatMapQ (fun z => loopQ m (fun i =>
    singletonQ {owner:=q,copy:=c,p:=z,i:=i})) nsR.1) [0,1]
  have h_ends : endsA.1=endsR.1 ∧ endsA.2≤endsR.2 := by
    change (Allocation.flatMapQ (fun c => Allocation.flatMapQ (fun z => Allocation.loopQ m (fun i =>
    Allocation.singletonQ {owner:=q,copy:=c,p:=z,i:=i})) nsA.1) [0,1]).1=(flatMapQ (fun c => flatMapQ (fun z => loopQ m (fun i =>
    singletonQ {owner:=q,copy:=c,p:=z,i:=i})) nsR.1) [0,1]).1 ∧ (Allocation.flatMapQ (fun c => Allocation.flatMapQ (fun z => Allocation.loopQ m (fun i =>
    Allocation.singletonQ {owner:=q,copy:=c,p:=z,i:=i})) nsA.1) [0,1]).2≤(flatMapQ (fun c => flatMapQ (fun z => loopQ m (fun i =>
    singletonQ {owner:=q,copy:=c,p:=z,i:=i})) nsR.1) [0,1]).2
    rw [h_ns.1]
    apply native_flat_simulation
    intro c
    apply native_flat_simulation
    intro z
    apply native_loop_simulation
    intro i
    exact ⟨allocation_singletonQ_value {owner:=q,copy:=c,p:=z,i:=i}, allocation_singletonQ_le {owner:=q,copy:=c,p:=z,i:=i}⟩
  let verticalA := Allocation.mapQ (fun z => Allocation.emitQ {owner:=q,part:=1,p:=z}) nsA.1
  let verticalR := mapQ (fun z => emitQ {owner:=q,part:=1,p:=z}) nsR.1
  have h_vertical : verticalA.1=verticalR.1 ∧ verticalA.2≤verticalR.2 := by
    change (Allocation.mapQ (fun z => Allocation.emitQ {owner:=q,part:=1,p:=z}) nsA.1).1=(mapQ (fun z => emitQ {owner:=q,part:=1,p:=z}) nsR.1).1 ∧ (Allocation.mapQ (fun z => Allocation.emitQ {owner:=q,part:=1,p:=z}) nsA.1).2≤(mapQ (fun z => emitQ {owner:=q,part:=1,p:=z}) nsR.1).2
    rw [h_ns.1]
    apply native_map_simulation
    intro z
    exact ⟨allocation_emitQ_value {owner:=q,part:=1,p:=z}, allocation_emitQ_le {owner:=q,part:=1,p:=z}⟩
  let outA := Allocation.collectQ [endsA,verticalA]
  let outR := collectQ [endsR,verticalR]
  have h_out : outA.1=outR.1 ∧ outA.2≤outR.2 := by
    change (Allocation.collectQ [endsA,verticalA]).1=(collectQ [endsR,verticalR]).1 ∧ (Allocation.collectQ [endsA,verticalA]).2≤(collectQ [endsR,verticalR]).2
    have hi0 : (endsA).1=(endsR).1 ∧ (endsA).2≤(endsR).2 := by
      exact h_ends
    have hi1 : (verticalA).1=(verticalR).1 ∧ (verticalA).2≤(verticalR).2 := by
      exact h_vertical
    apply native_collect_simulation
    · change [(endsA).1, (verticalA).1]=[(endsR).1, (verticalR).1]
      exact congrArg₂ List.cons hi0.1 (congrArg₂ List.cons hi1.1 (rfl))
    · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      have hc0 := hi0.2
      have hc1 := hi1.2
      omega
  constructor
  · change outA.1=outR.1
    simpa only [h_out.1]
  · change nsA.2+outA.2≤nsR.2+outR.2
    have hc0 := h_ns.2
    have hc1 := h_out.2
    omega
theorem allocation_qDoubleEdgesQ_value (F : Frame) (q m : ℕ) :
    (Allocation.qDoubleEdgesQ F q m).1=(qDoubleEdgesQ F q m).1 := by
  exact (native_qDoubleEdgesQ_simulation F q m).1
attribute [local simp] allocation_qDoubleEdgesQ_value
theorem allocation_qDoubleEdgesQ_le (F : Frame) (q m : ℕ) :
    (Allocation.qDoubleEdgesQ F q m).2≤(qDoubleEdgesQ F q m).2 := by
  exact (native_qDoubleEdgesQ_simulation F q m).2
theorem native_rxXCodesQ_simulation (F : Frame) (m : ℕ) :
    (Allocation.rxXCodesQ F m).1=(rxXCodesQ F m).1 ∧ (Allocation.rxXCodesQ F m).2≤(rxXCodesQ F m).2 := by
  unfold Allocation.rxXCodesQ rxXCodesQ
  apply native_loop_simulation
  intro x
  exact ⟨allocation_doubleVerticesQ_value F x m, allocation_doubleVerticesQ_le F x m⟩
theorem allocation_rxXCodesQ_value (F : Frame) (m : ℕ) :
    (Allocation.rxXCodesQ F m).1=(rxXCodesQ F m).1 := by
  exact (native_rxXCodesQ_simulation F m).1
attribute [local simp] allocation_rxXCodesQ_value
theorem allocation_rxXCodesQ_le (F : Frame) (m : ℕ) :
    (Allocation.rxXCodesQ F m).2≤(rxXCodesQ F m).2 := by
  exact (native_rxXCodesQ_simulation F m).2
theorem native_rxQCodesQ_simulation (F : Frame) (m : ℕ) :
    (Allocation.rxQCodesQ F m).1=(rxQCodesQ F m).1 ∧ (Allocation.rxQCodesQ F m).2≤(rxQCodesQ F m).2 := by
  unfold Allocation.rxQCodesQ rxQCodesQ
  let localPartA := Allocation.loopQ F.nx (fun x => Allocation.doubleEdgesQ F x m)
  let localPartR := loopQ F.nx (fun x => doubleEdgesQ F x m)
  have h_localPart : localPartA.1=localPartR.1 ∧ localPartA.2≤localPartR.2 := by
    change (Allocation.loopQ F.nx (fun x => Allocation.doubleEdgesQ F x m)).1=(loopQ F.nx (fun x => doubleEdgesQ F x m)).1 ∧ (Allocation.loopQ F.nx (fun x => Allocation.doubleEdgesQ F x m)).2≤(loopQ F.nx (fun x => doubleEdgesQ F x m)).2
    apply native_loop_simulation
    intro x
    exact ⟨allocation_doubleEdgesQ_value F x m, allocation_doubleEdgesQ_le F x m⟩
  let qlocalA := Allocation.loopQ F.nq (fun q =>
    let cells := Allocation.qDoubleVerticesQ F q m
    let out := Allocation.mapCodesQ (fun c => {c with family:=1}) cells.1
    (out.1,cells.2+out.2))
  let qlocalR := loopQ F.nq (fun q =>
    let cells := qDoubleVerticesQ F q m
    let out := mapCodesQ (fun c => {c with family:=1}) cells.1
    (out.1,cells.2+out.2))
  have h_qlocal : qlocalA.1=qlocalR.1 ∧ qlocalA.2≤qlocalR.2 := by
    change (Allocation.loopQ F.nq (fun q =>
    let cells := Allocation.qDoubleVerticesQ F q m
    let out := Allocation.mapCodesQ (fun c => {c with family:=1}) cells.1
    (out.1,cells.2+out.2))).1=(loopQ F.nq (fun q =>
    let cells := qDoubleVerticesQ F q m
    let out := mapCodesQ (fun c => {c with family:=1}) cells.1
    (out.1,cells.2+out.2))).1 ∧ (Allocation.loopQ F.nq (fun q =>
    let cells := Allocation.qDoubleVerticesQ F q m
    let out := Allocation.mapCodesQ (fun c => {c with family:=1}) cells.1
    (out.1,cells.2+out.2))).2≤(loopQ F.nq (fun q =>
    let cells := qDoubleVerticesQ F q m
    let out := mapCodesQ (fun c => {c with family:=1}) cells.1
    (out.1,cells.2+out.2))).2
    apply native_loop_simulation
    intro q
    let cellsA := Allocation.qDoubleVerticesQ F q m
    let cellsR := qDoubleVerticesQ F q m
    have h_cells : cellsA.1=cellsR.1 ∧ cellsA.2≤cellsR.2 := by
      change (Allocation.qDoubleVerticesQ F q m).1=(qDoubleVerticesQ F q m).1 ∧ (Allocation.qDoubleVerticesQ F q m).2≤(qDoubleVerticesQ F q m).2
      exact ⟨allocation_qDoubleVerticesQ_value F q m, allocation_qDoubleVerticesQ_le F q m⟩
    let outA := Allocation.mapCodesQ (fun c => {c with family:=1}) cellsA.1
    let outR := mapCodesQ (fun c => {c with family:=1}) cellsR.1
    have h_out : outA.1=outR.1 ∧ outA.2≤outR.2 := by
      change (Allocation.mapCodesQ (fun c => {c with family:=1}) cellsA.1).1=(mapCodesQ (fun c => {c with family:=1}) cellsR.1).1 ∧ (Allocation.mapCodesQ (fun c => {c with family:=1}) cellsA.1).2≤(mapCodesQ (fun c => {c with family:=1}) cellsR.1).2
      rw [h_cells.1]
      exact ⟨allocation_mapCodesQ_value (fun c => {c with family:=1}) cellsR.1, allocation_mapCodesQ_le (fun c => {c with family:=1}) cellsR.1⟩
    constructor
    · change outA.1=outR.1
      simpa only [h_out.1]
    · change cellsA.2+outA.2≤cellsR.2+outR.2
      have hc0 := h_cells.2
      have hc1 := h_out.2
      omega
  change (Allocation.collectQ [localPartA,qlocalA]).1=(collectQ [localPartR,qlocalR]).1 ∧ (Allocation.collectQ [localPartA,qlocalA]).2≤(collectQ [localPartR,qlocalR]).2
  have hi0 : (localPartA).1=(localPartR).1 ∧ (localPartA).2≤(localPartR).2 := by
    exact h_localPart
  have hi1 : (qlocalA).1=(qlocalR).1 ∧ (qlocalA).2≤(qlocalR).2 := by
    exact h_qlocal
  apply native_collect_simulation
  · change [(localPartA).1, (qlocalA).1]=[(localPartR).1, (qlocalR).1]
    exact congrArg₂ List.cons hi0.1 (congrArg₂ List.cons hi1.1 (rfl))
  · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    have hc0 := hi0.2
    have hc1 := hi1.2
    omega
theorem allocation_rxQCodesQ_value (F : Frame) (m : ℕ) :
    (Allocation.rxQCodesQ F m).1=(rxQCodesQ F m).1 := by
  exact (native_rxQCodesQ_simulation F m).1
attribute [local simp] allocation_rxQCodesQ_value
theorem allocation_rxQCodesQ_le (F : Frame) (m : ℕ) :
    (Allocation.rxQCodesQ F m).2≤(rxQCodesQ F m).2 := by
  exact (native_rxQCodesQ_simulation F m).2
theorem native_rxZCodesQ_simulation (F : Frame) (m : ℕ) :
    (Allocation.rxZCodesQ F m).1=(rxZCodesQ F m).1 ∧ (Allocation.rxZCodesQ F m).2≤(rxZCodesQ F m).2 := by
  unfold Allocation.rxZCodesQ rxZCodesQ
  let localPartA := Allocation.loopQ F.nx (fun x => Allocation.doubleFacesQ F x m)
  let localPartR := loopQ F.nx (fun x => doubleFacesQ F x m)
  have h_localPart : localPartA.1=localPartR.1 ∧ localPartA.2≤localPartR.2 := by
    change (Allocation.loopQ F.nx (fun x => Allocation.doubleFacesQ F x m)).1=(loopQ F.nx (fun x => doubleFacesQ F x m)).1 ∧ (Allocation.loopQ F.nx (fun x => Allocation.doubleFacesQ F x m)).2≤(loopQ F.nx (fun x => doubleFacesQ F x m)).2
    apply native_loop_simulation
    intro x
    exact ⟨allocation_doubleFacesQ_value F x m, allocation_doubleFacesQ_le F x m⟩
  let qlocalA := Allocation.loopQ F.nq (fun q =>
    let cells := Allocation.qDoubleEdgesQ F q m
    let out := Allocation.mapCodesQ (fun c => {c with family:=1}) cells.1
    (out.1,cells.2+out.2))
  let qlocalR := loopQ F.nq (fun q =>
    let cells := qDoubleEdgesQ F q m
    let out := mapCodesQ (fun c => {c with family:=1}) cells.1
    (out.1,cells.2+out.2))
  have h_qlocal : qlocalA.1=qlocalR.1 ∧ qlocalA.2≤qlocalR.2 := by
    change (Allocation.loopQ F.nq (fun q =>
    let cells := Allocation.qDoubleEdgesQ F q m
    let out := Allocation.mapCodesQ (fun c => {c with family:=1}) cells.1
    (out.1,cells.2+out.2))).1=(loopQ F.nq (fun q =>
    let cells := qDoubleEdgesQ F q m
    let out := mapCodesQ (fun c => {c with family:=1}) cells.1
    (out.1,cells.2+out.2))).1 ∧ (Allocation.loopQ F.nq (fun q =>
    let cells := Allocation.qDoubleEdgesQ F q m
    let out := Allocation.mapCodesQ (fun c => {c with family:=1}) cells.1
    (out.1,cells.2+out.2))).2≤(loopQ F.nq (fun q =>
    let cells := qDoubleEdgesQ F q m
    let out := mapCodesQ (fun c => {c with family:=1}) cells.1
    (out.1,cells.2+out.2))).2
    apply native_loop_simulation
    intro q
    let cellsA := Allocation.qDoubleEdgesQ F q m
    let cellsR := qDoubleEdgesQ F q m
    have h_cells : cellsA.1=cellsR.1 ∧ cellsA.2≤cellsR.2 := by
      change (Allocation.qDoubleEdgesQ F q m).1=(qDoubleEdgesQ F q m).1 ∧ (Allocation.qDoubleEdgesQ F q m).2≤(qDoubleEdgesQ F q m).2
      exact ⟨allocation_qDoubleEdgesQ_value F q m, allocation_qDoubleEdgesQ_le F q m⟩
    let outA := Allocation.mapCodesQ (fun c => {c with family:=1}) cellsA.1
    let outR := mapCodesQ (fun c => {c with family:=1}) cellsR.1
    have h_out : outA.1=outR.1 ∧ outA.2≤outR.2 := by
      change (Allocation.mapCodesQ (fun c => {c with family:=1}) cellsA.1).1=(mapCodesQ (fun c => {c with family:=1}) cellsR.1).1 ∧ (Allocation.mapCodesQ (fun c => {c with family:=1}) cellsA.1).2≤(mapCodesQ (fun c => {c with family:=1}) cellsR.1).2
      rw [h_cells.1]
      exact ⟨allocation_mapCodesQ_value (fun c => {c with family:=1}) cellsR.1, allocation_mapCodesQ_le (fun c => {c with family:=1}) cellsR.1⟩
    constructor
    · change outA.1=outR.1
      simpa only [h_out.1]
    · change cellsA.2+outA.2≤cellsR.2+outR.2
      have hc0 := h_cells.2
      have hc1 := h_out.2
      omega
  let oldA := Allocation.loopQ F.nz (fun z => Allocation.mapQ (fun c => Allocation.emitQ {family:=2,owner:=z,copy:=c}) [0,1])
  let oldR := loopQ F.nz (fun z => mapQ (fun c => emitQ {family:=2,owner:=z,copy:=c}) [0,1])
  have h_old : oldA.1=oldR.1 ∧ oldA.2≤oldR.2 := by
    change (Allocation.loopQ F.nz (fun z => Allocation.mapQ (fun c => Allocation.emitQ {family:=2,owner:=z,copy:=c}) [0,1])).1=(loopQ F.nz (fun z => mapQ (fun c => emitQ {family:=2,owner:=z,copy:=c}) [0,1])).1 ∧ (Allocation.loopQ F.nz (fun z => Allocation.mapQ (fun c => Allocation.emitQ {family:=2,owner:=z,copy:=c}) [0,1])).2≤(loopQ F.nz (fun z => mapQ (fun c => emitQ {family:=2,owner:=z,copy:=c}) [0,1])).2
    apply native_loop_simulation
    intro z
    apply native_map_simulation
    intro c
    exact ⟨allocation_emitQ_value {family:=2,owner:=z,copy:=c}, allocation_emitQ_le {family:=2,owner:=z,copy:=c}⟩
  change (Allocation.collectQ [localPartA,qlocalA,oldA]).1=(collectQ [localPartR,qlocalR,oldR]).1 ∧ (Allocation.collectQ [localPartA,qlocalA,oldA]).2≤(collectQ [localPartR,qlocalR,oldR]).2
  have hi0 : (localPartA).1=(localPartR).1 ∧ (localPartA).2≤(localPartR).2 := by
    exact h_localPart
  have hi1 : (qlocalA).1=(qlocalR).1 ∧ (qlocalA).2≤(qlocalR).2 := by
    exact h_qlocal
  have hi2 : (oldA).1=(oldR).1 ∧ (oldA).2≤(oldR).2 := by
    exact h_old
  apply native_collect_simulation
  · change [(localPartA).1, (qlocalA).1, (oldA).1]=[(localPartR).1, (qlocalR).1, (oldR).1]
    exact congrArg₂ List.cons hi0.1 (congrArg₂ List.cons hi1.1 (congrArg₂ List.cons hi2.1 (rfl)))
  · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    have hc0 := hi0.2
    have hc1 := hi1.2
    have hc2 := hi2.2
    omega
theorem allocation_rxZCodesQ_value (F : Frame) (m : ℕ) :
    (Allocation.rxZCodesQ F m).1=(rxZCodesQ F m).1 := by
  exact (native_rxZCodesQ_simulation F m).1
attribute [local simp] allocation_rxZCodesQ_value
theorem allocation_rxZCodesQ_le (F : Frame) (m : ℕ) :
    (Allocation.rxZCodesQ F m).2≤(rxZCodesQ F m).2 := by
  exact (native_rxZCodesQ_simulation F m).2
theorem allocation_gridVertexQ_value (F : Frame) (x m f i j : ℕ) :
    (Allocation.gridVertexQ F x m f i j).1=(gridVertexQ F x m f i j).1 := by
  simp only [Allocation.gridVertexQ, gridVertexQ, allocation_faceAt_value]
attribute [local simp] allocation_gridVertexQ_value
theorem allocation_gridVertexQ_le (F : Frame) (x m f i j : ℕ) :
    (Allocation.gridVertexQ F x m f i j).2≤(gridVertexQ F x m f i j).2 := by
  have h := allocation_faceAt_le F.faces f
  change (Allocation.faceAtQ F.faces f).2+1 ≤ (faceAtQ F.faces f).2+64
  omega
theorem allocation_horizontalEdgeQ_value (F : Frame) (x m f i j : ℕ) :
    (Allocation.horizontalEdgeQ F x m f i j).1=(horizontalEdgeQ F x m f i j).1 := by
  simp only [Allocation.horizontalEdgeQ, horizontalEdgeQ, allocation_faceAt_value]
attribute [local simp] allocation_horizontalEdgeQ_value
theorem allocation_horizontalEdgeQ_le (F : Frame) (x m f i j : ℕ) :
    (Allocation.horizontalEdgeQ F x m f i j).2≤(horizontalEdgeQ F x m f i j).2 := by
  have h := allocation_faceAt_le F.faces f
  change (Allocation.faceAtQ F.faces f).2+1 ≤ (faceAtQ F.faces f).2+48
  omega
theorem allocation_verticalEdgeQ_value (F : Frame) (x m f i j : ℕ) :
    (Allocation.verticalEdgeQ F x m f i j).1=(verticalEdgeQ F x m f i j).1 := by
  simp only [Allocation.verticalEdgeQ, verticalEdgeQ, allocation_faceAt_value]
attribute [local simp] allocation_verticalEdgeQ_value
theorem allocation_verticalEdgeQ_le (F : Frame) (x m f i j : ℕ) :
    (Allocation.verticalEdgeQ F x m f i j).2≤(verticalEdgeQ F x m f i j).2 := by
  have h := allocation_faceAt_le F.faces f
  change (Allocation.faceAtQ F.faces f).2+1 ≤ (faceAtQ F.faces f).2+48
  omega
theorem allocation_segmentVertexQ_value (x m : ℕ) (e : Code) (endpoint : ℕ) :
    (Allocation.segmentVertexQ x m e endpoint).1=(segmentVertexQ x m e endpoint).1 := by
  simp only [Allocation.segmentVertexQ, segmentVertexQ]
attribute [local simp] allocation_segmentVertexQ_value
theorem allocation_segmentVertexQ_le (x m : ℕ) (e : Code) (endpoint : ℕ) :
    (Allocation.segmentVertexQ x m e endpoint).2≤(segmentVertexQ x m e endpoint).2 := by
  change 1 ≤ 64
  decide
theorem allocation_doubleEdgeVertexQ_value (F : Frame) (m : ℕ) (e : Code) (endpoint : ℕ) :
    (Allocation.doubleEdgeVertexQ F m e endpoint).1=(doubleEdgeVertexQ F m e endpoint).1 := by
  by_cases hb : e.part≥4
  · simp only [Allocation.doubleEdgeVertexQ,doubleEdgeVertexQ,if_pos hb]
  · by_cases hs : e.part=0 ∨ e.part=1
    · simp only [Allocation.doubleEdgeVertexQ,doubleEdgeVertexQ,if_neg hb,if_pos hs,
        allocation_segmentVertexQ_value]
    · by_cases he : e.part=2
      · simp only [Allocation.doubleEdgeVertexQ,doubleEdgeVertexQ,if_neg hb,if_neg hs,
          if_pos he,allocation_gridVertexQ_value]
      · simp only [Allocation.doubleEdgeVertexQ,doubleEdgeVertexQ,if_neg hb,if_neg hs,
          if_neg he,allocation_gridVertexQ_value]
attribute [local simp] allocation_doubleEdgeVertexQ_value
theorem allocation_doubleEdgeVertexQ_le (F : Frame) (m : ℕ) (e : Code) (endpoint : ℕ) :
    (Allocation.doubleEdgeVertexQ F m e endpoint).2≤(doubleEdgeVertexQ F m e endpoint).2 := by
  by_cases hb : e.part≥4
  · simp only [Allocation.doubleEdgeVertexQ,doubleEdgeVertexQ,if_pos hb]
    change 1≤64
    decide
  · by_cases hs : e.part=0 ∨ e.part=1
    · simp only [Allocation.doubleEdgeVertexQ,doubleEdgeVertexQ,if_neg hb,if_pos hs]
      change (Allocation.segmentVertexQ e.owner m e endpoint).2+1 ≤
        (segmentVertexQ e.owner m e endpoint).2+40
      have h := allocation_segmentVertexQ_le e.owner m e endpoint
      omega
    · by_cases he : e.part=2
      · simp only [Allocation.doubleEdgeVertexQ,doubleEdgeVertexQ,if_neg hb,if_neg hs,if_pos he]
        have h := allocation_gridVertexQ_le F e.owner m e.p (e.i+endpoint) (e.j+1)
        change (Allocation.gridVertexQ F e.owner m e.p (e.i+endpoint) (e.j+1)).2+1 ≤
          (gridVertexQ F e.owner m e.p (e.i+endpoint) (e.j+1)).2+40
        omega
      · simp only [Allocation.doubleEdgeVertexQ,doubleEdgeVertexQ,if_neg hb,if_neg hs,if_neg he]
        have h := allocation_gridVertexQ_le F e.owner m e.p (e.i+1) (e.j+endpoint)
        change (Allocation.gridVertexQ F e.owner m e.p (e.i+1) (e.j+endpoint)).2+1 ≤
          (gridVertexQ F e.owner m e.p (e.i+1) (e.j+endpoint)).2+40
        omega
theorem allocation_qDoubleEdgeVertexQ_value (m : ℕ) (e : Code) (endpoint : ℕ) :
    (Allocation.qDoubleEdgeVertexQ m e endpoint).1=(qDoubleEdgeVertexQ m e endpoint).1 := by
  by_cases h0 : e.part=1 <;>
  simp only [Allocation.qDoubleEdgeVertexQ, qDoubleEdgeVertexQ, h0, ite_true, ite_false]
attribute [local simp] allocation_qDoubleEdgeVertexQ_value
theorem allocation_qDoubleEdgeVertexQ_le (m : ℕ) (e : Code) (endpoint : ℕ) :
    (Allocation.qDoubleEdgeVertexQ m e endpoint).2≤(qDoubleEdgeVertexQ m e endpoint).2 := by
  by_cases h : e.part=1
  · simp only [Allocation.qDoubleEdgeVertexQ,qDoubleEdgeVertexQ,if_pos h]
    change 1≤48
    decide
  · simp only [Allocation.qDoubleEdgeVertexQ,qDoubleEdgeVertexQ,if_neg h]
    change 1≤64
    decide
theorem allocation_qEdgeImageQ_value (x : ℕ) (e : Code) :
    (Allocation.qEdgeImageQ x e).1=(qEdgeImageQ x e).1 := by
  simp only [Allocation.qEdgeImageQ, qEdgeImageQ]
attribute [local simp] allocation_qEdgeImageQ_value
theorem allocation_qEdgeImageQ_le (x : ℕ) (e : Code) :
    (Allocation.qEdgeImageQ x e).2≤(qEdgeImageQ x e).2 := by
  change 1 ≤ 48
  decide
theorem allocation_bridgeOfVertexQ_value (v : Code) :
    (Allocation.bridgeOfVertexQ v).1=(bridgeOfVertexQ v).1 := by
  simp only [Allocation.bridgeOfVertexQ, bridgeOfVertexQ]
attribute [local simp] allocation_bridgeOfVertexQ_value
theorem allocation_bridgeOfVertexQ_le (v : Code) :
    (Allocation.bridgeOfVertexQ v).2≤(bridgeOfVertexQ v).2 := by
  change 1 ≤ 48
  decide
theorem native_rxLocalFaceCodesQ_simulation (F : Frame) (m : ℕ) :
    (Allocation.rxLocalFaceCodesQ F m).1=(rxLocalFaceCodesQ F m).1 ∧ (Allocation.rxLocalFaceCodesQ F m).2≤(rxLocalFaceCodesQ F m).2 := by
  unfold Allocation.rxLocalFaceCodesQ rxLocalFaceCodesQ
  apply native_loop_simulation
  intro x
  let fsA := Allocation.doubleFacesQ F x m
  let fsR := doubleFacesQ F x m
  have h_fs : fsA.1=fsR.1 ∧ fsA.2≤fsR.2 := by
    change (Allocation.doubleFacesQ F x m).1=(doubleFacesQ F x m).1 ∧ (Allocation.doubleFacesQ F x m).2≤(doubleFacesQ F x m).2
    exact ⟨allocation_doubleFacesQ_value F x m, allocation_doubleFacesQ_le F x m⟩
  let outA := Allocation.flatMapQ (fun f => Allocation.flatMapQ (fun a =>
      Allocation.mapQ (fun b => Allocation.emitQ {f with k:=a,l:=b}) [0,1]) [0,1]) fsA.1
  let outR := flatMapQ (fun f => flatMapQ (fun a =>
      mapQ (fun b => emitQ {f with k:=a,l:=b}) [0,1]) [0,1]) fsR.1
  have h_out : outA.1=outR.1 ∧ outA.2≤outR.2 := by
    change (Allocation.flatMapQ (fun f => Allocation.flatMapQ (fun a =>
      Allocation.mapQ (fun b => Allocation.emitQ {f with k:=a,l:=b}) [0,1]) [0,1]) fsA.1).1=(flatMapQ (fun f => flatMapQ (fun a =>
      mapQ (fun b => emitQ {f with k:=a,l:=b}) [0,1]) [0,1]) fsR.1).1 ∧ (Allocation.flatMapQ (fun f => Allocation.flatMapQ (fun a =>
      Allocation.mapQ (fun b => Allocation.emitQ {f with k:=a,l:=b}) [0,1]) [0,1]) fsA.1).2≤(flatMapQ (fun f => flatMapQ (fun a =>
      mapQ (fun b => emitQ {f with k:=a,l:=b}) [0,1]) [0,1]) fsR.1).2
    rw [h_fs.1]
    apply native_flat_simulation
    intro f
    apply native_flat_simulation
    intro a
    apply native_map_simulation
    intro b
    exact ⟨allocation_emitQ_value {f with k:=a,l:=b}, allocation_emitQ_le {f with k:=a,l:=b}⟩
  constructor
  · change outA.1=outR.1
    simpa only [h_out.1]
  · change fsA.2+outA.2≤fsR.2+outR.2
    have hc0 := h_fs.2
    have hc1 := h_out.2
    omega
theorem allocation_rxLocalFaceCodesQ_value (F : Frame) (m : ℕ) :
    (Allocation.rxLocalFaceCodesQ F m).1=(rxLocalFaceCodesQ F m).1 := by
  exact (native_rxLocalFaceCodesQ_simulation F m).1
attribute [local simp] allocation_rxLocalFaceCodesQ_value
theorem allocation_rxLocalFaceCodesQ_le (F : Frame) (m : ℕ) :
    (Allocation.rxLocalFaceCodesQ F m).2≤(rxLocalFaceCodesQ F m).2 := by
  exact (native_rxLocalFaceCodesQ_simulation F m).2
theorem native_rxGlueFaceCodesQ_simulation (F : Frame) (m : ℕ) :
    (Allocation.rxGlueFaceCodesQ F m).1=(rxGlueFaceCodesQ F m).1 ∧ (Allocation.rxGlueFaceCodesQ F m).2≤(rxGlueFaceCodesQ F m).2 := by
  unfold Allocation.rxGlueFaceCodesQ rxGlueFaceCodesQ
  apply native_loop_simulation
  intro x
  let qsA := Allocation.starQsQ F x
  let qsR := starQsQ F x
  have h_qs : qsA.1=qsR.1 ∧ qsA.2≤qsR.2 := by
    change (Allocation.starQsQ F x).1=(starQsQ F x).1 ∧ (Allocation.starQsQ F x).2≤(starQsQ F x).2
    exact ⟨allocation_starQsQ_value F x, allocation_starQsQ_le F x⟩
  let outA := Allocation.flatMapQ (fun q =>
      let es := Allocation.qDoubleEdgesQ F q m
      let out := Allocation.flatMapQ (fun e => Allocation.mapQ (fun a =>
        Allocation.emitQ {family:=1,owner:=x,copy:=e.copy,part:=e.part,p:=q,q:=e.p,i:=e.i,k:=a}) [0,1]) es.1
      (out.1,es.2+out.2)) qsA.1
  let outR := flatMapQ (fun q =>
      let es := qDoubleEdgesQ F q m
      let out := flatMapQ (fun e => mapQ (fun a =>
        emitQ {family:=1,owner:=x,copy:=e.copy,part:=e.part,p:=q,q:=e.p,i:=e.i,k:=a}) [0,1]) es.1
      (out.1,es.2+out.2)) qsR.1
  have h_out : outA.1=outR.1 ∧ outA.2≤outR.2 := by
    change (Allocation.flatMapQ (fun q =>
      let es := Allocation.qDoubleEdgesQ F q m
      let out := Allocation.flatMapQ (fun e => Allocation.mapQ (fun a =>
        Allocation.emitQ {family:=1,owner:=x,copy:=e.copy,part:=e.part,p:=q,q:=e.p,i:=e.i,k:=a}) [0,1]) es.1
      (out.1,es.2+out.2)) qsA.1).1=(flatMapQ (fun q =>
      let es := qDoubleEdgesQ F q m
      let out := flatMapQ (fun e => mapQ (fun a =>
        emitQ {family:=1,owner:=x,copy:=e.copy,part:=e.part,p:=q,q:=e.p,i:=e.i,k:=a}) [0,1]) es.1
      (out.1,es.2+out.2)) qsR.1).1 ∧ (Allocation.flatMapQ (fun q =>
      let es := Allocation.qDoubleEdgesQ F q m
      let out := Allocation.flatMapQ (fun e => Allocation.mapQ (fun a =>
        Allocation.emitQ {family:=1,owner:=x,copy:=e.copy,part:=e.part,p:=q,q:=e.p,i:=e.i,k:=a}) [0,1]) es.1
      (out.1,es.2+out.2)) qsA.1).2≤(flatMapQ (fun q =>
      let es := qDoubleEdgesQ F q m
      let out := flatMapQ (fun e => mapQ (fun a =>
        emitQ {family:=1,owner:=x,copy:=e.copy,part:=e.part,p:=q,q:=e.p,i:=e.i,k:=a}) [0,1]) es.1
      (out.1,es.2+out.2)) qsR.1).2
    rw [h_qs.1]
    apply native_flat_simulation
    intro q
    let esA := Allocation.qDoubleEdgesQ F q m
    let esR := qDoubleEdgesQ F q m
    have h_es : esA.1=esR.1 ∧ esA.2≤esR.2 := by
      change (Allocation.qDoubleEdgesQ F q m).1=(qDoubleEdgesQ F q m).1 ∧ (Allocation.qDoubleEdgesQ F q m).2≤(qDoubleEdgesQ F q m).2
      exact ⟨allocation_qDoubleEdgesQ_value F q m, allocation_qDoubleEdgesQ_le F q m⟩
    let outA := Allocation.flatMapQ (fun e => Allocation.mapQ (fun a =>
        Allocation.emitQ {family:=1,owner:=x,copy:=e.copy,part:=e.part,p:=q,q:=e.p,i:=e.i,k:=a}) [0,1]) esA.1
    let outR := flatMapQ (fun e => mapQ (fun a =>
        emitQ {family:=1,owner:=x,copy:=e.copy,part:=e.part,p:=q,q:=e.p,i:=e.i,k:=a}) [0,1]) esR.1
    have h_out : outA.1=outR.1 ∧ outA.2≤outR.2 := by
      change (Allocation.flatMapQ (fun e => Allocation.mapQ (fun a =>
        Allocation.emitQ {family:=1,owner:=x,copy:=e.copy,part:=e.part,p:=q,q:=e.p,i:=e.i,k:=a}) [0,1]) esA.1).1=(flatMapQ (fun e => mapQ (fun a =>
        emitQ {family:=1,owner:=x,copy:=e.copy,part:=e.part,p:=q,q:=e.p,i:=e.i,k:=a}) [0,1]) esR.1).1 ∧ (Allocation.flatMapQ (fun e => Allocation.mapQ (fun a =>
        Allocation.emitQ {family:=1,owner:=x,copy:=e.copy,part:=e.part,p:=q,q:=e.p,i:=e.i,k:=a}) [0,1]) esA.1).2≤(flatMapQ (fun e => mapQ (fun a =>
        emitQ {family:=1,owner:=x,copy:=e.copy,part:=e.part,p:=q,q:=e.p,i:=e.i,k:=a}) [0,1]) esR.1).2
      rw [h_es.1]
      apply native_flat_simulation
      intro e
      apply native_map_simulation
      intro a
      exact ⟨allocation_emitQ_value {family:=1,owner:=x,copy:=e.copy,part:=e.part,p:=q,q:=e.p,i:=e.i,k:=a}, allocation_emitQ_le {family:=1,owner:=x,copy:=e.copy,part:=e.part,p:=q,q:=e.p,i:=e.i,k:=a}⟩
    constructor
    · change outA.1=outR.1
      simpa only [h_out.1]
    · change esA.2+outA.2≤esR.2+outR.2
      have hc0 := h_es.2
      have hc1 := h_out.2
      omega
  constructor
  · change outA.1=outR.1
    simpa only [h_out.1]
  · change qsA.2+outA.2≤qsR.2+outR.2
    have hc0 := h_qs.2
    have hc1 := h_out.2
    omega
theorem allocation_rxGlueFaceCodesQ_value (F : Frame) (m : ℕ) :
    (Allocation.rxGlueFaceCodesQ F m).1=(rxGlueFaceCodesQ F m).1 := by
  exact (native_rxGlueFaceCodesQ_simulation F m).1
attribute [local simp] allocation_rxGlueFaceCodesQ_value
theorem allocation_rxGlueFaceCodesQ_le (F : Frame) (m : ℕ) :
    (Allocation.rxGlueFaceCodesQ F m).2≤(rxGlueFaceCodesQ F m).2 := by
  exact (native_rxGlueFaceCodesQ_simulation F m).2
theorem native_rxOldFaceCodesQ_simulation (F : Frame) :
    (Allocation.rxOldFaceCodesQ F).1=(rxOldFaceCodesQ F).1 ∧ (Allocation.rxOldFaceCodesQ F).2≤(rxOldFaceCodesQ F).2 := by
  unfold Allocation.rxOldFaceCodesQ rxOldFaceCodesQ
  apply native_loop_simulation
  intro f
  apply native_map_simulation
  intro c
  exact ⟨allocation_emitQ_value {family:=2,owner:=f,copy:=c}, allocation_emitQ_le {family:=2,owner:=f,copy:=c}⟩
theorem allocation_rxOldFaceCodesQ_value (F : Frame) :
    (Allocation.rxOldFaceCodesQ F).1=(rxOldFaceCodesQ F).1 := by
  exact (native_rxOldFaceCodesQ_simulation F).1
attribute [local simp] allocation_rxOldFaceCodesQ_value
theorem allocation_rxOldFaceCodesQ_le (F : Frame) :
    (Allocation.rxOldFaceCodesQ F).2≤(rxOldFaceCodesQ F).2 := by
  exact (native_rxOldFaceCodesQ_simulation F).2
theorem native_rxFaceCodesQ_simulation (F : Frame) (m : ℕ) :
    (Allocation.rxFaceCodesQ F m).1=(rxFaceCodesQ F m).1 ∧ (Allocation.rxFaceCodesQ F m).2≤(rxFaceCodesQ F m).2 := by
  unfold Allocation.rxFaceCodesQ rxFaceCodesQ
  have hi0 : (Allocation.rxLocalFaceCodesQ F m).1=(rxLocalFaceCodesQ F m).1 ∧ (Allocation.rxLocalFaceCodesQ F m).2≤(rxLocalFaceCodesQ F m).2 := by
    exact ⟨allocation_rxLocalFaceCodesQ_value F m, allocation_rxLocalFaceCodesQ_le F m⟩
  have hi1 : (Allocation.rxGlueFaceCodesQ F m).1=(rxGlueFaceCodesQ F m).1 ∧ (Allocation.rxGlueFaceCodesQ F m).2≤(rxGlueFaceCodesQ F m).2 := by
    exact ⟨allocation_rxGlueFaceCodesQ_value F m, allocation_rxGlueFaceCodesQ_le F m⟩
  have hi2 : (Allocation.rxOldFaceCodesQ F).1=(rxOldFaceCodesQ F).1 ∧ (Allocation.rxOldFaceCodesQ F).2≤(rxOldFaceCodesQ F).2 := by
    exact ⟨allocation_rxOldFaceCodesQ_value F, allocation_rxOldFaceCodesQ_le F⟩
  apply native_collect_simulation
  · change [(Allocation.rxLocalFaceCodesQ F m).1, (Allocation.rxGlueFaceCodesQ F m).1, (Allocation.rxOldFaceCodesQ F).1]=[(rxLocalFaceCodesQ F m).1, (rxGlueFaceCodesQ F m).1, (rxOldFaceCodesQ F).1]
    exact congrArg₂ List.cons hi0.1 (congrArg₂ List.cons hi1.1 (congrArg₂ List.cons hi2.1 (rfl)))
  · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    have hc0 := hi0.2
    have hc1 := hi1.2
    have hc2 := hi2.2
    omega
theorem allocation_rxFaceCodesQ_value (F : Frame) (m : ℕ) :
    (Allocation.rxFaceCodesQ F m).1=(rxFaceCodesQ F m).1 := by
  exact (native_rxFaceCodesQ_simulation F m).1
attribute [local simp] allocation_rxFaceCodesQ_value
theorem allocation_rxFaceCodesQ_le (F : Frame) (m : ℕ) :
    (Allocation.rxFaceCodesQ F m).2≤(rxFaceCodesQ F m).2 := by
  exact (native_rxFaceCodesQ_simulation F m).2
theorem allocation_localFaceEndpointsQ_value (F : Frame) (m : ℕ) (f : Code) :
    (Allocation.localFaceEndpointsQ F m f).1=(localFaceEndpointsQ F m f).1 := by
  by_cases h : f.part=0
  · simp only [Allocation.localFaceEndpointsQ,localFaceEndpointsQ,if_pos h,
      allocation_gridVertexQ_value,allocation_horizontalEdgeQ_value,allocation_verticalEdgeQ_value]
  · simp only [Allocation.localFaceEndpointsQ,localFaceEndpointsQ,if_neg h,
      allocation_doubleEdgeVertexQ_value,allocation_bridgeOfVertexQ_value]
attribute [local simp] allocation_localFaceEndpointsQ_value
theorem allocation_localFaceEndpointsQ_le (F : Frame) (m : ℕ) (f : Code) :
    (Allocation.localFaceEndpointsQ F m f).2≤(localFaceEndpointsQ F m f).2 := by
  by_cases h : f.part=0
  · have hx := allocation_gridVertexQ_le F f.owner m f.p (f.i+f.k) (f.j+f.l)
    have h0 := allocation_horizontalEdgeQ_le F f.owner m f.p f.i (f.j+f.l)
    have h1 := allocation_verticalEdgeQ_le F f.owner m f.p (f.i+f.k) f.j
    simp only [Allocation.localFaceEndpointsQ,localFaceEndpointsQ,if_pos h]
    omega
  · let e : Code := {owner:=f.owner,copy:=f.k,part:=1,p:=f.p,q:=f.q,i:=f.i}
    have hx := allocation_doubleEdgeVertexQ_le F m e f.l
    have hb := allocation_bridgeOfVertexQ_le (doubleEdgeVertexQ F m e f.l).1
    simp only [Allocation.localFaceEndpointsQ,localFaceEndpointsQ,if_neg h,
      allocation_doubleEdgeVertexQ_value]
    change (Allocation.doubleEdgeVertexQ F m e f.l).2+
      (Allocation.bridgeOfVertexQ (doubleEdgeVertexQ F m e f.l).1).2+2 ≤
      (doubleEdgeVertexQ F m e f.l).2+(bridgeOfVertexQ (doubleEdgeVertexQ F m e f.l).1).2+72
    omega
theorem allocation_glueFaceEndpointsQ_value (F : Frame) (m : ℕ) (f : Code) :
    (Allocation.glueFaceEndpointsQ F m f).1=(glueFaceEndpointsQ F m f).1 := by
  simp only [Allocation.glueFaceEndpointsQ, glueFaceEndpointsQ, allocation_qEdgeImageQ_value, allocation_doubleEdgeVertexQ_value, allocation_qDoubleEdgeVertexQ_value]
attribute [local simp] allocation_glueFaceEndpointsQ_value
theorem allocation_glueFaceEndpointsQ_le (F : Frame) (m : ℕ) (f : Code) :
    (Allocation.glueFaceEndpointsQ F m f).2≤(glueFaceEndpointsQ F m f).2 := by
  let e : Code := {family:=1,owner:=f.p,copy:=f.copy,part:=f.part,p:=f.q,i:=f.i}
  have hi := allocation_qEdgeImageQ_le f.owner e
  have hx := allocation_doubleEdgeVertexQ_le F m (qEdgeImageQ f.owner e).1 f.k
  have hq := allocation_qDoubleEdgeVertexQ_le m e f.k
  simp only [Allocation.glueFaceEndpointsQ,glueFaceEndpointsQ,allocation_qEdgeImageQ_value]
  change (Allocation.qEdgeImageQ f.owner e).2+
    (Allocation.doubleEdgeVertexQ F m (qEdgeImageQ f.owner e).1 f.k).2+
    (Allocation.qDoubleEdgeVertexQ m e f.k).2+2 ≤
    (qEdgeImageQ f.owner e).2+(doubleEdgeVertexQ F m (qEdgeImageQ f.owner e).1 f.k).2+
    (qDoubleEdgeVertexQ m e f.k).2+72
  omega
theorem allocation_oldFaceEndpointsQ_value (F : Frame) (f : Code) :
    (Allocation.oldFaceEndpointsQ F f).1=(oldFaceEndpointsQ F f).1 := by
  simp only [Allocation.oldFaceEndpointsQ,oldFaceEndpointsQ,allocation_faceAt_value]
attribute [local simp] allocation_oldFaceEndpointsQ_value
theorem allocation_oldFaceEndpointsQ_le (F : Frame) (f : Code) :
    (Allocation.oldFaceEndpointsQ F f).2≤(oldFaceEndpointsQ F f).2 := by
  have h := allocation_faceAt_le F.faces f.owner
  change (Allocation.faceAtQ F.faces f.owner).2+5 ≤ (faceAtQ F.faces f.owner).2+136
  omega
theorem allocation_faceEndpointsQ_value (F : Frame) (m : ℕ) (f : Code) :
    (Allocation.faceEndpointsQ F m f).1=(faceEndpointsQ F m f).1 := by
  by_cases h0 : f.family=0
  · simp only [Allocation.faceEndpointsQ,faceEndpointsQ,if_pos h0,allocation_localFaceEndpointsQ_value]
  · by_cases h1 : f.family=1
    · simp only [Allocation.faceEndpointsQ,faceEndpointsQ,if_neg h0,if_pos h1,allocation_glueFaceEndpointsQ_value]
    · simp only [Allocation.faceEndpointsQ,faceEndpointsQ,if_neg h0,if_neg h1,allocation_oldFaceEndpointsQ_value]
attribute [local simp] allocation_faceEndpointsQ_value
theorem allocation_faceEndpointsQ_le (F : Frame) (m : ℕ) (f : Code) :
    (Allocation.faceEndpointsQ F m f).2≤(faceEndpointsQ F m f).2 := by
  by_cases h0 : f.family=0
  · simp only [Allocation.faceEndpointsQ,faceEndpointsQ,if_pos h0]
    have h := allocation_localFaceEndpointsQ_le F m f
    omega
  · by_cases h1 : f.family=1
    · simp only [Allocation.faceEndpointsQ,faceEndpointsQ,if_neg h0,if_pos h1]
      have h := allocation_glueFaceEndpointsQ_le F m f
      omega
    · simp only [Allocation.faceEndpointsQ,faceEndpointsQ,if_neg h0,if_neg h1]
      have h := allocation_oldFaceEndpointsQ_le F f
      omega
theorem allocation_indexFaceQ_value (xs qs zs : List Code) (code : Code) (f : FaceCodes) :
    (Allocation.indexFaceQ xs qs zs code f).1=(indexFaceQ xs qs zs code f).1 := by
  simp only [Allocation.indexFaceQ,indexFaceQ,allocation_handle_value]
attribute [local simp] allocation_indexFaceQ_value
theorem allocation_indexFaceQ_le (xs qs zs : List Code) (code : Code) (f : FaceCodes) :
    (Allocation.indexFaceQ xs qs zs code f).2≤(indexFaceQ xs qs zs code f).2 := by
  have hx := allocation_handle_le f.x xs
  have hz := allocation_handle_le f.z zs
  have h0 := allocation_handle_le f.q0 qs
  have h1 := allocation_handle_le f.q1 qs
  change (Allocation.handleQ f.x xs).2+(Allocation.handleQ f.z zs).2+
    (Allocation.handleQ f.q0 qs).2+(Allocation.handleQ f.q1 qs).2+1 ≤
    (handleQ f.x xs).2+(handleQ f.z zs).2+(handleQ f.q0 qs).2+(handleQ f.q1 qs).2+7
  omega
theorem allocation_packFrameQ_value (xs qs zs : List Code) (fs : List FaceRow) :
    (Allocation.packFrameQ xs qs zs fs).1=(packFrameQ xs qs zs fs).1 := by
  simp only [Allocation.packFrameQ, packFrameQ]
attribute [local simp] allocation_packFrameQ_value
theorem allocation_packFrameQ_le (xs qs zs : List Code) (fs : List FaceRow) :
    (Allocation.packFrameQ xs qs zs fs).2≤(packFrameQ xs qs zs fs).2 := by
  change 1 ≤ xs.length+qs.length+zs.length+fs.length+13
  omega
theorem allocation_memCodeQ_value (c : Code) (as : List Code) :
    (Allocation.memCodeQ c as).1=(memCodeQ c as).1 := by
  exact native_any_value_congr (Allocation.equalCodeQ c) (equalCodeQ c) as
    (allocation_equalCodeQ_value c)
attribute [local simp] allocation_memCodeQ_value
theorem allocation_memCodeQ_le (c : Code) (as : List Code) :
    (Allocation.memCodeQ c as).2≤(memCodeQ c as).2 := by
  exact allocation_any_le (Allocation.equalCodeQ c) (equalCodeQ c) as
    (allocation_equalCodeQ_le c)
theorem allocation_dedupQ_value (xs : List Code) :
    (Allocation.dedupQ xs).1=(dedupQ xs).1 := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
      simp only [Allocation.dedupQ,dedupQ,allocation_memCodeQ_value,ih]
theorem allocation_dedupQ_le (xs : List Code) :
    (Allocation.dedupQ xs).2≤(dedupQ xs).2 := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
      have hm := allocation_memCodeQ_le a (dedupQ as).1
      cases h : (memCodeQ a (dedupQ as).1).1 <;>
        simp [Allocation.dedupQ,dedupQ,allocation_dedupQ_value,
          allocation_memCodeQ_value,h] <;> omega
attribute [local simp] allocation_dedupQ_value
theorem native_rxFrameQ_simulation (F : Frame) (m : ℕ) :
    (Allocation.rxFrameQ F m).1=(rxFrameQ F m).1 ∧ (Allocation.rxFrameQ F m).2≤(rxFrameQ F m).2 := by
  unfold Allocation.rxFrameQ rxFrameQ
  let rawXA := Allocation.rxXCodesQ F m
  let rawXR := rxXCodesQ F m
  have h_rawX : rawXA.1=rawXR.1 ∧ rawXA.2≤rawXR.2 := by
    change (Allocation.rxXCodesQ F m).1=(rxXCodesQ F m).1 ∧ (Allocation.rxXCodesQ F m).2≤(rxXCodesQ F m).2
    exact ⟨allocation_rxXCodesQ_value F m, allocation_rxXCodesQ_le F m⟩
  let rawQA := Allocation.rxQCodesQ F m
  let rawQR := rxQCodesQ F m
  have h_rawQ : rawQA.1=rawQR.1 ∧ rawQA.2≤rawQR.2 := by
    change (Allocation.rxQCodesQ F m).1=(rxQCodesQ F m).1 ∧ (Allocation.rxQCodesQ F m).2≤(rxQCodesQ F m).2
    exact ⟨allocation_rxQCodesQ_value F m, allocation_rxQCodesQ_le F m⟩
  let rawZA := Allocation.rxZCodesQ F m
  let rawZR := rxZCodesQ F m
  have h_rawZ : rawZA.1=rawZR.1 ∧ rawZA.2≤rawZR.2 := by
    change (Allocation.rxZCodesQ F m).1=(rxZCodesQ F m).1 ∧ (Allocation.rxZCodesQ F m).2≤(rxZCodesQ F m).2
    exact ⟨allocation_rxZCodesQ_value F m, allocation_rxZCodesQ_le F m⟩
  let rawFA := Allocation.rxFaceCodesQ F m
  let rawFR := rxFaceCodesQ F m
  have h_rawF : rawFA.1=rawFR.1 ∧ rawFA.2≤rawFR.2 := by
    change (Allocation.rxFaceCodesQ F m).1=(rxFaceCodesQ F m).1 ∧ (Allocation.rxFaceCodesQ F m).2≤(rxFaceCodesQ F m).2
    exact ⟨allocation_rxFaceCodesQ_value F m, allocation_rxFaceCodesQ_le F m⟩
  let xsA := Allocation.dedupQ rawXA.1
  let xsR := dedupQ rawXR.1
  have h_xs : xsA.1=xsR.1 ∧ xsA.2≤xsR.2 := by
    change (Allocation.dedupQ rawXA.1).1=(dedupQ rawXR.1).1 ∧ (Allocation.dedupQ rawXA.1).2≤(dedupQ rawXR.1).2
    rw [h_rawX.1]
    exact ⟨allocation_dedupQ_value rawXR.1, allocation_dedupQ_le rawXR.1⟩
  let qsA := Allocation.dedupQ rawQA.1
  let qsR := dedupQ rawQR.1
  have h_qs : qsA.1=qsR.1 ∧ qsA.2≤qsR.2 := by
    change (Allocation.dedupQ rawQA.1).1=(dedupQ rawQR.1).1 ∧ (Allocation.dedupQ rawQA.1).2≤(dedupQ rawQR.1).2
    rw [h_rawQ.1]
    exact ⟨allocation_dedupQ_value rawQR.1, allocation_dedupQ_le rawQR.1⟩
  let zsA := Allocation.dedupQ rawZA.1
  let zsR := dedupQ rawZR.1
  have h_zs : zsA.1=zsR.1 ∧ zsA.2≤zsR.2 := by
    change (Allocation.dedupQ rawZA.1).1=(dedupQ rawZR.1).1 ∧ (Allocation.dedupQ rawZA.1).2≤(dedupQ rawZR.1).2
    rw [h_rawZ.1]
    exact ⟨allocation_dedupQ_value rawZR.1, allocation_dedupQ_le rawZR.1⟩
  let fcA := Allocation.dedupQ rawFA.1
  let fcR := dedupQ rawFR.1
  have h_fc : fcA.1=fcR.1 ∧ fcA.2≤fcR.2 := by
    change (Allocation.dedupQ rawFA.1).1=(dedupQ rawFR.1).1 ∧ (Allocation.dedupQ rawFA.1).2≤(dedupQ rawFR.1).2
    rw [h_rawF.1]
    exact ⟨allocation_dedupQ_value rawFR.1, allocation_dedupQ_le rawFR.1⟩
  let rowsA := Allocation.mapQ (fun f =>
    let points := Allocation.faceEndpointsQ F m f
    let out := Allocation.indexFaceQ xsA.1 qsA.1 zsA.1 f points.1
    (out.1,points.2+out.2)) fcA.1
  let rowsR := mapQ (fun f =>
    let points := faceEndpointsQ F m f
    let out := indexFaceQ xsR.1 qsR.1 zsR.1 f points.1
    (out.1,points.2+out.2)) fcR.1
  have h_rows : rowsA.1=rowsR.1 ∧ rowsA.2≤rowsR.2 := by
    change (Allocation.mapQ (fun f =>
    let points := Allocation.faceEndpointsQ F m f
    let out := Allocation.indexFaceQ xsA.1 qsA.1 zsA.1 f points.1
    (out.1,points.2+out.2)) fcA.1).1=(mapQ (fun f =>
    let points := faceEndpointsQ F m f
    let out := indexFaceQ xsR.1 qsR.1 zsR.1 f points.1
    (out.1,points.2+out.2)) fcR.1).1 ∧ (Allocation.mapQ (fun f =>
    let points := Allocation.faceEndpointsQ F m f
    let out := Allocation.indexFaceQ xsA.1 qsA.1 zsA.1 f points.1
    (out.1,points.2+out.2)) fcA.1).2≤(mapQ (fun f =>
    let points := faceEndpointsQ F m f
    let out := indexFaceQ xsR.1 qsR.1 zsR.1 f points.1
    (out.1,points.2+out.2)) fcR.1).2
    rw [h_xs.1, h_qs.1, h_zs.1, h_fc.1]
    apply native_map_simulation
    intro f
    let pointsA := Allocation.faceEndpointsQ F m f
    let pointsR := faceEndpointsQ F m f
    have h_points : pointsA.1=pointsR.1 ∧ pointsA.2≤pointsR.2 := by
      change (Allocation.faceEndpointsQ F m f).1=(faceEndpointsQ F m f).1 ∧ (Allocation.faceEndpointsQ F m f).2≤(faceEndpointsQ F m f).2
      exact ⟨allocation_faceEndpointsQ_value F m f, allocation_faceEndpointsQ_le F m f⟩
    let outA := Allocation.indexFaceQ xsR.1 qsR.1 zsR.1 f pointsA.1
    let outR := indexFaceQ xsR.1 qsR.1 zsR.1 f pointsR.1
    have h_out : outA.1=outR.1 ∧ outA.2≤outR.2 := by
      change (Allocation.indexFaceQ xsR.1 qsR.1 zsR.1 f pointsA.1).1=(indexFaceQ xsR.1 qsR.1 zsR.1 f pointsR.1).1 ∧ (Allocation.indexFaceQ xsR.1 qsR.1 zsR.1 f pointsA.1).2≤(indexFaceQ xsR.1 qsR.1 zsR.1 f pointsR.1).2
      rw [h_points.1]
      exact ⟨allocation_indexFaceQ_value xsR.1 qsR.1 zsR.1 f pointsR.1, allocation_indexFaceQ_le xsR.1 qsR.1 zsR.1 f pointsR.1⟩
    constructor
    · change outA.1=outR.1
      simpa only [h_out.1]
    · change pointsA.2+outA.2≤pointsR.2+outR.2
      have hc0 := h_points.2
      have hc1 := h_out.2
      omega
  let outA := Allocation.packFrameQ xsA.1 qsA.1 zsA.1 rowsA.1
  let outR := packFrameQ xsR.1 qsR.1 zsR.1 rowsR.1
  have h_out : outA.1=outR.1 ∧ outA.2≤outR.2 := by
    change (Allocation.packFrameQ xsA.1 qsA.1 zsA.1 rowsA.1).1=(packFrameQ xsR.1 qsR.1 zsR.1 rowsR.1).1 ∧ (Allocation.packFrameQ xsA.1 qsA.1 zsA.1 rowsA.1).2≤(packFrameQ xsR.1 qsR.1 zsR.1 rowsR.1).2
    rw [h_xs.1, h_qs.1, h_zs.1, h_rows.1]
    exact ⟨allocation_packFrameQ_value xsR.1 qsR.1 zsR.1 rowsR.1, allocation_packFrameQ_le xsR.1 qsR.1 zsR.1 rowsR.1⟩
  constructor
  · change outA.1=outR.1
    simpa only [h_out.1]
  · change rawXA.2+rawQA.2+rawZA.2+rawFA.2+xsA.2+qsA.2+zsA.2+fcA.2+rowsA.2+outA.2+4≤rawXR.2+rawQR.2+rawZR.2+rawFR.2+xsR.2+qsR.2+zsR.2+fcR.2+rowsR.2+outR.2+16
    have hc0 := h_rawX.2
    have hc1 := h_rawQ.2
    have hc2 := h_rawZ.2
    have hc3 := h_rawF.2
    have hc4 := h_xs.2
    have hc5 := h_qs.2
    have hc6 := h_zs.2
    have hc7 := h_fc.2
    have hc8 := h_rows.2
    have hc9 := h_out.2
    omega
theorem allocation_rxFrameQ_value (F : Frame) (m : ℕ) :
    (Allocation.rxFrameQ F m).1=(rxFrameQ F m).1 := by
  exact (native_rxFrameQ_simulation F m).1
attribute [local simp] allocation_rxFrameQ_value
theorem allocation_rxFrameQ_le (F : Frame) (m : ℕ) :
    (Allocation.rxFrameQ F m).2≤(rxFrameQ F m).2 := by
  exact (native_rxFrameQ_simulation F m).2
theorem allocation_transposeFrameQ_value (F : Frame) :
    (Allocation.transposeFrameQ F).1=(transposeFrameQ F).1 := by
  simp only [Allocation.transposeFrameQ, transposeFrameQ, allocation_map_value, mapQ_value]
attribute [local simp] allocation_transposeFrameQ_value
theorem allocation_transposeFrameQ_le (F : Frame) :
    (Allocation.transposeFrameQ F).2≤(transposeFrameQ F).2 := by
  have h := allocation_map_le
    (fun f : FaceRow => ((⟨f.code,f.z,f.x,f.q0,f.q1⟩ : FaceRow),1))
    (fun f : FaceRow => ((⟨f.code,f.z,f.x,f.q0,f.q1⟩ : FaceRow),17)) F.faces
    (by intro f; change 1≤17; decide)
  change (Allocation.mapQ (fun f : FaceRow => ((⟨f.code,f.z,f.x,f.q0,f.q1⟩ : FaceRow),1)) F.faces).2+1 ≤
    (mapQ (fun f : FaceRow => ((⟨f.code,f.z,f.x,f.q0,f.q1⟩ : FaceRow),17)) F.faces).2+17
  omega
theorem allocation_rzFrameQ_value (F : Frame) (m : ℕ) :
    (Allocation.rzFrameQ F m).1=(rzFrameQ F m).1 := by
  simp only [Allocation.rzFrameQ, rzFrameQ, allocation_transposeFrameQ_value, allocation_rxFrameQ_value]
attribute [local simp] allocation_rzFrameQ_value
theorem allocation_rzFrameQ_le (F : Frame) (m : ℕ) :
    (Allocation.rzFrameQ F m).2≤(rzFrameQ F m).2 := by
  have hi := allocation_transposeFrameQ_le F
  have hn := allocation_rxFrameQ_le (transposeFrameQ F).1 m
  have ho := allocation_transposeFrameQ_le (rxFrameQ (transposeFrameQ F).1 m).1
  simpa only [Allocation.rzFrameQ,rzFrameQ,allocation_transposeFrameQ_value,
    allocation_rxFrameQ_value] using Nat.add_le_add (Nat.add_le_add hi hn) ho
theorem allocation_nextFrameQ_value (S : OddScale) (n : ℕ) (F : Frame) :
    (Allocation.nextFrameQ S n F).1=(nextFrameQ S n F).1 := by
  by_cases h : n%2=0
  · simp only [Allocation.nextFrameQ,nextFrameQ,if_pos h,allocation_rxFrameQ_value]
  · simp only [Allocation.nextFrameQ,nextFrameQ,if_neg h,allocation_rzFrameQ_value]
attribute [local simp] allocation_nextFrameQ_value
theorem allocation_nextFrameQ_le (S : OddScale) (n : ℕ) (F : Frame) :
    (Allocation.nextFrameQ S n F).2≤(nextFrameQ S n F).2 := by
  by_cases h : n%2=0
  · simp only [Allocation.nextFrameQ,nextFrameQ,if_pos h]
    have hc := allocation_rxFrameQ_le F S.half
    omega
  · simp only [Allocation.nextFrameQ,nextFrameQ,if_neg h]
    have hc := allocation_rzFrameQ_le F S.half
    omega
theorem allocation_historyQ_value (S : OddScale) (n : ℕ) :
    (Allocation.historyQ S n).1=(historyQ S n).1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Allocation.historyQ,historyQ,Allocation.appendQ,appendQ,
        allocation_last_value,allocation_nextFrameQ_value,ih]
theorem allocation_historyQ_le (S : OddScale) (n : ℕ) :
    (Allocation.historyQ S n).2≤(historyQ S n).2 := by
  induction n with
  | zero => change 32≤169; decide
  | succ n ih =>
      have hl := allocation_last_le (historyQ S n).1
      have hs := allocation_nextFrameQ_le S n (lastFrameQ (historyQ S n).1).1
      simp only [Allocation.historyQ,historyQ,Allocation.appendQ,appendQ,
        allocation_historyQ_value,allocation_last_value,allocation_nextFrameQ_value]
      omega
attribute [local simp] allocation_historyQ_value
theorem allocation_generateQ_value (S : OddScale) (n : ℕ) :
    (Allocation.generateQ S n).1=(generateQ S n).1 := by
  simp only [Allocation.generateQ,generateQ,allocation_historyQ_value,allocation_last_value]
attribute [local simp] allocation_generateQ_value
theorem allocation_generateQ_le (S : OddScale) (n : ℕ) :
    (Allocation.generateQ S n).2≤(generateQ S n).2 := by
  have hh := allocation_historyQ_le S n
  have hl := allocation_last_le (historyQ S n).1
  simpa only [Allocation.generateQ,generateQ,allocation_historyQ_value] using Nat.add_le_add hh hl
theorem native_denseXQQ_simulation (F : Frame) :
    (Allocation.denseXQQ F).1=(denseXQQ F).1 ∧ (Allocation.denseXQQ F).2≤(denseXQQ F).2 := by
  unfold Allocation.denseXQQ denseXQQ
  apply native_loop_simulation
  intro x
  let qsA := Allocation.rangeQ F.nq
  let qsR := rangeQ F.nq
  have h_qs : qsA.1=qsR.1 ∧ qsA.2≤qsR.2 := by
    change (Allocation.rangeQ F.nq).1=(rangeQ F.nq).1 ∧ (Allocation.rangeQ F.nq).2≤(rangeQ F.nq).2
    exact ⟨allocation_range_value F.nq, allocation_range_le F.nq⟩
  let outA := Allocation.mapQ (fun q => let hit := Allocation.xqQ F x q; ((x,q,hit.1),hit.2+1)) qsA.1
  let outR := mapQ (fun q => let hit := xqQ F x q; ((x,q,hit.1),hit.2+4)) qsR.1
  have h_out : outA.1=outR.1 ∧ outA.2≤outR.2 := by
    change (Allocation.mapQ (fun q => let hit := Allocation.xqQ F x q; ((x,q,hit.1),hit.2+1)) qsA.1).1=(mapQ (fun q => let hit := xqQ F x q; ((x,q,hit.1),hit.2+4)) qsR.1).1 ∧ (Allocation.mapQ (fun q => let hit := Allocation.xqQ F x q; ((x,q,hit.1),hit.2+1)) qsA.1).2≤(mapQ (fun q => let hit := xqQ F x q; ((x,q,hit.1),hit.2+4)) qsR.1).2
    rw [h_qs.1]
    apply native_map_simulation
    intro q
    let hitA := Allocation.xqQ F x q
    let hitR := xqQ F x q
    have h_hit : hitA.1=hitR.1 ∧ hitA.2≤hitR.2 := by
      change (Allocation.xqQ F x q).1=(xqQ F x q).1 ∧ (Allocation.xqQ F x q).2≤(xqQ F x q).2
      exact ⟨allocation_xqQ_value F x q, allocation_xqQ_le F x q⟩
    constructor
    · change (x,q,hitA.1)=(x,q,hitR.1)
      simpa only [h_hit.1]
    · change hitA.2+1≤hitR.2+4
      have hc0 := h_hit.2
      omega
  constructor
  · change outA.1=outR.1
    simpa only [h_out.1]
  · change qsA.2+outA.2≤qsR.2+outR.2
    have hc0 := h_qs.2
    have hc1 := h_out.2
    omega
theorem allocation_denseXQQ_value (F : Frame) :
    (Allocation.denseXQQ F).1=(denseXQQ F).1 := by
  exact (native_denseXQQ_simulation F).1
attribute [local simp] allocation_denseXQQ_value
theorem allocation_denseXQQ_le (F : Frame) :
    (Allocation.denseXQQ F).2≤(denseXQQ F).2 := by
  exact (native_denseXQQ_simulation F).2
theorem native_denseQZQ_simulation (F : Frame) :
    (Allocation.denseQZQ F).1=(denseQZQ F).1 ∧ (Allocation.denseQZQ F).2≤(denseQZQ F).2 := by
  unfold Allocation.denseQZQ denseQZQ
  apply native_loop_simulation
  intro q
  let zsA := Allocation.rangeQ F.nz
  let zsR := rangeQ F.nz
  have h_zs : zsA.1=zsR.1 ∧ zsA.2≤zsR.2 := by
    change (Allocation.rangeQ F.nz).1=(rangeQ F.nz).1 ∧ (Allocation.rangeQ F.nz).2≤(rangeQ F.nz).2
    exact ⟨allocation_range_value F.nz, allocation_range_le F.nz⟩
  let outA := Allocation.mapQ (fun z => let hit := Allocation.qzQ F q z; ((q,z,hit.1),hit.2+1)) zsA.1
  let outR := mapQ (fun z => let hit := qzQ F q z; ((q,z,hit.1),hit.2+4)) zsR.1
  have h_out : outA.1=outR.1 ∧ outA.2≤outR.2 := by
    change (Allocation.mapQ (fun z => let hit := Allocation.qzQ F q z; ((q,z,hit.1),hit.2+1)) zsA.1).1=(mapQ (fun z => let hit := qzQ F q z; ((q,z,hit.1),hit.2+4)) zsR.1).1 ∧ (Allocation.mapQ (fun z => let hit := Allocation.qzQ F q z; ((q,z,hit.1),hit.2+1)) zsA.1).2≤(mapQ (fun z => let hit := qzQ F q z; ((q,z,hit.1),hit.2+4)) zsR.1).2
    rw [h_zs.1]
    apply native_map_simulation
    intro z
    let hitA := Allocation.qzQ F q z
    let hitR := qzQ F q z
    have h_hit : hitA.1=hitR.1 ∧ hitA.2≤hitR.2 := by
      change (Allocation.qzQ F q z).1=(qzQ F q z).1 ∧ (Allocation.qzQ F q z).2≤(qzQ F q z).2
      exact ⟨allocation_qzQ_value F q z, allocation_qzQ_le F q z⟩
    constructor
    · change (q,z,hitA.1)=(q,z,hitR.1)
      simpa only [h_hit.1]
    · change hitA.2+1≤hitR.2+4
      have hc0 := h_hit.2
      omega
  constructor
  · change outA.1=outR.1
    simpa only [h_out.1]
  · change zsA.2+outA.2≤zsR.2+outR.2
    have hc0 := h_zs.2
    have hc1 := h_out.2
    omega
theorem allocation_denseQZQ_value (F : Frame) :
    (Allocation.denseQZQ F).1=(denseQZQ F).1 := by
  exact (native_denseQZQ_simulation F).1
attribute [local simp] allocation_denseQZQ_value
theorem allocation_denseQZQ_le (F : Frame) :
    (Allocation.denseQZQ F).2≤(denseQZQ F).2 := by
  exact (native_denseQZQ_simulation F).2
theorem native_vertexCodesQ_simulation (F : Frame) :
    (Allocation.vertexCodesQ F).1=(vertexCodesQ F).1 ∧ (Allocation.vertexCodesQ F).2≤(vertexCodesQ F).2 := by
  unfold Allocation.vertexCodesQ vertexCodesQ
  let rawA := Allocation.collectQ [
    Allocation.loopQ F.nx (fun x => Allocation.singletonQ {owner:=x}),
    Allocation.loopQ F.nq (fun q => Allocation.singletonQ {family:=1,owner:=q}),
    Allocation.loopQ F.nz (fun z => Allocation.singletonQ {family:=2,owner:=z})]
  let rawR := collectQ [
    loopQ F.nx (fun x => singletonQ {owner:=x}),
    loopQ F.nq (fun q => singletonQ {family:=1,owner:=q}),
    loopQ F.nz (fun z => singletonQ {family:=2,owner:=z})]
  have h_raw : rawA.1=rawR.1 ∧ rawA.2≤rawR.2 := by
    change (Allocation.collectQ [
    Allocation.loopQ F.nx (fun x => Allocation.singletonQ {owner:=x}),
    Allocation.loopQ F.nq (fun q => Allocation.singletonQ {family:=1,owner:=q}),
    Allocation.loopQ F.nz (fun z => Allocation.singletonQ {family:=2,owner:=z})]).1=(collectQ [
    loopQ F.nx (fun x => singletonQ {owner:=x}),
    loopQ F.nq (fun q => singletonQ {family:=1,owner:=q}),
    loopQ F.nz (fun z => singletonQ {family:=2,owner:=z})]).1 ∧ (Allocation.collectQ [
    Allocation.loopQ F.nx (fun x => Allocation.singletonQ {owner:=x}),
    Allocation.loopQ F.nq (fun q => Allocation.singletonQ {family:=1,owner:=q}),
    Allocation.loopQ F.nz (fun z => Allocation.singletonQ {family:=2,owner:=z})]).2≤(collectQ [
    loopQ F.nx (fun x => singletonQ {owner:=x}),
    loopQ F.nq (fun q => singletonQ {family:=1,owner:=q}),
    loopQ F.nz (fun z => singletonQ {family:=2,owner:=z})]).2
    have hi0 : (Allocation.loopQ F.nx (fun x => Allocation.singletonQ {owner:=x})).1=(loopQ F.nx (fun x => singletonQ {owner:=x})).1 ∧ (Allocation.loopQ F.nx (fun x => Allocation.singletonQ {owner:=x})).2≤(loopQ F.nx (fun x => singletonQ {owner:=x})).2 := by
      apply native_loop_simulation
      intro x
      exact ⟨allocation_singletonQ_value {owner:=x}, allocation_singletonQ_le {owner:=x}⟩
    have hi1 : (Allocation.loopQ F.nq (fun q => Allocation.singletonQ {family:=1,owner:=q})).1=(loopQ F.nq (fun q => singletonQ {family:=1,owner:=q})).1 ∧ (Allocation.loopQ F.nq (fun q => Allocation.singletonQ {family:=1,owner:=q})).2≤(loopQ F.nq (fun q => singletonQ {family:=1,owner:=q})).2 := by
      apply native_loop_simulation
      intro q
      exact ⟨allocation_singletonQ_value {family:=1,owner:=q}, allocation_singletonQ_le {family:=1,owner:=q}⟩
    have hi2 : (Allocation.loopQ F.nz (fun z => Allocation.singletonQ {family:=2,owner:=z})).1=(loopQ F.nz (fun z => singletonQ {family:=2,owner:=z})).1 ∧ (Allocation.loopQ F.nz (fun z => Allocation.singletonQ {family:=2,owner:=z})).2≤(loopQ F.nz (fun z => singletonQ {family:=2,owner:=z})).2 := by
      apply native_loop_simulation
      intro z
      exact ⟨allocation_singletonQ_value {family:=2,owner:=z}, allocation_singletonQ_le {family:=2,owner:=z}⟩
    apply native_collect_simulation
    · change [(Allocation.loopQ F.nx (fun x => Allocation.singletonQ {owner:=x})).1, (Allocation.loopQ F.nq (fun q => Allocation.singletonQ {family:=1,owner:=q})).1, (Allocation.loopQ F.nz (fun z => Allocation.singletonQ {family:=2,owner:=z})).1]=[(loopQ F.nx (fun x => singletonQ {owner:=x})).1, (loopQ F.nq (fun q => singletonQ {family:=1,owner:=q})).1, (loopQ F.nz (fun z => singletonQ {family:=2,owner:=z})).1]
      exact congrArg₂ List.cons hi0.1 (congrArg₂ List.cons hi1.1 (congrArg₂ List.cons hi2.1 (rfl)))
    · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      have hc0 := hi0.2
      have hc1 := hi1.2
      have hc2 := hi2.2
      omega
  let uniqueA := Allocation.dedupQ rawA.1
  let uniqueR := dedupQ rawR.1
  have h_unique : uniqueA.1=uniqueR.1 ∧ uniqueA.2≤uniqueR.2 := by
    change (Allocation.dedupQ rawA.1).1=(dedupQ rawR.1).1 ∧ (Allocation.dedupQ rawA.1).2≤(dedupQ rawR.1).2
    rw [h_raw.1]
    exact ⟨allocation_dedupQ_value rawR.1, allocation_dedupQ_le rawR.1⟩
  constructor
  · change uniqueA.1=uniqueR.1
    simpa only [h_unique.1]
  · change rawA.2+uniqueA.2≤rawR.2+uniqueR.2+1
    have hc0 := h_raw.2
    have hc1 := h_unique.2
    omega
theorem allocation_vertexCodesQ_value (F : Frame) :
    (Allocation.vertexCodesQ F).1=(vertexCodesQ F).1 := by
  exact (native_vertexCodesQ_simulation F).1
attribute [local simp] allocation_vertexCodesQ_value
theorem allocation_vertexCodesQ_le (F : Frame) :
    (Allocation.vertexCodesQ F).2≤(vertexCodesQ F).2 := by
  exact (native_vertexCodesQ_simulation F).2
theorem native_edgeCodesQ_simulation (F : Frame) :
    (Allocation.edgeCodesQ F).1=(edgeCodesQ F).1 ∧ (Allocation.edgeCodesQ F).2≤(edgeCodesQ F).2 := by
  unfold Allocation.edgeCodesQ edgeCodesQ
  let aA := Allocation.denseXQQ F
  let aR := denseXQQ F
  have h_a : aA.1=aR.1 ∧ aA.2≤aR.2 := by
    change (Allocation.denseXQQ F).1=(denseXQQ F).1 ∧ (Allocation.denseXQQ F).2≤(denseXQQ F).2
    exact ⟨allocation_denseXQQ_value F, allocation_denseXQQ_le F⟩
  let bA := Allocation.denseQZQ F
  let bR := denseQZQ F
  have h_b : bA.1=bR.1 ∧ bA.2≤bR.2 := by
    change (Allocation.denseQZQ F).1=(denseQZQ F).1 ∧ (Allocation.denseQZQ F).2≤(denseQZQ F).2
    exact ⟨allocation_denseQZQ_value F, allocation_denseQZQ_le F⟩
  let axA := Allocation.filterQ (fun t => (t.2.2,0)) aA.1
  let axR := filterQ (fun t => (t.2.2,2)) aR.1
  have h_ax : axA.1=axR.1 ∧ axA.2≤axR.2 := by
    change (Allocation.filterQ (fun t => (t.2.2,0)) aA.1).1=(filterQ (fun t => (t.2.2,2)) aR.1).1 ∧ (Allocation.filterQ (fun t => (t.2.2,0)) aA.1).2≤(filterQ (fun t => (t.2.2,2)) aR.1).2
    rw [h_a.1]
    apply native_filter_simulation
    intro t
    constructor
    · change t.2.2=t.2.2
      rfl
    · change 0≤2
      omega
  let bzA := Allocation.filterQ (fun t => (t.2.2,0)) bA.1
  let bzR := filterQ (fun t => (t.2.2,2)) bR.1
  have h_bz : bzA.1=bzR.1 ∧ bzA.2≤bzR.2 := by
    change (Allocation.filterQ (fun t => (t.2.2,0)) bA.1).1=(filterQ (fun t => (t.2.2,2)) bR.1).1 ∧ (Allocation.filterQ (fun t => (t.2.2,0)) bA.1).2≤(filterQ (fun t => (t.2.2,2)) bR.1).2
    rw [h_b.1]
    apply native_filter_simulation
    intro t
    constructor
    · change t.2.2=t.2.2
      rfl
    · change 0≤2
      omega
  let leftA := Allocation.mapQ (fun t => Allocation.emitQ {owner:=t.1,p:=t.2.1}) axA.1
  let leftR := mapQ (fun t => emitQ {owner:=t.1,p:=t.2.1}) axR.1
  have h_left : leftA.1=leftR.1 ∧ leftA.2≤leftR.2 := by
    change (Allocation.mapQ (fun t => Allocation.emitQ {owner:=t.1,p:=t.2.1}) axA.1).1=(mapQ (fun t => emitQ {owner:=t.1,p:=t.2.1}) axR.1).1 ∧ (Allocation.mapQ (fun t => Allocation.emitQ {owner:=t.1,p:=t.2.1}) axA.1).2≤(mapQ (fun t => emitQ {owner:=t.1,p:=t.2.1}) axR.1).2
    rw [h_ax.1]
    apply native_map_simulation
    intro t
    exact ⟨allocation_emitQ_value {owner:=t.1,p:=t.2.1}, allocation_emitQ_le {owner:=t.1,p:=t.2.1}⟩
  let rightA := Allocation.mapQ (fun t => Allocation.emitQ {family:=1,owner:=t.1,p:=t.2.1}) bzA.1
  let rightR := mapQ (fun t => emitQ {family:=1,owner:=t.1,p:=t.2.1}) bzR.1
  have h_right : rightA.1=rightR.1 ∧ rightA.2≤rightR.2 := by
    change (Allocation.mapQ (fun t => Allocation.emitQ {family:=1,owner:=t.1,p:=t.2.1}) bzA.1).1=(mapQ (fun t => emitQ {family:=1,owner:=t.1,p:=t.2.1}) bzR.1).1 ∧ (Allocation.mapQ (fun t => Allocation.emitQ {family:=1,owner:=t.1,p:=t.2.1}) bzA.1).2≤(mapQ (fun t => emitQ {family:=1,owner:=t.1,p:=t.2.1}) bzR.1).2
    rw [h_bz.1]
    apply native_map_simulation
    intro t
    exact ⟨allocation_emitQ_value {family:=1,owner:=t.1,p:=t.2.1}, allocation_emitQ_le {family:=1,owner:=t.1,p:=t.2.1}⟩
  let outA := Allocation.collectQ [leftA,rightA]
  let outR := collectQ [leftR,rightR]
  have h_out : outA.1=outR.1 ∧ outA.2≤outR.2 := by
    change (Allocation.collectQ [leftA,rightA]).1=(collectQ [leftR,rightR]).1 ∧ (Allocation.collectQ [leftA,rightA]).2≤(collectQ [leftR,rightR]).2
    have hi0 : (leftA).1=(leftR).1 ∧ (leftA).2≤(leftR).2 := by
      exact h_left
    have hi1 : (rightA).1=(rightR).1 ∧ (rightA).2≤(rightR).2 := by
      exact h_right
    apply native_collect_simulation
    · change [(leftA).1, (rightA).1]=[(leftR).1, (rightR).1]
      exact congrArg₂ List.cons hi0.1 (congrArg₂ List.cons hi1.1 (rfl))
    · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      have hc0 := hi0.2
      have hc1 := hi1.2
      omega
  let uniqueA := Allocation.dedupQ outA.1
  let uniqueR := dedupQ outR.1
  have h_unique : uniqueA.1=uniqueR.1 ∧ uniqueA.2≤uniqueR.2 := by
    change (Allocation.dedupQ outA.1).1=(dedupQ outR.1).1 ∧ (Allocation.dedupQ outA.1).2≤(dedupQ outR.1).2
    rw [h_out.1]
    exact ⟨allocation_dedupQ_value outR.1, allocation_dedupQ_le outR.1⟩
  constructor
  · change uniqueA.1=uniqueR.1
    simpa only [h_unique.1]
  · change aA.2+bA.2+axA.2+bzA.2+outA.2+uniqueA.2≤aR.2+bR.2+axR.2+bzR.2+outR.2+uniqueR.2+1
    have hc0 := h_a.2
    have hc1 := h_b.2
    have hc2 := h_ax.2
    have hc3 := h_bz.2
    have hc4 := h_out.2
    have hc5 := h_unique.2
    omega
theorem allocation_edgeCodesQ_value (F : Frame) :
    (Allocation.edgeCodesQ F).1=(edgeCodesQ F).1 := by
  exact (native_edgeCodesQ_simulation F).1
attribute [local simp] allocation_edgeCodesQ_value
theorem allocation_edgeCodesQ_le (F : Frame) :
    (Allocation.edgeCodesQ F).2≤(edgeCodesQ F).2 := by
  exact (native_edgeCodesQ_simulation F).2
theorem allocation_edgeVertexTestQ_value (e v : Code) :
    (Allocation.edgeVertexTestQ e v).1=(edgeVertexTestQ e v).1 := by
  simp only [Allocation.edgeVertexTestQ, edgeVertexTestQ]
attribute [local simp] allocation_edgeVertexTestQ_value
theorem allocation_edgeVertexTestQ_le (e v : Code) :
    (Allocation.edgeVertexTestQ e v).2≤(edgeVertexTestQ e v).2 := by
  exact Nat.zero_le _
theorem allocation_faceEdgeTestQ_value (f : FaceRow) (e : Code) :
    (Allocation.faceEdgeTestQ f e).1=(faceEdgeTestQ f e).1 := by
  simp only [Allocation.faceEdgeTestQ, faceEdgeTestQ]
attribute [local simp] allocation_faceEdgeTestQ_value
theorem allocation_faceEdgeTestQ_le (f : FaceRow) (e : Code) :
    (Allocation.faceEdgeTestQ f e).2≤(faceEdgeTestQ f e).2 := by
  exact Nat.zero_le _
theorem native_cellularBoundary1Q_simulation (vertices edges : List Code) :
    (Allocation.cellularBoundary1Q vertices edges).1=(cellularBoundary1Q vertices edges).1 ∧ (Allocation.cellularBoundary1Q vertices edges).2≤(cellularBoundary1Q vertices edges).2 := by
  unfold Allocation.cellularBoundary1Q cellularBoundary1Q
  let eiA := Allocation.rangeQ edges.length
  let eiR := rangeQ edges.length
  have h_ei : eiA.1=eiR.1 ∧ eiA.2≤eiR.2 := by
    change (Allocation.rangeQ edges.length).1=(rangeQ edges.length).1 ∧ (Allocation.rangeQ edges.length).2≤(rangeQ edges.length).2
    exact ⟨allocation_range_value edges.length, allocation_range_le edges.length⟩
  let viA := Allocation.rangeQ vertices.length
  let viR := rangeQ vertices.length
  have h_vi : viA.1=viR.1 ∧ viA.2≤viR.2 := by
    change (Allocation.rangeQ vertices.length).1=(rangeQ vertices.length).1 ∧ (Allocation.rangeQ vertices.length).2≤(rangeQ vertices.length).2
    exact ⟨allocation_range_value vertices.length, allocation_range_le vertices.length⟩
  let outA := Allocation.flatMapQ (fun e => Allocation.mapQ (fun v =>
    let ec := edges[e]?.getD {}
    let vc := vertices[v]?.getD {}
    let hit := Allocation.edgeVertexTestQ ec vc
    ((v,e,hit.1),hit.2+1)) viA.1) eiA.1
  let outR := flatMapQ (fun e => mapQ (fun v =>
    let ec := edges[e]?.getD {}
    let vc := vertices[v]?.getD {}
    let hit := edgeVertexTestQ ec vc
    ((v,e,hit.1),2*e+2*v+hit.2+8)) viR.1) eiR.1
  have h_out : outA.1=outR.1 ∧ outA.2≤outR.2 := by
    change (Allocation.flatMapQ (fun e => Allocation.mapQ (fun v =>
    let ec := edges[e]?.getD {}
    let vc := vertices[v]?.getD {}
    let hit := Allocation.edgeVertexTestQ ec vc
    ((v,e,hit.1),hit.2+1)) viA.1) eiA.1).1=(flatMapQ (fun e => mapQ (fun v =>
    let ec := edges[e]?.getD {}
    let vc := vertices[v]?.getD {}
    let hit := edgeVertexTestQ ec vc
    ((v,e,hit.1),2*e+2*v+hit.2+8)) viR.1) eiR.1).1 ∧ (Allocation.flatMapQ (fun e => Allocation.mapQ (fun v =>
    let ec := edges[e]?.getD {}
    let vc := vertices[v]?.getD {}
    let hit := Allocation.edgeVertexTestQ ec vc
    ((v,e,hit.1),hit.2+1)) viA.1) eiA.1).2≤(flatMapQ (fun e => mapQ (fun v =>
    let ec := edges[e]?.getD {}
    let vc := vertices[v]?.getD {}
    let hit := edgeVertexTestQ ec vc
    ((v,e,hit.1),2*e+2*v+hit.2+8)) viR.1) eiR.1).2
    rw [h_ei.1, h_vi.1]
    apply native_flat_simulation
    intro e
    apply native_map_simulation
    intro v
    let ecR := edges[e]?.getD {}
    let vcR := vertices[v]?.getD {}
    let hitA := Allocation.edgeVertexTestQ ecR vcR
    let hitR := edgeVertexTestQ ecR vcR
    have h_hit : hitA.1=hitR.1 ∧ hitA.2≤hitR.2 := by
      change (Allocation.edgeVertexTestQ ecR vcR).1=(edgeVertexTestQ ecR vcR).1 ∧ (Allocation.edgeVertexTestQ ecR vcR).2≤(edgeVertexTestQ ecR vcR).2

      exact ⟨allocation_edgeVertexTestQ_value ecR vcR, allocation_edgeVertexTestQ_le ecR vcR⟩
    constructor
    · change (v,e,hitA.1)=(v,e,hitR.1)
      simpa only [h_hit.1]
    · change hitA.2+1≤2*e+2*v+hitR.2+8
      have hc0 := h_hit.2
      omega
  constructor
  · change outA.1=outR.1
    simpa only [h_out.1]
  · change eiA.2+viA.2+outA.2≤vertices.length+edges.length+eiR.2+viR.2+outR.2+2
    have hc0 := h_ei.2
    have hc1 := h_vi.2
    have hc2 := h_out.2
    omega
theorem allocation_cellularBoundary1Q_value (vertices edges : List Code) :
    (Allocation.cellularBoundary1Q vertices edges).1=(cellularBoundary1Q vertices edges).1 := by
  exact (native_cellularBoundary1Q_simulation vertices edges).1
attribute [local simp] allocation_cellularBoundary1Q_value
theorem allocation_cellularBoundary1Q_le (vertices edges : List Code) :
    (Allocation.cellularBoundary1Q vertices edges).2≤(cellularBoundary1Q vertices edges).2 := by
  exact (native_cellularBoundary1Q_simulation vertices edges).2
theorem native_cellularBoundary2Q_simulation (F : Frame) (edges : List Code) :
    (Allocation.cellularBoundary2Q F edges).1=(cellularBoundary2Q F edges).1 ∧ (Allocation.cellularBoundary2Q F edges).2≤(cellularBoundary2Q F edges).2 := by
  unfold Allocation.cellularBoundary2Q cellularBoundary2Q
  let fiA := Allocation.rangeQ F.nf
  let fiR := rangeQ F.nf
  have h_fi : fiA.1=fiR.1 ∧ fiA.2≤fiR.2 := by
    change (Allocation.rangeQ F.nf).1=(rangeQ F.nf).1 ∧ (Allocation.rangeQ F.nf).2≤(rangeQ F.nf).2
    exact ⟨allocation_range_value F.nf, allocation_range_le F.nf⟩
  let eiA := Allocation.rangeQ edges.length
  let eiR := rangeQ edges.length
  have h_ei : eiA.1=eiR.1 ∧ eiA.2≤eiR.2 := by
    change (Allocation.rangeQ edges.length).1=(rangeQ edges.length).1 ∧ (Allocation.rangeQ edges.length).2≤(rangeQ edges.length).2
    exact ⟨allocation_range_value edges.length, allocation_range_le edges.length⟩
  let outA := Allocation.flatMapQ (fun f =>
    let row := Allocation.faceAtQ F.faces f
    let cells := Allocation.mapQ (fun e =>
      let ec := edges[e]?.getD {}
      let hit := Allocation.faceEdgeTestQ row.1 ec
      ((e,f,hit.1),hit.2+1)) eiA.1
    (cells.1,row.2+cells.2)) fiA.1
  let outR := flatMapQ (fun f =>
    let row := faceAtQ F.faces f
    let cells := mapQ (fun e =>
      let ec := edges[e]?.getD {}
      let hit := faceEdgeTestQ row.1 ec
      ((e,f,hit.1),2*e+hit.2+6)) eiR.1
    (cells.1,row.2+cells.2)) fiR.1
  have h_out : outA.1=outR.1 ∧ outA.2≤outR.2 := by
    change (Allocation.flatMapQ (fun f =>
    let row := Allocation.faceAtQ F.faces f
    let cells := Allocation.mapQ (fun e =>
      let ec := edges[e]?.getD {}
      let hit := Allocation.faceEdgeTestQ row.1 ec
      ((e,f,hit.1),hit.2+1)) eiA.1
    (cells.1,row.2+cells.2)) fiA.1).1=(flatMapQ (fun f =>
    let row := faceAtQ F.faces f
    let cells := mapQ (fun e =>
      let ec := edges[e]?.getD {}
      let hit := faceEdgeTestQ row.1 ec
      ((e,f,hit.1),2*e+hit.2+6)) eiR.1
    (cells.1,row.2+cells.2)) fiR.1).1 ∧ (Allocation.flatMapQ (fun f =>
    let row := Allocation.faceAtQ F.faces f
    let cells := Allocation.mapQ (fun e =>
      let ec := edges[e]?.getD {}
      let hit := Allocation.faceEdgeTestQ row.1 ec
      ((e,f,hit.1),hit.2+1)) eiA.1
    (cells.1,row.2+cells.2)) fiA.1).2≤(flatMapQ (fun f =>
    let row := faceAtQ F.faces f
    let cells := mapQ (fun e =>
      let ec := edges[e]?.getD {}
      let hit := faceEdgeTestQ row.1 ec
      ((e,f,hit.1),2*e+hit.2+6)) eiR.1
    (cells.1,row.2+cells.2)) fiR.1).2
    rw [h_fi.1, h_ei.1]
    apply native_flat_simulation
    intro f
    let rowA := Allocation.faceAtQ F.faces f
    let rowR := faceAtQ F.faces f
    have h_row : rowA.1=rowR.1 ∧ rowA.2≤rowR.2 := by
      change (Allocation.faceAtQ F.faces f).1=(faceAtQ F.faces f).1 ∧ (Allocation.faceAtQ F.faces f).2≤(faceAtQ F.faces f).2
      exact ⟨allocation_faceAt_value F.faces f, allocation_faceAt_le F.faces f⟩
    let cellsA := Allocation.mapQ (fun e =>
      let ec := edges[e]?.getD {}
      let hit := Allocation.faceEdgeTestQ rowA.1 ec
      ((e,f,hit.1),hit.2+1)) eiR.1
    let cellsR := mapQ (fun e =>
      let ec := edges[e]?.getD {}
      let hit := faceEdgeTestQ rowR.1 ec
      ((e,f,hit.1),2*e+hit.2+6)) eiR.1
    have h_cells : cellsA.1=cellsR.1 ∧ cellsA.2≤cellsR.2 := by
      change (Allocation.mapQ (fun e =>
      let ec := edges[e]?.getD {}
      let hit := Allocation.faceEdgeTestQ rowA.1 ec
      ((e,f,hit.1),hit.2+1)) eiR.1).1=(mapQ (fun e =>
      let ec := edges[e]?.getD {}
      let hit := faceEdgeTestQ rowR.1 ec
      ((e,f,hit.1),2*e+hit.2+6)) eiR.1).1 ∧ (Allocation.mapQ (fun e =>
      let ec := edges[e]?.getD {}
      let hit := Allocation.faceEdgeTestQ rowA.1 ec
      ((e,f,hit.1),hit.2+1)) eiR.1).2≤(mapQ (fun e =>
      let ec := edges[e]?.getD {}
      let hit := faceEdgeTestQ rowR.1 ec
      ((e,f,hit.1),2*e+hit.2+6)) eiR.1).2
      rw [h_row.1]
      apply native_map_simulation
      intro e
      let ecR := edges[e]?.getD {}
      let hitA := Allocation.faceEdgeTestQ rowR.1 ecR
      let hitR := faceEdgeTestQ rowR.1 ecR
      have h_hit : hitA.1=hitR.1 ∧ hitA.2≤hitR.2 := by
        change (Allocation.faceEdgeTestQ rowR.1 ecR).1=(faceEdgeTestQ rowR.1 ecR).1 ∧ (Allocation.faceEdgeTestQ rowR.1 ecR).2≤(faceEdgeTestQ rowR.1 ecR).2

        exact ⟨allocation_faceEdgeTestQ_value rowR.1 ecR, allocation_faceEdgeTestQ_le rowR.1 ecR⟩
      constructor
      · change (e,f,hitA.1)=(e,f,hitR.1)
        simpa only [h_hit.1]
      · change hitA.2+1≤2*e+hitR.2+6
        have hc0 := h_hit.2
        omega
    constructor
    · change cellsA.1=cellsR.1
      simpa only [h_cells.1]
    · change rowA.2+cellsA.2≤rowR.2+cellsR.2
      have hc0 := h_row.2
      have hc1 := h_cells.2
      omega
  constructor
  · change outA.1=outR.1
    simpa only [h_out.1]
  · change fiA.2+eiA.2+outA.2≤edges.length+fiR.2+eiR.2+outR.2+2
    have hc0 := h_fi.2
    have hc1 := h_ei.2
    have hc2 := h_out.2
    omega
theorem allocation_cellularBoundary2Q_value (F : Frame) (edges : List Code) :
    (Allocation.cellularBoundary2Q F edges).1=(cellularBoundary2Q F edges).1 := by
  exact (native_cellularBoundary2Q_simulation F edges).1
attribute [local simp] allocation_cellularBoundary2Q_value
theorem allocation_cellularBoundary2Q_le (F : Frame) (edges : List Code) :
    (Allocation.cellularBoundary2Q F edges).2≤(cellularBoundary2Q F edges).2 := by
  exact (native_cellularBoundary2Q_simulation F edges).2
theorem native_runQ_simulation (S : OddScale) (n : ℕ) :
    (Allocation.runQ S n).1=(runQ S n).1 ∧ (Allocation.runQ S n).2≤(runQ S n).2 := by
  unfold Allocation.runQ runQ
  let frameA := Allocation.generateQ S n
  let frameR := generateQ S n
  have h_frame : frameA.1=frameR.1 ∧ frameA.2≤frameR.2 := by
    change (Allocation.generateQ S n).1=(generateQ S n).1 ∧ (Allocation.generateQ S n).2≤(generateQ S n).2
    exact ⟨allocation_generateQ_value S n, allocation_generateQ_le S n⟩
  let aA := Allocation.denseXQQ frameA.1
  let aR := denseXQQ frameR.1
  have h_a : aA.1=aR.1 ∧ aA.2≤aR.2 := by
    change (Allocation.denseXQQ frameA.1).1=(denseXQQ frameR.1).1 ∧ (Allocation.denseXQQ frameA.1).2≤(denseXQQ frameR.1).2
    rw [h_frame.1]
    exact ⟨allocation_denseXQQ_value frameR.1, allocation_denseXQQ_le frameR.1⟩
  let bA := Allocation.denseQZQ frameA.1
  let bR := denseQZQ frameR.1
  have h_b : bA.1=bR.1 ∧ bA.2≤bR.2 := by
    change (Allocation.denseQZQ frameA.1).1=(denseQZQ frameR.1).1 ∧ (Allocation.denseQZQ frameA.1).2≤(denseQZQ frameR.1).2
    rw [h_frame.1]
    exact ⟨allocation_denseQZQ_value frameR.1, allocation_denseQZQ_le frameR.1⟩
  let verticesA := Allocation.vertexCodesQ frameA.1
  let verticesR := vertexCodesQ frameR.1
  have h_vertices : verticesA.1=verticesR.1 ∧ verticesA.2≤verticesR.2 := by
    change (Allocation.vertexCodesQ frameA.1).1=(vertexCodesQ frameR.1).1 ∧ (Allocation.vertexCodesQ frameA.1).2≤(vertexCodesQ frameR.1).2
    rw [h_frame.1]
    exact ⟨allocation_vertexCodesQ_value frameR.1, allocation_vertexCodesQ_le frameR.1⟩
  let edgesA := Allocation.edgeCodesQ frameA.1
  let edgesR := edgeCodesQ frameR.1
  have h_edges : edgesA.1=edgesR.1 ∧ edgesA.2≤edgesR.2 := by
    change (Allocation.edgeCodesQ frameA.1).1=(edgeCodesQ frameR.1).1 ∧ (Allocation.edgeCodesQ frameA.1).2≤(edgeCodesQ frameR.1).2
    rw [h_frame.1]
    exact ⟨allocation_edgeCodesQ_value frameR.1, allocation_edgeCodesQ_le frameR.1⟩
  let boundary1A := Allocation.cellularBoundary1Q verticesA.1 edgesA.1
  let boundary1R := cellularBoundary1Q verticesR.1 edgesR.1
  have h_boundary1 : boundary1A.1=boundary1R.1 ∧ boundary1A.2≤boundary1R.2 := by
    change (Allocation.cellularBoundary1Q verticesA.1 edgesA.1).1=(cellularBoundary1Q verticesR.1 edgesR.1).1 ∧ (Allocation.cellularBoundary1Q verticesA.1 edgesA.1).2≤(cellularBoundary1Q verticesR.1 edgesR.1).2
    rw [h_vertices.1, h_edges.1]
    exact ⟨allocation_cellularBoundary1Q_value verticesR.1 edgesR.1, allocation_cellularBoundary1Q_le verticesR.1 edgesR.1⟩
  let boundary2A := Allocation.cellularBoundary2Q frameA.1 edgesA.1
  let boundary2R := cellularBoundary2Q frameR.1 edgesR.1
  have h_boundary2 : boundary2A.1=boundary2R.1 ∧ boundary2A.2≤boundary2R.2 := by
    change (Allocation.cellularBoundary2Q frameA.1 edgesA.1).1=(cellularBoundary2Q frameR.1 edgesR.1).1 ∧ (Allocation.cellularBoundary2Q frameA.1 edgesA.1).2≤(cellularBoundary2Q frameR.1 edgesR.1).2
    rw [h_frame.1, h_edges.1]
    exact ⟨allocation_cellularBoundary2Q_value frameR.1 edgesR.1, allocation_cellularBoundary2Q_le frameR.1 edgesR.1⟩
  constructor
  · change (⟨frameA.1,aA.1,bA.1,verticesA.1,edgesA.1,boundary1A.1,boundary2A.1⟩ : Output)=⟨frameR.1,aR.1,bR.1,verticesR.1,edgesR.1,boundary1R.1,boundary2R.1⟩
    simpa only [h_frame.1, h_a.1, h_b.1, h_vertices.1, h_edges.1, h_boundary1.1, h_boundary2.1]
  · change frameA.2+aA.2+bA.2+verticesA.2+edgesA.2+boundary1A.2+boundary2A.2+1≤frameR.2+aR.2+bR.2+verticesR.2+edgesR.2+boundary1R.2+boundary2R.2+8
    have hc0 := h_frame.2
    have hc1 := h_a.2
    have hc2 := h_b.2
    have hc3 := h_vertices.2
    have hc4 := h_edges.2
    have hc5 := h_boundary1.2
    have hc6 := h_boundary2.2
    omega
theorem allocation_runQ_value (S : OddScale) (n : ℕ) :
    (Allocation.runQ S n).1=(runQ S n).1 := by
  exact (native_runQ_simulation S n).1
attribute [local simp] allocation_runQ_value
theorem allocation_runQ_le (S : OddScale) (n : ℕ) :
    (Allocation.runQ S n).2≤(runQ S n).2 := by
  exact (native_runQ_simulation S n).2
theorem allocation_seedRowsQ_value  :
    (Allocation.seedRowsQ).1=(seedRowsQ).1 := by
  rfl
attribute [local simp] allocation_seedRowsQ_value
theorem allocation_seedRowsQ_le  :
    (Allocation.seedRowsQ).2≤(seedRowsQ).2 := by
  decide
theorem native_triangleCodesQ_simulation (F : Frame) :
    (Allocation.triangleCodesQ F).1=(triangleCodesQ F).1 ∧ (Allocation.triangleCodesQ F).2≤(triangleCodesQ F).2 := by
  unfold Allocation.triangleCodesQ triangleCodesQ
  let rawA := Allocation.loopQ F.nf (fun f => Allocation.mapQ (fun d => Allocation.emitQ {family:=3,owner:=f,copy:=d}) [0,1])
  let rawR := loopQ F.nf (fun f => mapQ (fun d => emitQ {family:=3,owner:=f,copy:=d}) [0,1])
  have h_raw : rawA.1=rawR.1 ∧ rawA.2≤rawR.2 := by
    change (Allocation.loopQ F.nf (fun f => Allocation.mapQ (fun d => Allocation.emitQ {family:=3,owner:=f,copy:=d}) [0,1])).1=(loopQ F.nf (fun f => mapQ (fun d => emitQ {family:=3,owner:=f,copy:=d}) [0,1])).1 ∧ (Allocation.loopQ F.nf (fun f => Allocation.mapQ (fun d => Allocation.emitQ {family:=3,owner:=f,copy:=d}) [0,1])).2≤(loopQ F.nf (fun f => mapQ (fun d => emitQ {family:=3,owner:=f,copy:=d}) [0,1])).2
    apply native_loop_simulation
    intro f
    apply native_map_simulation
    intro d
    exact ⟨allocation_emitQ_value {family:=3,owner:=f,copy:=d}, allocation_emitQ_le {family:=3,owner:=f,copy:=d}⟩
  let uniqueA := Allocation.dedupQ rawA.1
  let uniqueR := dedupQ rawR.1
  have h_unique : uniqueA.1=uniqueR.1 ∧ uniqueA.2≤uniqueR.2 := by
    change (Allocation.dedupQ rawA.1).1=(dedupQ rawR.1).1 ∧ (Allocation.dedupQ rawA.1).2≤(dedupQ rawR.1).2
    rw [h_raw.1]
    exact ⟨allocation_dedupQ_value rawR.1, allocation_dedupQ_le rawR.1⟩
  constructor
  · change uniqueA.1=uniqueR.1
    simpa only [h_unique.1]
  · change rawA.2+uniqueA.2≤rawR.2+uniqueR.2
    have hc0 := h_raw.2
    have hc1 := h_unique.2
    omega
theorem allocation_triangleCodesQ_value (F : Frame) :
    (Allocation.triangleCodesQ F).1=(triangleCodesQ F).1 := by
  exact (native_triangleCodesQ_simulation F).1
attribute [local simp] allocation_triangleCodesQ_value
theorem allocation_triangleCodesQ_le (F : Frame) :
    (Allocation.triangleCodesQ F).2≤(triangleCodesQ F).2 := by
  exact (native_triangleCodesQ_simulation F).2
theorem native_setupQ_simulation (S : OddScale) (n : ℕ) :
    (Allocation.setupQ S n).1=(setupQ S n).1 ∧ (Allocation.setupQ S n).2≤(setupQ S n).2 := by
  unfold Allocation.setupQ setupQ
  let dataA := Allocation.runQ S n
  let dataR := runQ S n
  have h_data : dataA.1=dataR.1 ∧ dataA.2≤dataR.2 := by
    change (Allocation.runQ S n).1=(runQ S n).1 ∧ (Allocation.runQ S n).2≤(runQ S n).2
    exact ⟨allocation_runQ_value S n, allocation_runQ_le S n⟩
  let trianglesA := Allocation.triangleCodesQ dataA.1.frame
  let trianglesR := triangleCodesQ dataR.1.frame
  have h_triangles : trianglesA.1=trianglesR.1 ∧ trianglesA.2≤trianglesR.2 := by
    change (Allocation.triangleCodesQ dataA.1.frame).1=(triangleCodesQ dataR.1.frame).1 ∧ (Allocation.triangleCodesQ dataA.1.frame).2≤(triangleCodesQ dataR.1.frame).2
    rw [h_data.1]
    exact ⟨allocation_triangleCodesQ_value dataR.1.frame, allocation_triangleCodesQ_le dataR.1.frame⟩
  let initialA := Allocation.seedRowsQ
  let initialR := seedRowsQ
  have h_initial : initialA.1=initialR.1 ∧ initialA.2≤ initialR.2 := by
    change (Allocation.seedRowsQ).1=(seedRowsQ).1 ∧ (Allocation.seedRowsQ).2≤(seedRowsQ).2
    exact ⟨allocation_seedRowsQ_value, allocation_seedRowsQ_le⟩
  constructor
  · change (⟨dataA.1,trianglesA.1,initialA.1⟩ : SetupOutput)=⟨dataR.1,trianglesR.1,initialR.1⟩
    simpa only [h_data.1, h_triangles.1, h_initial.1]
  · change dataA.2+trianglesA.2+initialA.2+1≤dataR.2+trianglesR.2+initialR.2+5
    have hc0 := h_data.2
    have hc1 := h_triangles.2
    have hc2 := h_initial.2
    omega
theorem allocation_setupQ_value (S : OddScale) (n : ℕ) :
    (Allocation.setupQ S n).1=(setupQ S n).1 := by
  exact (native_setupQ_simulation S n).1
attribute [local simp] allocation_setupQ_value
def allocatedRecords (S : OddScale) (n : ℕ) : ℕ := (Allocation.setupQ S n).2
def runtimeOpcodes : List String :=
  ["mapQ",
    "filterQ",
    "rangeQ",
    "appendQ",
    "flattenQ",
    "productQ",
    "equalCodeQ",
    "handleQ",
    "xqFaceTestQ",
    "qzFaceTestQ",
    "anyQ",
    "xqQ",
    "qzQ",
    "seedFrameQ",
    "flatMapQ",
    "collectQ",
    "emitQ",
    "singletonQ",
    "loopQ",
    "mapCodesQ",
    "facesAtXQ",
    "starQsQ",
    "starZsQ",
    "starSidesQ",
    "subVerticesQ",
    "subEdgesQ",
    "subFacesQ",
    "doubleVerticesQ",
    "doubleEdgesQ",
    "doubleFacesQ",
    "qNeighborsQ",
    "qDoubleVerticesQ",
    "qDoubleEdgesQ",
    "rxXCodesQ",
    "rxQCodesQ",
    "rxZCodesQ",
    "faceAtQ",
    "gridVertexQ",
    "horizontalEdgeQ",
    "verticalEdgeQ",
    "segmentVertexQ",
    "doubleEdgeVertexQ",
    "qDoubleEdgeVertexQ",
    "qEdgeImageQ",
    "bridgeOfVertexQ",
    "rxLocalFaceCodesQ",
    "rxGlueFaceCodesQ",
    "rxOldFaceCodesQ",
    "rxFaceCodesQ",
    "localFaceEndpointsQ",
    "glueFaceEndpointsQ",
    "oldFaceEndpointsQ",
    "faceEndpointsQ",
    "indexFaceQ",
    "packFrameQ",
    "memCodeQ",
    "dedupQ",
    "rxFrameQ",
    "transposeFrameQ",
    "rzFrameQ",
    "nextFrameQ",
    "lastFrameQ",
    "historyQ",
    "generateQ",
    "denseXQQ",
    "denseQZQ",
    "vertexCodesQ",
    "edgeCodesQ",
    "edgeVertexTestQ",
    "faceEdgeTestQ",
    "cellularBoundary1Q",
    "cellularBoundary2Q",
    "runQ",
    "seedRowsQ",
    "triangleCodesQ",
    "setupQ"]
def codeWords (c : Code) : List ℕ :=
  [c.family,c.owner,c.copy,c.part,c.p,c.q,c.i,c.j,c.k,c.l]
def faceWords (f : FaceRow) : List ℕ := codeWords f.code++[f.x,f.z,f.q0,f.q1]
def recordSlotReserve : ℕ := 4*((faceWords ⟨{},0,0,0,0⟩).length+2)
def controlSlotsPerStage : ℕ := runtimeOpcodes.length
def peakSlotEnvelope (S : OddScale) (n : ℕ) : ℕ :=
  prefixRecords S n+outputRecords (setupQ S n).1+recordSlotReserve*allocatedRecords S n+controlSlotsPerStage*(n+1)
end QEC.Coding.BDL26NativePresentationGenerator


