-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T19:03:10.715316+00:00
-- url     : https://prove2.me/theorems/77e86b3f-e4c4-4dce-960c-a885e487c515
-- title:
--   Paired Decoder Channel
-- statement:
--   Definitions and structural lemmas for Paired Decoder Channel, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderChannel.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_Xbar_Zbar_anticommute
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_Xbar_adjoint
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_Xbar_square
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_Zbar_adjoint
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_Zbar_square
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_logicalZ_normalizer
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_logicalZ_phase
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_logicalZ_xPart
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_logicalZ_zPart
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
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_finiteH1Equiv_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_generator_value
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_prefixCocycle_value
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_prefixCocycle_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_atom_adjoint
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_atom_mul_of_ne
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_atom_square
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_dressed_adjoint
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_dressed_binaryOne
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_dressed_mul_atom
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_dressed_square
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_normalizer_commute_atom
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_phaseOperator_adjoint
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_phaseOperator_binaryOne
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_phaseOperator_square
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_sum_atom
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
import Theorems.Thm_QEC_Coding_BDL26SectorTranslation_translation_x
import Theorems.Thm_QEC_Coding_BDL26SectorTranslation_translation_y
import Theorems.Thm_QEC_Coding_BDL26SectorTranslation_translation_z
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
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rxDualFace_left_inverse
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rxDualFace_right_inverse
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rzDualFace_left_inverse
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rzDualFace_right_inverse
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_transpose_transpose
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_dualBaseDecode_zero
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_dualBaseLocal_zero
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_pairedCorrection_phase
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
import Theorems.Thm_QEC_Coding_CSSGibbs_jointTranslation_apply
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
import Theorems.Thm_QEC_Coding_PauliSymplectic_adjoint_toHermitianQubitOperator_eq_self
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_square
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionLength_sym2_mk
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_diag_not_mem_fixedGeneratorInteractions
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_commutationPhase_square
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_dressedX_adjoint
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_dressedX_square
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_dressedZ_adjoint
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_dressedZ_square
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_goodSyndromeProjector_adjoint
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_goodSyndromeProjector_mul_self
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_phaseOperator_adjoint
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_phaseOperator_square
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_phase_mul_self
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_star_phase
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_toHermitianQubitOperator_mul_eq_commutationPhase_smul
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorOperator_adjoint_eq_self
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorSupport_eq_support
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_syndromeProjector_adjoint
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_syndromeProjector_mul_self
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
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_blockLength_eq_card
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_incidence_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_mem_variableSupport_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheck_globalOperator_eq_extendLocalToRegister
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
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_apply
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
attribute [local simp] QEC.Coding.BDL26BareLogicalPair.Xbar_adjoint
attribute [local simp] QEC.Coding.BDL26BareLogicalPair.Xbar_square
attribute [local simp] QEC.Coding.BDL26BareLogicalPair.Zbar_adjoint
attribute [local simp] QEC.Coding.BDL26BareLogicalPair.Zbar_square
attribute [local simp] QEC.Coding.BDL26BareLogicalPair.logicalZ_phase
attribute [local simp] QEC.Coding.BDL26BareLogicalPair.logicalZ_xPart
attribute [local simp] QEC.Coding.BDL26BareLogicalPair.logicalZ_zPart
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
attribute [local simp] QEC.Coding.BDL26FiniteCohomology.finiteH1Equiv_zero
attribute [local simp] QEC.Coding.BDL26FiniteCohomology.generator_value
attribute [local simp] QEC.Coding.BDL26FiniteCohomology.prefixCocycle_value
attribute [local simp] QEC.Coding.BDL26FiniteCohomology.prefixCocycle_zero
attribute [local simp] QEC.Coding.BDL26FiniteTannerSquare.doubleCylinderEndInclusion_apply
attribute [local simp] QEC.Coding.BDL26PairedDecoderPhase.atom_adjoint
attribute [local simp] QEC.Coding.BDL26PairedDecoderPhase.atom_square
attribute [local simp] QEC.Coding.BDL26PairedDecoderPhase.dressed_adjoint
attribute [local simp] QEC.Coding.BDL26PairedDecoderPhase.dressed_binaryOne
attribute [local simp] QEC.Coding.BDL26PairedDecoderPhase.dressed_square
attribute [local simp] QEC.Coding.BDL26PairedDecoderPhase.phaseOperator_adjoint
attribute [local simp] QEC.Coding.BDL26PairedDecoderPhase.phaseOperator_binaryOne
attribute [local simp] QEC.Coding.BDL26PairedDecoderPhase.phaseOperator_square
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
attribute [local simp] QEC.Coding.BDL26SectorTranslation.translation_x
attribute [local simp] QEC.Coding.BDL26SectorTranslation.translation_y
attribute [local simp] QEC.Coding.BDL26SectorTranslation.translation_z
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
attribute [local simp] QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rxDualFace_left_inverse
attribute [local simp] QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rxDualFace_right_inverse
attribute [local simp] QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rzDualFace_left_inverse
attribute [local simp] QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rzDualFace_right_inverse
attribute [local simp] QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.transpose_transpose
attribute [local simp] QEC.Coding.BDL26TransposedStoppedDecoder.dualBaseDecode_zero
attribute [local simp] QEC.Coding.BDL26TransposedStoppedDecoder.dualBaseLocal_zero
attribute [local simp] QEC.Coding.BDL26TransposedStoppedDecoder.pairedCorrection_phase
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
attribute [local simp] QEC.Coding.CSSGibbs.jointTranslation_apply
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
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.interactionLength_sym2_mk
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_diag_not_mem_fixedGeneratorInteractions
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.DecoderDressedLogical.commutationPhase_square
attribute [local simp] QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedX_adjoint
attribute [local simp] QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedX_square
attribute [local simp] QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedZ_adjoint
attribute [local simp] QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedZ_square
attribute [local simp] QEC.Coding.StabilizerCode.DecoderDressedLogical.goodSyndromeProjector_adjoint
attribute [local simp] QEC.Coding.StabilizerCode.DecoderDressedLogical.goodSyndromeProjector_mul_self
attribute [local simp] QEC.Coding.StabilizerCode.DecoderDressedLogical.phaseOperator_adjoint
attribute [local simp] QEC.Coding.StabilizerCode.DecoderDressedLogical.phaseOperator_square
attribute [local simp] QEC.Coding.StabilizerCode.DecoderDressedLogical.phase_mul_self
attribute [local simp] QEC.Coding.StabilizerCode.DecoderDressedLogical.star_phase
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorOperator_adjoint_eq_self
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorSupport_eq_support
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.syndromeProjector_adjoint
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.syndromeProjector_mul_self
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
attribute [local simp] QEC.QLDPC.FiniteQuditCheck.globalOperator_eq_extendLocalToRegister
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.blockLength_eq_card
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.incidence_iff_mem_region
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.mem_variableSupport_iff_mem_region
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
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.log2Matrix_apply
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.logMatrix_apply
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
namespace QEC.Coding.BDL26PairedDecoderChannel
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase
open StabilizerCode.DecoderDressedLogical
open scoped BigOperators TensorProduct
abbrev Register (S : OddScale) (n : Nat) := Qubit.QubitRegister (Physical S (n+2))
abbrev Op (S : OddScale) (n : Nat) := Operator (Register S n)
variable (S : OddScale) (n : Nat)
local instance _p2m_local_instance_c895a38b5b_28 : Fintype (BDL26TransposedStoppedDecoder.XSyndromeDomain S n) := Fintype.ofFinite _
local instance _p2m_local_instance_c895a38b5b_29 : Fintype (BDL26TransposedStoppedDecoder.ZSyndromeDomain S n) := Fintype.ofFinite _
def correctionOperator (s : Visible S n) : Op S n :=
  toHermitianQubitOperator (correction S n s)
@[simp] theorem correction_adjoint (s : Visible S n) :
    LinearMap.adjoint (correctionOperator S n s) = correctionOperator S n s :=
  adjoint_toHermitianQubitOperator_eq_self _
@[simp] theorem correction_square (s : Visible S n) :
    correctionOperator S n s * correctionOperator S n s = 1 :=
  toHermitianQubitOperator_square _
def kraus : FiniteKrausFamily (Visible S n) (Register S n) (Register S n) where
  operator s := correctionOperator S n s * atom S n s
@[simp] theorem kraus_operator (s : Visible S n) :
    (kraus S n).operator s = correctionOperator S n s * atom S n s := rfl
@[simp] theorem kraus_adjoint (s : Visible S n) :
    LinearMap.adjoint ((kraus S n).operator s) = atom S n s * correctionOperator S n s := by
  rw [kraus_operator]
  change LinearMap.adjoint ((correctionOperator S n s).comp (atom S n s)) =
    (atom S n s).comp (correctionOperator S n s)
  rw [LinearMap.adjoint_comp, atom_adjoint S n s, correction_adjoint S n s]
theorem kraus_complete : (kraus S n).Complete := by
  change (∑ s : Visible S n,
    LinearMap.adjoint ((kraus S n).operator s) * (kraus S n).operator s) = 1
  calc
    _ = ∑ s : Visible S n, atom S n s := by
      apply Finset.sum_congr rfl
      intro s _
      rw [kraus_adjoint, kraus_operator]
      calc
        _ = atom S n s *
            (correctionOperator S n s * correctionOperator S n s) * atom S n s := by
          simp only [mul_assoc]
        _ = atom S n s := by rw [correction_square, mul_one, atom_square]
    _ = 1 := sum_atom S n
def channel : QuantumChannel (Register S n) (Register S n) :=
  (kraus S n).toQuantumChannel (kraus_complete S n)
def heisenberg : Op S n →ₗ[ℂ] Op S n where
  toFun O := ∑ s : Visible S n,
    atom S n s * correctionOperator S n s * O * correctionOperator S n s * atom S n s
  map_add' A B := by simp [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c A := by simp [mul_smul_comm, smul_mul_assoc, Finset.smul_sum]
theorem heisenberg_apply (O : Op S n) :
    heisenberg S n O = ∑ s : Visible S n,
      atom S n s * correctionOperator S n s * O * correctionOperator S n s * atom S n s := rfl
@[simp] theorem heisenberg_one : heisenberg S n 1 = 1 := by
  rw [heisenberg_apply]
  have h (s : Visible S n) : atom S n s * correctionOperator S n s * 1 *
      correctionOperator S n s * atom S n s = atom S n s := by
    simp only [mul_one]
    calc
      _ = atom S n s * (correctionOperator S n s * correctionOperator S n s) * atom S n s := by
        noncomm_ring
      _ = atom S n s := by rw [correction_square, mul_one, atom_square]
  simp_rw [h]
  exact sum_atom S n
@[simp] theorem heisenberg_adjoint (O : Op S n) :
    heisenberg S n (LinearMap.adjoint O) = LinearMap.adjoint (heisenberg S n O) := by
  simp only [heisenberg_apply, map_sum, Module.End.mul_eq_comp, LinearMap.adjoint_comp,
    atom_adjoint, correction_adjoint]
  simp only [LinearMap.comp_assoc]
def rawBranch (w : Word (ZMod 2) (Sum (ZLabel S (n+2)) (XLabel S (n+2))))
    (A : Op S n) : Op S n :=
  ∑ s : Visible S n,
    if CSSGibbs.realizableEmbedding (zSyndrome S (n+2)) (xSyndrome S (n+2)) s = w then
      correctionOperator S n s * atom S n s * A * atom S n s * correctionOperator S n s
    else 0
theorem correction_conjugates (s : Visible S n) (L : Binary (Physical S (n+2))) :
    correctionOperator S n s * toHermitianQubitOperator L * correctionOperator S n s =
      StabilizerCode.DecoderDressedLogical.commutationPhase (correction S n s) L •
        toHermitianQubitOperator L := by
  unfold correctionOperator
  rw [toHermitianQubitOperator_mul_eq_commutationPhase_smul]
  rw [smul_mul_assoc, mul_assoc, toHermitianQubitOperator_square, mul_one]
theorem heisenberg_mul_normalizers (L M : Binary (Physical S (n+2)))
    (hL : (code S n).InBinaryNormalizer L) (hM : (code S n).InBinaryNormalizer M) :
    heisenberg S n (toHermitianQubitOperator L * toHermitianQubitOperator M) =
      dressed S n L * dressed S n M := by
  have hsector (s : Visible S n) :
      heisenberg S n (toHermitianQubitOperator L * toHermitianQubitOperator M) * atom S n s =
        (dressed S n L * dressed S n M) * atom S n s := by
    rw [heisenberg_apply, Finset.sum_mul, Finset.sum_eq_single s]
    · have hcL := normalizer_commute_atom S n L hL s
      have hcM := normalizer_commute_atom S n M hM s
      have hcLM := hcL.mul_left hcM
      have hprod : correctionOperator S n s *
          (toHermitianQubitOperator L * toHermitianQubitOperator M) * correctionOperator S n s =
          (correctionOperator S n s * toHermitianQubitOperator L * correctionOperator S n s) *
          (correctionOperator S n s * toHermitianQubitOperator M * correctionOperator S n s) := by
        symm
        calc
          _ = correctionOperator S n s * toHermitianQubitOperator L *
              (correctionOperator S n s * correctionOperator S n s) *
              toHermitianQubitOperator M * correctionOperator S n s := by noncomm_ring
          _ = _ := by rw [correction_square]; simp [mul_assoc]
      calc
        _ = atom S n s *
            (correctionOperator S n s *
              (toHermitianQubitOperator L * toHermitianQubitOperator M) *
              correctionOperator S n s) * atom S n s := by
          simp only [mul_assoc, atom_square]
        _ = (commutationPhase (correction S n s) L * commutationPhase (correction S n s) M) •
            ((toHermitianQubitOperator L * toHermitianQubitOperator M) * atom S n s) := by
          rw [hprod, correction_conjugates, correction_conjugates, smul_mul_smul_comm,
            mul_smul_comm, smul_mul_assoc, ← hcLM.eq, mul_assoc, atom_square]
        _ = _ := by
          symm
          rw [mul_assoc, dressed_mul_atom, mul_smul_comm, hcM.eq, ← mul_assoc,
            dressed_mul_atom, smul_mul_assoc, smul_smul]
          rw [mul_comm (commutationPhase (correction S n s) M)
            (commutationPhase (correction S n s) L)]
          exact congrArg
            (fun T : Op S n =>
              (commutationPhase (correction S n s) L * commutationPhase (correction S n s) M) • T)
            ((mul_assoc (toHermitianQubitOperator L) (atom S n s) (toHermitianQubitOperator M)).trans
              ((congrArg (fun T : Op S n => toHermitianQubitOperator L * T) hcM.eq.symm).trans
                (mul_assoc (toHermitianQubitOperator L) (toHermitianQubitOperator M) (atom S n s)).symm))
    · intro t _ hts
      simp only [mul_assoc]
      rw [atom_mul_of_ne S n t s hts]
      simp
    · simp
  calc
    _ = heisenberg S n (toHermitianQubitOperator L * toHermitianQubitOperator M) *
        (∑ s : Visible S n, atom S n s) := by rw [sum_atom, mul_one]
    _ = (dressed S n L * dressed S n M) * (∑ s : Visible S n, atom S n s) := by
      simp_rw [Finset.mul_sum, hsector]
    _ = _ := by rw [sum_atom, mul_one]
abbrev bareX : Op S n := BDL26BareLogicalPair.Xbar S (n+2)
abbrev bareZ : Op S n := BDL26BareLogicalPair.Zbar S (n+2)
def bareY : Op S n := Complex.I • (bareX S n * bareZ S n)
abbrev dressedX : Op S n := dressed S n (BDL26BareLogicalPair.logicalX S (n+2))
abbrev dressedZ : Op S n := dressed S n (BDL26BareLogicalPair.logicalZ S (n+2))
def dressedY : Op S n := Complex.I • (dressedX S n * dressedZ S n)
theorem dressed_anticommute : dressedX S n * dressedZ S n = -(dressedZ S n * dressedX S n) := by
  rw [← heisenberg_mul_normalizers S n _ _
    (BDL26BareLogicalPair.logicalX_normalizer S (n+2))
    (BDL26BareLogicalPair.logicalZ_normalizer S (n+2)),
    BDL26BareLogicalPair.Xbar_Zbar_anticommute, map_neg,
    heisenberg_mul_normalizers S n _ _
      (BDL26BareLogicalPair.logicalZ_normalizer S (n+2))
      (BDL26BareLogicalPair.logicalX_normalizer S (n+2))]
def barePauliPair : ThermalEncoding.PauliLikePair (Register S n) where
  x := bareX S n
  z := bareZ S n
  x_symmetric := by
    rw [LinearMap.isSymmetric_iff_isSelfAdjoint, LinearMap.isSelfAdjoint_iff']
    exact BDL26BareLogicalPair.Xbar_adjoint S (n+2)
  z_symmetric := by
    rw [LinearMap.isSymmetric_iff_isSelfAdjoint, LinearMap.isSelfAdjoint_iff']
    exact BDL26BareLogicalPair.Zbar_adjoint S (n+2)
  x_sq := BDL26BareLogicalPair.Xbar_square S (n+2)
  z_sq := BDL26BareLogicalPair.Zbar_square S (n+2)
  anticommute := BDL26BareLogicalPair.Xbar_Zbar_anticommute S (n+2)
def dressedPauliPair : ThermalEncoding.PauliLikePair (Register S n) where
  x := dressedX S n
  z := dressedZ S n
  x_symmetric := by
    rw [LinearMap.isSymmetric_iff_isSelfAdjoint, LinearMap.isSelfAdjoint_iff']
    exact dressed_adjoint S n _ (BDL26BareLogicalPair.logicalX_normalizer S (n+2))
  z_symmetric := by
    rw [LinearMap.isSymmetric_iff_isSelfAdjoint, LinearMap.isSelfAdjoint_iff']
    exact dressed_adjoint S n _ (BDL26BareLogicalPair.logicalZ_normalizer S (n+2))
  x_sq := dressed_square S n _ (BDL26BareLogicalPair.logicalX_normalizer S (n+2))
  z_sq := dressed_square S n _ (BDL26BareLogicalPair.logicalZ_normalizer S (n+2))
  anticommute := dressed_anticommute S n
def readout : QuantumChannel (Register S n) Qubit.QubitSpace :=
  QuantumChannel.comp (barePauliPair S n).thermalDecoding (channel S n)
def pairEmbedding {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteQuantumSystem H]
    (P : ThermalEncoding.PauliLikePair H) : Operator Qubit.QubitSpace →ₗ[ℂ] Operator H where
  toFun O := P.factorization.conjOperator (TensorProduct.map O (1 : Operator P.AuxiliarySpace))
  map_add' A B := by
    rw [TensorProduct.map_add_left]
    exact P.factorization.conjOperatorLinearMap.map_add _ _
  map_smul' c A := by
    rw [TensorProduct.map_smul_left]
    exact P.factorization.conjOperatorLinearMap.map_smul _ _
end QEC.Coding.BDL26PairedDecoderChannel
end


