-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_OldXAllOddPrefixSeed_QECert
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_OldXAllOddPrefixSeed_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T23:05:50.97547+00:00
-- url     : https://prove2.me/theorems/3ac23529-523a-42f7-919c-44087b7490ef
-- title:
--   All-odd OldX prefix seed
-- statement:
--   Exact prefix support lemmas for the all-odd OldX dual-readout proof.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L18360-L18373

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_OldXAllOddCoreFirstCutStripOrder_QECert
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_OldXAllOddCoreFirstCutPortEnd_QECert
import Theorems.Thm_QEC_Coding_BDL26RXPrimitiveC2QEndpoint_global_interior_zero_before_last
attribute [local simp] QEC.Coding.BDL26BareLogicalPair.Xbar_adjoint
attribute [local simp] QEC.Coding.BDL26BareLogicalPair.Xbar_square
attribute [local simp] QEC.Coding.BDL26BareLogicalPair.Zbar_adjoint
attribute [local simp] QEC.Coding.BDL26BareLogicalPair.Zbar_square
attribute [local simp] QEC.Coding.BDL26BareLogicalPair.logicalZ_phase
attribute [local simp] QEC.Coding.BDL26BareLogicalPair.logicalZ_xPart
attribute [local simp] QEC.Coding.BDL26BareLogicalPair.logicalZ_zPart
attribute [local simp] QEC.Coding.BDL26BoundedRateDavies.oppositeFrequency_opposite
attribute [local simp] QEC.Coding.BDL26BoundedRateDavies.oppositeFrequency_val
attribute [local simp] QEC.Coding.BDL26CSSDaviesLocality.coupling_x
attribute [local simp] QEC.Coding.BDL26CSSDaviesLocality.coupling_y
attribute [local simp] QEC.Coding.BDL26CSSDaviesLocality.coupling_z
attribute [local simp] QEC.Coding.BDL26CSSHamiltonian.check_hermitian
attribute [local simp] QEC.Coding.BDL26CSSHamiltonian.mem_x_checkSupport
attribute [local simp] QEC.Coding.BDL26CSSHamiltonian.mem_z_checkSupport
attribute [local simp] QEC.Coding.BDL26CanonicalHistoryMarks.physicalMarks_base
attribute [local simp] QEC.Coding.BDL26CanonicalHistoryMarks.physicalMarks_step
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
attribute [local simp] QEC.Coding.BDL26LevelTwoOldXStarEndpoint.localLift_other
attribute [local simp] QEC.Coding.BDL26LevelTwoOldXStarEndpoint.localLift_same
attribute [local simp] QEC.Coding.BDL26LevelTwoOldXStarEndpoint.mem_neighborhood_edge
attribute [local simp] QEC.Coding.BDL26LevelTwoOldXStarEndpoint.mem_neighborhood_q
attribute [local simp] QEC.Coding.BDL26LevelTwoOldXStarEndpoint.oldXLift_parity
attribute [local simp] QEC.Coding.BDL26LevelTwoOldXStarEndpoint.outsideMask_read
attribute [local simp] QEC.Coding.BDL26PairedDecoderChannel.dressedY_adjoint
attribute [local simp] QEC.Coding.BDL26PairedDecoderChannel.heisenberg_X
attribute [local simp] QEC.Coding.BDL26PairedDecoderChannel.heisenberg_Y
attribute [local simp] QEC.Coding.BDL26PairedDecoderChannel.heisenberg_Z
attribute [local simp] QEC.Coding.BDL26PairedDecoderChannel.readout_trace_I
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
attribute [local simp] QEC.Coding.BDL26TopOwnerIsolation.markedAdjacent_iff
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


section
noncomputable section
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26CSSHamiltonian BDL26ActualFailureReadout BDL26LevelTwoCode
open BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder BDL26RXPhysicalCoordinateTrace
open scoped Classical BigOperators
attribute [local instance] QEC.Coding.BDL26RXPrimitiveC2QEndpoint.rawOneXEncodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.rawOneQEncodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.rawOneZEncodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.executableTransposeFaceEncodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.executableTransposeEdgeEncodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.baseZeroX QEC.Coding.BDL26RXPrimitiveC2QEndpoint.rawRX0Encodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.rawRX1Encodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.baseXEncodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.baseQEncodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.baseZEncodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.baseFaceEncodable
attribute [local simp] basis_value
attribute [local simp] word_add_eval word_smul_eval word_zero_eval
private theorem global_same_owner_direct_zero (S : OddScale) (a : Word F (RawTwo S).Q)
    (r : (RawOne S).Q) (z : (RawOne S).Z) (hz : (RawOne S).qz r z=true)
    (hu : ∀ z', (RawOne S).qz r z'=true → z'=z)
    (x x' : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (hx' : (RawOne S).xq x' r=true) (c : BDL26FiniteTannerSquare.Two)
    (depth : Option (Fin (S.half-1))) (K : Nat) (hK : 0<K)
    (hr : K≤Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
    (hR : Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)≤K^2)
    (hX : Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤K^2)
    (hi : ∀ i, depth=some i → i.val<K^2)
    (horder : Encodable.encode (executableCoordinate S
      (.inr ⟨r,chosenPort (RawOne S) S r x hx c depth⟩))<
        Encodable.encode (executableCoordinate S
          (.inr ⟨r,chosenPort (RawOne S) S r x' hx' c depth⟩))) :
    BDL26GlobalLookupLinearity.actualGlobal S (tannerCoboundary1 (RawTwo S) a)
      (.inr ⟨r,chosenPort (RawOne S) S r x hx c depth⟩)=0 := by
  obtain ⟨p,hp⟩ := exists_direct_path_later_OldXCore_QECert S r r x x hx hx z hz c depth
    K hK hr hR hX hi
  obtain ⟨p',hp'⟩ := exists_direct_path_later_OldXCore_QECert S r r x x' hx hx' z hz c depth
    K hK hr hR hX hi
  exact global_zero_of_same_owner_pair_OldXCore_QECert S a r z hz hu _ _
    (zCenter (RawOne S) S z c) p p' horder hp hp'
theorem global_radial_minor_endpoint_zero_OldXBounded_QECert (S : OddScale)
    (a : Word F (RawTwo S).Q) (j : Fin 2) (n : Fin S.half)
    (hn : 0<j.val+n.val) (x : (RawOne S).X)
    (hx : (RawOne S).xq x (gammaRadial S j n)=true)
    (hne : x≠oldLargestX S (gammaRadial S j n))
    (c : BDL26FiniteTannerSquare.Two) :
    BDL26GlobalLookupLinearity.actualGlobal S (tannerCoboundary1 (RawTwo S) a)
      (.inr ⟨gammaRadial S j n,(c,.inl (.inr ⟨x,hx⟩))⟩)=0 := by
  let r := gammaRadial S j n
  let K := Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)
  have hK : 0<K := gamma_code_pos_OldXCore_QECert S j n hn
  have hxle : Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (oldLargestX S r :
        (BDL26LevelTwoDecoder.executableLevelOne S).X) :=
    oldLargestX_upper_OldXCore_QECert S 0 (.inl (0,.inl (seedRadial j,n))) x hx
  have hstrict : Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)<
      Encodable.encode (oldLargestX S r :
        (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
    have hncode : Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)≠
        Encodable.encode (oldLargestX S r :
          (BDL26LevelTwoDecoder.executableLevelOne S).X) :=
      fun he => hne (Encodable.encode_injective he)
    omega
  have hX : Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤K^2 :=
    hxle.trans (gammaLargestX_le_square_OldXCore_QECert S j n hn)
  have hR : K≤K^2 := Nat.le_self_pow (by decide) K
  have hi : ∀ i : Fin (S.half-1), (none : Option (Fin (S.half-1)))=some i → i.val<K^2 := by
    intro i he
    cases he
  have hz : (RawOne S).qz r (seedRadialCheck S j n)=true :=
    (seedRadial_degree_one S j n).1
  exact global_same_owner_direct_zero S a r (seedRadialCheck S j n) hz
    (seedRadial_degree_one S j n).2 x (oldLargestX S r) hx
    (oldLargestX_incident S r) c none K hK le_rfl hR hX hi
    (chosenPort_order_same_owner_OldXCore_QECert S r x (oldLargestX S r) hx
      (oldLargestX_incident S r) c none hstrict)
theorem global_first_radial_last_interior_zero_OldXBounded_QECert (S : OddScale) (hh : 2≤S.half)
    (a : Word F (RawTwo S).Q) (x : (RawOne S).X)
    (hx : (RawOne S).xq x (firstRadialQ S)=true)
    (c : BDL26FiniteTannerSquare.Two) :
    BDL26GlobalLookupLinearity.actualGlobal S (tannerCoboundary1 (RawTwo S) a)
      (.inr ⟨firstRadialQ S,(c,.inr (⟨x,hx⟩,lastInterior S hh))⟩)=0 := by
  apply global_last_interior_of_least_old_neighbor_OldXCore_QECert S hh a (firstRadialQ S) x hx c
  intro r' _ hn
  have hz : Encodable.encode
      (firstRadialQ S : (BDL26LevelTwoDecoder.executableLevelOne S).Q)=0 := by rfl
  have hne : Encodable.encode
      (r' : (BDL26LevelTwoDecoder.executableLevelOne S).Q)≠0 := by
    intro he
    exact hn (Encodable.encode_injective (he.trans hz.symm))
  omega
private theorem radialInterior_grid_eq (S : OddScale) (j : Fin 2)
    (i : Fin (S.half-1)) (f : XStarFace baseTannerSquarePresentation (0 : BaseX))
    (a b : Fin (S.half+1))
    (h : subdivisionGridVertex baseTannerSquarePresentation 0 S f a b=
      .inr (.inl (seedRadial j,i))) :
    f=seedFace j ∧ a.val=i.val+1 ∧ b.val=0 := by
  rcases subdivisionGridVertex_eq_edgeInterior_coordinates
    baseTannerSquarePresentation 0 S f a b (seedRadial j) i h with h | h | h | h
  · exact False.elim (seedRadial_face_one j f h.1)
  · exact False.elim (seedRadial_ne_qz j f 0 h.1)
  · exact ⟨(seedRadial_face_zero j f).mp h.1,h.2.1,h.2.2⟩
  · exact False.elim (seedRadial_ne_qz j f 1 h.1)
private theorem radialInterior_subdivision_edges (S : OddScale) (j : Fin 2)
    (i : Fin (S.half-1)) (e : SubdivisionEdge baseTannerSquarePresentation (0 : BaseX) S)
    (h : subdivisionEdgeStart baseTannerSquarePresentation 0 S e=.inr (.inl (seedRadial j,i)) ∨
      subdivisionEdgeEnd baseTannerSquarePresentation 0 S e=.inr (.inl (seedRadial j,i))) :
    e=.inl (seedRadial j,radialPrevious S i) ∨
      e=.inl (seedRadial j,radialFollowing S i) ∨
      e=.inr (.inr (seedFace j,i,⟨0,S.half_pos⟩)) := by
  rcases subdivision_edge_grid_cover_OldXCore_QECert baseTannerSquarePresentation
    baseTannerSquareAdmissibleV4 0 S e with hh | hv
  · obtain ⟨f,k,row,rfl⟩ := hh
    rcases h with hs | ht
    · erw [own_horizontal_start] at hs
      obtain ⟨hf,hk,hr⟩ := radialInterior_grid_eq S j i f _ _ hs
      subst f
      have hrow : row=0 := Fin.ext hr
      have hseg : k=radialFollowing S i := Fin.ext hk
      subst row
      subst k
      right
      left
      simp only [subdivisionHorizontalEdge,dif_pos (by rfl :
        (0 : Fin (S.half+1)).val=0)]
      exact congrArg (fun a : XStarEdge baseTannerSquarePresentation (0 : BaseX) =>
        (Sum.inl (a,radialFollowing S i) : SubdivisionEdge baseTannerSquarePresentation 0 S))
        ((seedRadial_face_zero j (seedFace j)).mpr rfl).symm
    · erw [own_horizontal_end] at ht
      obtain ⟨hf,hk,hr⟩ := radialInterior_grid_eq S j i f _ _ ht
      subst f
      have hrow : row=0 := Fin.ext hr
      have hseg : k=radialPrevious S i := by
        apply Fin.ext
        change k.val=i.val
        change k.val+1=i.val+1 at hk
        omega
      subst row
      subst k
      left
      simp only [subdivisionHorizontalEdge,dif_pos (by rfl :
        (0 : Fin (S.half+1)).val=0)]
      exact congrArg (fun a : XStarEdge baseTannerSquarePresentation (0 : BaseX) =>
        (Sum.inl (a,radialPrevious S i) : SubdivisionEdge baseTannerSquarePresentation 0 S))
        ((seedRadial_face_zero j (seedFace j)).mpr rfl).symm
  · obtain ⟨f,column,k,rfl⟩ := hv
    rcases h with hs | ht
    · erw [own_vertical_start] at hs
      obtain ⟨hf,hc,hk⟩ := radialInterior_grid_eq S j i f _ _ hs
      subst f
      have hcolumn : column=finInteriorGrid S i := Fin.ext hc
      have hseg : k=⟨0,S.half_pos⟩ := Fin.ext hk
      subst column
      subst k
      right
      right
      have hi0 : (finInteriorGrid S i).val≠0 := by simp [finInteriorGrid]
      have hih : (finInteriorGrid S i).val≠S.half := by have := i.isLt; dsimp [finInteriorGrid]; omega
      have hn : i.val+1≠S.half := by have := i.isLt; omega
      erw [vertical_inner_eq_OldXCore_QECert baseTannerSquarePresentation (0 : BaseX) S
        (seedFace j) (finInteriorGrid S i) ⟨0,S.half_pos⟩ hi0 hih]
      apply congrArg (fun k : Fin (S.half-1) =>
        (Sum.inr (Sum.inr (seedFace j,k,⟨0,S.half_pos⟩)) :
          SubdivisionEdge baseTannerSquarePresentation (0 : BaseX) S))
      apply Fin.ext
      change (i.val+1)-1=i.val
      omega
    · erw [own_vertical_end] at ht
      obtain ⟨_,_,hk⟩ := radialInterior_grid_eq S j i f _ _ ht
      change k.val+1=0 at hk
      omega
private theorem raisedBoundaryL0_support (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (hh : 2≤S.half) (f : XStarFace P x)
    (e : SubdivisionEdge P x S) (he : pathChain (raisedBoundaryL0 P x S f) e≠0) :
    raisedBoundarySupport P x S hh e := by
  change (pathChain
    (verticalAtColumnPath P x S f (lastGridInterior S) S.half le_rfl) e+
      (Pi.single (subdivisionHorizontalEdge P x S f (lastSegment S)
        (gridAt S S.half le_rfl)) (1:F) : Word F (SubdivisionEdge P x S)) e)≠0 at he
  by_cases hp : pathChain
      (verticalAtColumnPath P x S f (lastGridInterior S) S.half le_rfl) e=0
  · rw [hp,zero_add] at he
    have heq : e=subdivisionHorizontalEdge P x S f (lastSegment S)
        (gridAt S S.half le_rfl) := by
      by_contra hn
      exact he (by simp [hn,Ne.symm hn])
    right; right
    refine ⟨xStarFaceQZEdge P x f 1,?_⟩
    simpa [subdivisionHorizontalEdge,gridAt,S.half_pos.ne'] using heq
  · obtain ⟨k,_,hk⟩ := verticalAtColumnPath_support P x S f
      (lastGridInterior S) S.half le_rfl e hp
    left
    refine ⟨f,k,?_⟩
    have hc0 : (lastGridInterior S).val≠0 := by dsimp [lastGridInterior]; omega
    have hch : (lastGridInterior S).val≠S.half := by dsimp [lastGridInterior]; omega
    have hedge : subdivisionVerticalEdge P x S f (lastGridInterior S) k=
        (Sum.inr (Sum.inr (f,lastInterior S hh,k)) :
          SubdivisionEdge P x S) := by
      simp only [subdivisionVerticalEdge,dif_neg hc0,dif_neg hch]
      apply congrArg (fun index : Fin (S.half-1) =>
        (Sum.inr (Sum.inr (f,index,k)) : SubdivisionEdge P x S))
      apply Fin.ext
      change (S.half-1)-1=S.half-2
      omega
    exact hk.trans hedge
private theorem raisedBoundaryL1_support (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (hh : 2≤S.half) (f : XStarFace P x)
    (e : SubdivisionEdge P x S) (he : pathChain (raisedBoundaryL1 P x S f) e≠0) :
    raisedBoundarySupport P x S hh e := by
  change (pathChain
    (horizontalAtRowPath P x S f (lastGridInterior S) S.half le_rfl) e+
      (Pi.single (subdivisionVerticalEdge P x S f (gridAt S S.half le_rfl)
        (lastSegment S)) (1:F) : Word F (SubdivisionEdge P x S)) e)≠0 at he
  by_cases hp : pathChain
      (horizontalAtRowPath P x S f (lastGridInterior S) S.half le_rfl) e=0
  · rw [hp,zero_add] at he
    have heq : e=subdivisionVerticalEdge P x S f (gridAt S S.half le_rfl)
        (lastSegment S) := by
      by_contra hn
      exact he (by simp [hn,Ne.symm hn])
    right; right
    refine ⟨xStarFaceQZEdge P x f 0,?_⟩
    simpa [subdivisionVerticalEdge,gridAt,S.half_pos.ne'] using heq
  · obtain ⟨k,_,hk⟩ := horizontalAtRowPath_support P x S f
      (lastGridInterior S) S.half le_rfl e hp
    right; left
    refine ⟨f,k,?_⟩
    have hc0 : (lastGridInterior S).val≠0 := by dsimp [lastGridInterior]; omega
    have hch : (lastGridInterior S).val≠S.half := by dsimp [lastGridInterior]; omega
    have hedge : subdivisionHorizontalEdge P x S f k (lastGridInterior S)=
        (Sum.inr (Sum.inl (f,k,lastInterior S hh)) :
          SubdivisionEdge P x S) := by
      simp only [subdivisionHorizontalEdge,dif_neg hc0,dif_neg hch]
      apply congrArg (fun index : Fin (S.half-1) =>
        (Sum.inr (Sum.inl (f,k,index)) : SubdivisionEdge P x S))
      apply Fin.ext
      change (S.half-1)-1=S.half-2
      omega
    exact hk.trans hedge
private theorem boundarySpokeEdge_face (P : TannerSquarePresentation) (x : P.X)
    (f : XStarFace P x) (j : BDL26FiniteTannerSquare.Two)
    (hm : xStarBoundaryVertexMember P x (.q (P.faceQ f.val j))=true) :
    boundarySpokeEdge P x (P.faceQ f.val j) hm=xStarFaceXQEdge P x f j := by
  apply Subtype.ext
  unfold boundarySpokeEdge xStarFaceXQEdge
  change (.inl ⟨(x,P.faceQ f.val j),_⟩ : Edge P)=.inl (faceXQEdge P f.val j)
  apply congrArg Sum.inl
  apply Subtype.ext
  have hfx : P.faceX f.val=x := by simpa [xStarFaceMember] using f.property
  exact Prod.ext hfx.symm rfl
private theorem raisedBoundary_face_start (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (hh : 2≤S.half)
    (f : XStarFace P x) (j : BDL26FiniteTannerSquare.Two) :
    raisedBoundaryVertex P x S hh (xBoundaryEdgeStart P x (faceBoundaryEdge P x f j))=
      if j=0 then subdivisionGridVertex P x S f (lastGridInterior S) 0
      else subdivisionGridVertex P x S f 0 (lastGridInterior S) := by
  change (Sum.inr (Sum.inl
    (boundarySpokeEdge P x (P.faceQ f.val j) _,lastInterior S hh)) : SubdivisionVertex P x S)=_
  erw [boundarySpokeEdge_face]
  have hi : (⟨(lastInterior S hh).val+1,by have := (lastInterior S hh).isLt; omega⟩ :
      Fin (S.half+1))=lastGridInterior S := by
    apply Fin.ext
    dsimp [lastInterior,lastGridInterior]
    omega
  fin_cases j
  · change (Sum.inr (Sum.inl (xStarFaceXQEdge P x f 0,lastInterior S hh)) :
      SubdivisionVertex P x S)=
      subdivisionGridVertex P x S f (lastGridInterior S) 0
    simpa only [hi] using
      (subdivisionGridVertex_edgeInterior_xq0 P x S f (lastInterior S hh)).symm
  · change (Sum.inr (Sum.inl (xStarFaceXQEdge P x f 1,lastInterior S hh)) :
      SubdivisionVertex P x S)=
      subdivisionGridVertex P x S f 0 (lastGridInterior S)
    simpa only [hi] using
      (subdivisionGridVertex_edgeInterior_xq1 P x S f (lastInterior S hh)).symm
private theorem raisedBoundary_face_end (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (hh : 2≤S.half)
    (f : XStarFace P x) (j : BDL26FiniteTannerSquare.Two) :
    raisedBoundaryVertex P x S hh (xBoundaryEdgeEnd P x (faceBoundaryEdge P x f j))=
      subdivisionGridVertex P x S f (gridAt S S.half le_rfl)
        (gridAt S S.half le_rfl) := by
  change (.inl ⟨.z (P.faceZ f.val),_⟩ : SubdivisionVertex P x S)=_
  simp only [subdivisionGridVertex,gridAt,S.half_pos.ne',↓reduceDIte]
  rfl
private theorem exists_raised_boundary_segment (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (x : P.X) (S : OddScale) (hh : 2≤S.half)
    (e : XStarBoundaryEdge P x) :
    ∃ p : UndirectedPath (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
      (raisedBoundaryVertex P x S hh (xBoundaryEdgeStart P x e))
      (raisedBoundaryVertex P x S hh (xBoundaryEdgeEnd P x e)),
      ∀ e', pathChain p e'≠0 → raisedBoundarySupport P x S hh e' := by
  rcases e with ⟨e,hm⟩
  rcases e with e | e
  · simp [xStarBoundaryEdgeMember] at hm
  · have hs : xStarEdgeMember P x (.inr e)=true :=
      xStarBoundaryEdgeMember_to_star P x (.inr e) hm
    obtain ⟨⟨f,j⟩,he⟩ := A.xBoundaryFaceOwner x e hs
    have hfull : (⟨.inr e,hm⟩ : XStarBoundaryEdge P x)=faceBoundaryEdge P x f j := by
      apply Subtype.ext
      exact (congrArg Subtype.val he).symm
    rw [hfull,raisedBoundary_face_start,raisedBoundary_face_end]
    fin_cases j
    · refine ⟨raisedBoundaryL0 P x S f,?_⟩
      exact raisedBoundaryL0_support P x S hh f
    · refine ⟨raisedBoundaryL1 P x S f,?_⟩
      exact raisedBoundaryL1_support P x S hh f
private theorem exists_raised_boundary_path (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (x : P.X) (S : OddScale) (hh : 2≤S.half)
    (v : XStarBoundaryVertex P x) :
    ∃ p : UndirectedPath (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
      (raisedBoundaryVertex P x S hh (A.xBoundaryRoot x))
      (raisedBoundaryVertex P x S hh v),
      ∀ e, pathChain p e≠0 → raisedBoundarySupport P x S hh e := by
  exact exists_path_substitution_OldXCore_QECert (raisedBoundaryVertex P x S hh)
    (raisedBoundarySupport P x S hh)
    (exists_raised_boundary_segment P A x S hh)
    (A.xBoundaryPath x v)
private theorem exists_actual_raised_boundary_path (S : OddScale) (hh : 2≤S.half)
    (c : BDL26FiniteTannerSquare.Two) (z : (RawOne S).Z)
    (v : XStarBoundaryVertex (transposePresentation (RawOne S)) z) :
    ∃ p : UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation (RawOne S)) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) z S)
      (actualRaisedRoots S hh c z)
      (c,raisedBoundaryVertex (transposePresentation (RawOne S)) z S hh v),
      ∀ e, pathChain p e≠0 → ∃ e',
        e=.inl (c,e') ∧ raisedBoundarySupport (transposePresentation (RawOne S)) z S hh e' := by
  let A := transposeTannerSquareAdmissibleV4 (RawOne S) (rxState S baseState).admissible
  obtain ⟨p,hp⟩ := exists_raised_boundary_path
    (transposePresentation (RawOne S)) A z S hh v
  refine ⟨atCopyPath (transposePresentation (RawOne S)) z S c p,?_⟩
  intro e he
  obtain ⟨e',he',heq⟩ := atCopyPath_support (transposePresentation (RawOne S)) z S c p e he
  exact ⟨e',heq,hp e' he'⟩
private theorem radialInterior_endpoint_neighbours (S : OddScale) (j : Fin 2)
    (i : Fin (S.half-1)) (x : BaseX)
    (e : DoubleCylinderEdge baseTannerSquarePresentation x S)
    (b : BDL26FiniteTannerSquare.Two)
    (h : radialInteriorX S j i=⟨x,BDL26TannerLocalRegularity.edgeEndpoint
      (tannerDoubleCylinderEdgeStart baseTannerSquarePresentation x S)
      (tannerDoubleCylinderEdgeEnd baseTannerSquarePresentation x S) e b⟩) :
    (Sum.inl ⟨x,e⟩ : (RawOne S).Q)=gammaRadial S j (radialPrevious S i) ∨
      (Sum.inl ⟨x,e⟩ : (RawOne S).Q)=gammaRadial S j (radialFollowing S i) ∨
      (Sum.inl ⟨x,e⟩ : (RawOne S).Q)=radialPerp S j i := by
  have howner : (0 : BaseX)=x := congrArg Sigma.fst h
  cases howner
  have hv := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  change (0,.inr (.inl (seedRadial j,i)))=
    BDL26TannerLocalRegularity.edgeEndpoint
      (tannerDoubleCylinderEdgeStart baseTannerSquarePresentation 0 S)
      (tannerDoubleCylinderEdgeEnd baseTannerSquarePresentation 0 S) e b at hv
  rcases e with ⟨c,e⟩ | v
  · have hc : (0 : BDL26FiniteTannerSquare.Two)=c := by
      fin_cases b <;> exact congrArg Prod.fst hv
    cases hc
    have hs : subdivisionEdgeStart baseTannerSquarePresentation 0 S e=
        .inr (.inl (seedRadial j,i)) ∨
      subdivisionEdgeEnd baseTannerSquarePresentation 0 S e=
        .inr (.inl (seedRadial j,i)) := by
      fin_cases b
      · left
        exact (congrArg Prod.snd hv).symm
      · right
        exact (congrArg Prod.snd hv).symm
    rcases radialInterior_subdivision_edges S j i e hs with he | he | he
    · left
      exact congrArg (fun a : SubdivisionEdge baseTannerSquarePresentation 0 S =>
        (Sum.inl ⟨(0 : BaseX),.inl (0,a)⟩ : (RawOne S).Q)) he
    · right
      left
      exact congrArg (fun a : SubdivisionEdge baseTannerSquarePresentation 0 S =>
        (Sum.inl ⟨(0 : BaseX),.inl (0,a)⟩ : (RawOne S).Q)) he
    · right
      right
      exact congrArg (fun a : SubdivisionEdge baseTannerSquarePresentation 0 S =>
        (Sum.inl ⟨(0 : BaseX),.inl (0,a)⟩ : (RawOne S).Q)) he
  · fin_cases b
    · have hvertex : (Sum.inr (.inl (seedRadial j,i)) :
          SubdivisionVertex baseTannerSquarePresentation 0 S)=v.val := congrArg Prod.snd hv
      have hm := v.property
      rw [← hvertex] at hm
      simp [subdivisionBoundaryVertexMember,seedRadial,xStarBoundaryEdgeMember] at hm
    · change (0,Sum.inr (Sum.inl (seedRadial j,i)))=(1,v.val) at hv
      have hc := congrArg Prod.fst hv
      have : (0 : BDL26FiniteTannerSquare.Two)≠1 := by decide
      exact False.elim (this hc)
private theorem radialInterior_shifted_false (S : OddScale) (j : Fin 2)
    (i : Fin (S.half-1)) (q : BaseQubit)
    (v : QDoubleCylinderVertex baseTannerSquarePresentation q S) :
    ¬(RawOne S).xq (radialInteriorX S j i) (.inr ⟨q,v⟩)=true := by
  have hm := raw_boundary1_view S (radialInteriorX S j i) (.inr ⟨q,v⟩)
  have hz : rxBoundary1Matrix baseTannerSquarePresentation S
      (radialInteriorX S j i) (.inr ⟨q,v⟩)=0 := by
    rcases v with ⟨c,(cone | endpoint) | ⟨edge,k⟩⟩
    all_goals
      fin_cases c <;>
        simp [rxBoundary1Matrix,qDoubleCylinderVertexXIncidence,
          qSubdivisionVertexXIncidence,radialInteriorX,seedRadial,
          xStarBoundaryEdgeToStar,qToXBoundaryEdge,Subtype.ext_iff,dite_eq_ite,ite_self]
    all_goals split_ifs <;> simp_all only [dite_eq_ite,ite_self]
    all_goals
      change (if _hxq : baseTannerSquarePresentation.xq (0 : BaseX) q=true then
        (0:F) else 0)=0
      split_ifs <;> rfl
  change rxBoundary1Matrix baseTannerSquarePresentation S
    (radialInteriorX S j i) (.inr ⟨q,v⟩)=
    (if (RawOne S).xq (radialInteriorX S j i) (.inr ⟨q,v⟩)=true then (1:F) else 0) at hm
  intro hi
  erw [hz,if_pos hi] at hm
  exact zero_ne_one hm
private theorem radialInterior_neighbours (S : OddScale) (j : Fin 2)
    (i : Fin (S.half-1)) (r : (RawOne S).Q)
    (hr : (RawOne S).xq (radialInteriorX S j i) r=true) :
    r=gammaRadial S j (radialPrevious S i) ∨
      r=gammaRadial S j (radialFollowing S i) ∨ r=radialPerp S j i := by
  change RX1 baseTannerSquarePresentation S at r
  rcases r with ⟨x,e⟩ | ⟨q,v⟩
  · rcases (old_local_incidence S _ x e).mp hr with hs | ht
    · exact radialInterior_endpoint_neighbours S j i x e 0
        (by change radialInteriorX S j i=⟨x,tannerDoubleCylinderEdgeStart
          baseTannerSquarePresentation x S e⟩; exact hs)
    · exact radialInterior_endpoint_neighbours S j i x e 1
        (by change radialInteriorX S j i=⟨x,tannerDoubleCylinderEdgeEnd
          baseTannerSquarePresentation x S e⟩; exact ht)
  · exact False.elim (radialInterior_shifted_false S j i q v hr)
private theorem shiftedFacePath0_raised_support (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (hh : 2≤S.half) (f : XStarFace P x)
    (i : Fin (S.half-1)) (e : SubdivisionEdge P x S)
    (he : pathChain (shiftedFacePath0 P x S f i) e≠0) :
    raisedPortSupport P x S hh i e := by
  rcases shiftedFacePath0_support_OldXCore_QECert P x S f i e he with h | h
  · obtain ⟨k,_,rfl⟩ := h
    left; left
    exact ⟨f,k,rfl⟩
  · right
    exact ⟨f,Or.inl h⟩
private theorem shiftedFacePath1_raised_support (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (hh : 2≤S.half) (f : XStarFace P x)
    (i : Fin (S.half-1)) (e : SubdivisionEdge P x S)
    (he : pathChain (shiftedFacePath1 P x S f i) e≠0) :
    raisedPortSupport P x S hh i e := by
  rcases shiftedFacePath1_support_OldXCore_QECert P x S f i e he with h | h
  · obtain ⟨k,_,rfl⟩ := h
    left; right; left
    exact ⟨f,k,rfl⟩
  · right
    exact ⟨f,Or.inr h⟩
private theorem exists_actual_raised_face_port_path (S : OddScale) (hh : 2≤S.half)
    (z : (RawOne S).Z) (f : XStarFace (transposePresentation (RawOne S)) z)
    (j : BDL26FiniteTannerSquare.Two)
    (hz : (RawOne S).qz ((RawOne S).faceQ f.val j) z=true)
    (c : BDL26FiniteTannerSquare.Two) (i : Fin (S.half-1)) :
    ∃ p : UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation (RawOne S)) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) z S)
      (actualRaisedRoots S hh c z)
      (qToZDoubleCylinderVertex (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible
        ((RawOne S).faceQ f.val j) z hz S
        (chosenPort (RawOne S) S ((RawOne S).faceQ f.val j)
          ((RawOne S).faceX f.val) ((RawOne S).data.faceQ_xq f.val j) c (some i))),
      ∀ e, pathChain p e≠0 → ∃ e',
        e=.inl (c,e') ∧ raisedPortSupport (transposePresentation (RawOne S)) z S hh i e' := by
  have oldBoundary := exists_actual_raised_boundary_path S hh c z
    (xBoundaryEdgeStart (transposePresentation (RawOne S)) z
      (faceBoundaryEdge (transposePresentation (RawOne S)) z f j))
  have hboundary := congrArg (fun v => (c,v))
    (raisedBoundary_face_start (transposePresentation (RawOne S)) z S hh f j)
  have boundary := (exists_supported_path_congr rfl hboundary _).mp oldBoundary
  fin_cases j
  · have hend := congrArg (fun v => (c,v))
      (qToZ_face_interior0 (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible z f hz S i)
    apply (exists_supported_path_congr rfl hend.symm _).mp
    simp only [ite_true] at boundary
    obtain ⟨initialPath,hprefix⟩ := boundary
    let suffix := atCopyPath (transposePresentation (RawOne S)) z S c
      (shiftedFacePath0 (transposePresentation (RawOne S)) z S f i)
    refine ⟨initialPath.append suffix,?_⟩
    apply path_append_support
    · intro e he
      obtain ⟨e',heq,hs⟩ := hprefix e he
      exact ⟨e',heq,Or.inl hs⟩
    · intro e he
      obtain ⟨e',he',heq⟩ := atCopyPath_support
        (transposePresentation (RawOne S)) z S c _ e he
      exact ⟨e',heq,shiftedFacePath0_raised_support
        (transposePresentation (RawOne S)) z S hh f i e' he'⟩
  · have hend := congrArg (fun v => (c,v))
      (qToZ_face_interior1 (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible z f hz S i)
    apply (exists_supported_path_congr rfl hend.symm _).mp
    simp only [show (1 : BDL26FiniteTannerSquare.Two)≠0 by decide,ite_false] at boundary
    obtain ⟨initialPath,hprefix⟩ := boundary
    let suffix := atCopyPath (transposePresentation (RawOne S)) z S c
      (shiftedFacePath1 (transposePresentation (RawOne S)) z S f i)
    refine ⟨initialPath.append suffix,?_⟩
    apply path_append_support
    · intro e he
      obtain ⟨e',heq,hs⟩ := hprefix e he
      exact ⟨e',heq,Or.inl hs⟩
    · intro e he
      obtain ⟨e',he',heq⟩ := atCopyPath_support
        (transposePresentation (RawOne S)) z S c _ e he
      exact ⟨e',heq,shiftedFacePath1_raised_support
        (transposePresentation (RawOne S)) z S hh f i e' he'⟩
private theorem exists_actual_raised_port_path (S : OddScale) (hh : 2≤S.half)
    (r : (RawOne S).Q) (x : (RawOne S).X) (z : (RawOne S).Z)
    (hx : (RawOne S).xq x r=true) (hz : (RawOne S).qz r z=true)
    (c : BDL26FiniteTannerSquare.Two) (i : Fin (S.half-1)) :
    ∃ p : UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation (RawOne S)) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) z S)
      (actualRaisedRoots S hh c z)
      (qToZDoubleCylinderVertex (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S
        (chosenPort (RawOne S) S r x hx c (some i))),
      ∀ e, pathChain p e≠0 → ∃ e',
        e=.inl (c,e') ∧ raisedPortSupport (transposePresentation (RawOne S)) z S hh i e' := by
  obtain ⟨f,j,hq,hx'⟩ := face_of_qxz (RawOne S) x r z hx hz
  cases hq
  cases hx'
  exact exists_actual_raised_face_port_path S hh z f j hz c i
private theorem cast_rz_any_segment (S : OddScale) {P Q : TannerSquarePresentation}
    (h : P=Q) (z : Q.Z) (a : XStarEdge (transposePresentation Q) z)
    (c : BDL26FiniteTannerSquare.Two) (k : Fin S.half) :
    cast (congrArg (fun P => RZQ P S) h).symm
      (.inl ⟨z,.inl (c,.inl (a,k))⟩)=
      .inl ⟨cast (congrArg TannerSquarePresentation.Z h).symm z,
        .inl (c,.inl (castZStarEdge h z a,k))⟩ := by
  cases h
  rfl
private theorem cast_rz_horizontal (S : OddScale) {P Q : TannerSquarePresentation}
    (h : P=Q) (z : Q.Z) (f : XStarFace (transposePresentation Q) z)
    (c : BDL26FiniteTannerSquare.Two) (a : Fin S.half) (b : Fin (S.half-1)) :
    cast (congrArg (fun P => RZQ P S) h).symm
      (.inl ⟨z,.inl (c,.inr (.inl (f,a,b)))⟩)=
      .inl ⟨cast (congrArg TannerSquarePresentation.Z h).symm z,
        .inl (c,.inr (.inl (castZStarFace h z f,a,b)))⟩ := by
  cases h
  rfl
private theorem cast_rz_vertical (S : OddScale) {P Q : TannerSquarePresentation}
    (h : P=Q) (z : Q.Z) (f : XStarFace (transposePresentation Q) z)
    (c : BDL26FiniteTannerSquare.Two) (a : Fin (S.half-1)) (b : Fin S.half) :
    cast (congrArg (fun P => RZQ P S) h).symm
      (.inl ⟨z,.inl (c,.inr (.inr (f,a,b)))⟩)=
      .inl ⟨cast (congrArg TannerSquarePresentation.Z h).symm z,
        .inl (c,.inr (.inr (castZStarFace h z f,a,b)))⟩ := by
  cases h
  rfl
private theorem encoded_any_segment (S : OddScale) (z : (RawOne S).Z)
    (a : XStarEdge (transposePresentation (RawOne S)) z)
    (c : BDL26FiniteTannerSquare.Two) (k : Fin S.half) :
    Encodable.encode (executableCoordinate S (.inl ⟨z,.inl (c,.inl (a,k))⟩))=
      2*Nat.pair (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
        (2*Nat.pair c.val (2*Nat.pair
          (Encodable.encode (castZStarEdge
            (executableLevelOne_eq_raw S) z a).val) k.val)) := by
  change Encodable.encode (cast (congrArg (fun P => RZQ P S)
    (executableLevelOne_eq_raw S)).symm _) = _
  erw [cast_rz_any_segment S (executableLevelOne_eq_raw S) z a c k]
  rfl
private theorem structural_horizontal_encoding (P : TannerSquarePresentation)
    [Encodable P.X] [Encodable P.Q] [Encodable P.Z] [Encodable P.Face]
    (S : OddScale) (z : P.Z) (f : XStarFace (transposePresentation P) z)
    (c : BDL26FiniteTannerSquare.Two)
    (a : Fin S.half) (b : Fin (S.half-1)) :
  letI : Encodable (transposePresentation P).Face :=
    inferInstanceAs (Encodable P.Face)
  letI : ∀ z : P.Z, Encodable (SubdivisionVertex (transposePresentation P) z S) :=
    fun z => by
      dsimp [SubdivisionVertex,XStarVertex,XStarEdge,XStarFace,
        BDL26FiniteTannerSquare.Edge,XQEdge,QZEdge,
        transposePresentation,transposeTannerSquareData]
      infer_instance
  letI : ∀ z : P.Z, Encodable (SubdivisionEdge (transposePresentation P) z S) :=
    fun z => by
      dsimp [SubdivisionEdge,XStarEdge,XStarFace,BDL26FiniteTannerSquare.Edge,
        XQEdge,QZEdge,transposePresentation,transposeTannerSquareData]
      infer_instance
  letI : Encodable (RZQ P S) := by
    dsimp [RZQ,ZDoubleCylinderEdge,DoubleCylinderEdge,QDoubleCylinderVertex,
      transposePresentation,transposeTannerSquareData]
    infer_instance
  Encodable.encode (Sum.inl ⟨z,Sum.inl (c,Sum.inr (Sum.inl (f,a,b)))⟩ : RZQ P S)=
    2*Nat.pair (Encodable.encode z) (2*Nat.pair c.val (2*(2*Nat.pair (Encodable.encode f.val) (Nat.pair a.val b.val))+1)) := by
  rfl
private theorem structural_vertical_encoding (P : TannerSquarePresentation)
    [Encodable P.X] [Encodable P.Q] [Encodable P.Z] [Encodable P.Face]
    (S : OddScale) (z : P.Z) (f : XStarFace (transposePresentation P) z)
    (c : BDL26FiniteTannerSquare.Two)
    (a : Fin (S.half-1)) (b : Fin S.half) :
  letI : Encodable (transposePresentation P).Face :=
    inferInstanceAs (Encodable P.Face)
  letI : ∀ z : P.Z, Encodable (SubdivisionVertex (transposePresentation P) z S) :=
    fun z => by
      dsimp [SubdivisionVertex,XStarVertex,XStarEdge,XStarFace,
        BDL26FiniteTannerSquare.Edge,XQEdge,QZEdge,
        transposePresentation,transposeTannerSquareData]
      infer_instance
  letI : ∀ z : P.Z, Encodable (SubdivisionEdge (transposePresentation P) z S) :=
    fun z => by
      dsimp [SubdivisionEdge,XStarEdge,XStarFace,BDL26FiniteTannerSquare.Edge,
        XQEdge,QZEdge,transposePresentation,transposeTannerSquareData]
      infer_instance
  letI : Encodable (RZQ P S) := by
    dsimp [RZQ,ZDoubleCylinderEdge,DoubleCylinderEdge,QDoubleCylinderVertex,
      transposePresentation,transposeTannerSquareData]
    infer_instance
  Encodable.encode (Sum.inl ⟨z,Sum.inl (c,Sum.inr (Sum.inr (f,a,b)))⟩ : RZQ P S)=
    2*Nat.pair (Encodable.encode z) (2*Nat.pair c.val (2*(2*Nat.pair (Encodable.encode f.val) (Nat.pair a.val b.val)+1)+1)) := by
  rfl
private theorem encoded_horizontal_raw (S : OddScale) (z : (RawOne S).Z)
    (f : XStarFace (transposePresentation (RawOne S)) z)
    (c : BDL26FiniteTannerSquare.Two) (a : Fin S.half) (b : Fin (S.half-1)) :
    Encodable.encode (executableCoordinate S
      (.inl ⟨z,.inl (c,.inr (.inl (f,a,b)))⟩))=
      2*Nat.pair (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
        (2*Nat.pair c.val (2*(2*Nat.pair
          (Encodable.encode (castZStarFace
            (executableLevelOne_eq_raw S) z f).val)
          (Nat.pair a.val b.val))+1)) := by
  change Encodable.encode (cast (congrArg (fun P => RZQ P S)
    (executableLevelOne_eq_raw S)).symm _) = _
  erw [cast_rz_horizontal S (executableLevelOne_eq_raw S) z f c a b]
  exact structural_horizontal_encoding (BDL26LevelTwoDecoder.executableLevelOne S) S
    (cast (congrArg TannerSquarePresentation.Z (executableLevelOne_eq_raw S)).symm z)
    (castZStarFace (executableLevelOne_eq_raw S) z f) c a b
private theorem encoded_horizontal (S : OddScale) (z : (RawOne S).Z)
    (f : XStarFace (transposePresentation (RawOne S)) z)
    (c : BDL26FiniteTannerSquare.Two) (a : Fin S.half) (b : Fin (S.half-1)) :
    Encodable.encode (executableCoordinate S
      (.inl ⟨z,.inl (c,.inr (.inl (f,a,b)))⟩))=
      2*Nat.pair (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
        (2*Nat.pair c.val (4*Nat.pair
          (Encodable.encode (castZStarFace
            (executableLevelOne_eq_raw S) z f).val)
          (Nat.pair a.val b.val)+1)) := by
  rw [encoded_horizontal_raw]
  apply congrArg (fun n => 2*Nat.pair
    (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
    (2*Nat.pair c.val n))
  omega
private theorem encoded_vertical_raw (S : OddScale) (z : (RawOne S).Z)
    (f : XStarFace (transposePresentation (RawOne S)) z)
    (c : BDL26FiniteTannerSquare.Two) (a : Fin (S.half-1)) (b : Fin S.half) :
    Encodable.encode (executableCoordinate S
      (.inl ⟨z,.inl (c,.inr (.inr (f,a,b)))⟩))=
      2*Nat.pair (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
        (2*Nat.pair c.val (2*(2*Nat.pair
          (Encodable.encode (castZStarFace
            (executableLevelOne_eq_raw S) z f).val)
          (Nat.pair a.val b.val)+1)+1)) := by
  change Encodable.encode (cast (congrArg (fun P => RZQ P S)
    (executableLevelOne_eq_raw S)).symm _) = _
  erw [cast_rz_vertical S (executableLevelOne_eq_raw S) z f c a b]
  exact structural_vertical_encoding (BDL26LevelTwoDecoder.executableLevelOne S) S
    (cast (congrArg TannerSquarePresentation.Z (executableLevelOne_eq_raw S)).symm z)
    (castZStarFace (executableLevelOne_eq_raw S) z f) c a b
private theorem encoded_vertical (S : OddScale) (z : (RawOne S).Z)
    (f : XStarFace (transposePresentation (RawOne S)) z)
    (c : BDL26FiniteTannerSquare.Two) (a : Fin (S.half-1)) (b : Fin S.half) :
    Encodable.encode (executableCoordinate S
      (.inl ⟨z,.inl (c,.inr (.inr (f,a,b)))⟩))=
      2*Nat.pair (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
        (2*Nat.pair c.val (4*Nat.pair
          (Encodable.encode (castZStarFace
            (executableLevelOne_eq_raw S) z f).val)
          (Nat.pair a.val b.val)+3)) := by
  rw [encoded_vertical_raw]
  apply congrArg (fun n => 2*Nat.pair
    (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
    (2*Nat.pair c.val n))
  omega
private theorem raisedPortSupport_later (S : OddScale) (hh : 2≤S.half)
    (r0 : (RawOne S).Q) (x0 : (RawOne S).X)
    (hx0 : (RawOne S).xq x0 r0=true) (z : (RawOne S).Z)
    (c : BDL26FiniteTannerSquare.Two) (i : Fin (S.half-1))
    (hr : Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q)< i.val)
    (hx : Encodable.encode (x0 : (BDL26LevelTwoDecoder.executableLevelOne S).X)< i.val)
    (e : SubdivisionEdge (transposePresentation (RawOne S)) z S)
    (he : raisedPortSupport (transposePresentation (RawOne S)) z S hh i e) :
    Encodable.encode (executableCoordinate S
      (.inr ⟨r0,chosenPort (RawOne S) S r0 x0 hx0 c (some i)⟩))<
      Encodable.encode (executableCoordinate S (.inl ⟨z,.inl (c,e)⟩)) := by
  rw [encoded_chosenPort_OldXCore_QECert]
  rcases he with (⟨f,k,rfl⟩ | ⟨f,k,rfl⟩ | ⟨a,rfl⟩) | ⟨f,h | h⟩
  · erw [encoded_vertical]
    apply interior_before_grid_code_OldXCore_QECert _ _ _ _ _ _ _ _ c hr hx _ (by decide)
    have := i.isLt
    dsimp [lastInterior]
    omega
  · erw [encoded_horizontal]
    apply interior_before_grid_code_OldXCore_QECert _ _ _ _ _ _ _ _ c hr hx _ (by decide)
    have := i.isLt
    dsimp [lastInterior]
    omega
  · erw [encoded_any_segment]
    exact interior_before_far_last_radial_code_OldXCore_QECert _ _ _ _ _ _ c hr hx
      (by have := i.isLt; dsimp [lastSegment]; omega)
  · subst e
    erw [encoded_horizontal]
    exact interior_before_grid_code_OldXCore_QECert _ _ _ _ _ _ _ _ c hr hx
      (by have := i.isLt; dsimp [lastSegment]; omega) (by decide)
  · subst e
    erw [encoded_vertical]
    exact interior_before_grid_code_OldXCore_QECert _ _ _ _ _ _ _ _ c hr hx
      (by have := i.isLt; dsimp [lastSegment]; omega) (by decide)
theorem exists_raised_path_later_OldXBounded_QECert (S : OddScale)
    (r0 r : (RawOne S).Q) (x0 x : (RawOne S).X)
    (hx0 : (RawOne S).xq x0 r0=true) (hx : (RawOne S).xq x r=true)
    (z : (RawOne S).Z) (hz : (RawOne S).qz r z=true)
    (c : BDL26FiniteTannerSquare.Two) (i : Fin (S.half-1))
    (hr : Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q)< i.val)
    (hX : Encodable.encode (x0 : (BDL26LevelTwoDecoder.executableLevelOne S).X)< i.val) :
    ∃ p : UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation (RawOne S)) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) z S)
      (actualRaisedRoots S (by have := i.isLt; omega) c z)
      (qToZDoubleCylinderVertex (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S
        (chosenPort (RawOne S) S r x hx c (some i))),
      ∀ e, pathChain p e≠0 →
        Encodable.encode (executableCoordinate S
          (.inr ⟨r0,chosenPort (RawOne S) S r0 x0 hx0 c (some i)⟩))<
          Encodable.encode (executableCoordinate S (.inl ⟨z,e⟩)) := by
  have hh : 2≤S.half := by have := i.isLt; omega
  obtain ⟨p,hp⟩ := exists_actual_raised_port_path S hh r x z hx hz c i
  refine ⟨p,?_⟩
  intro e he
  obtain ⟨e',rfl,hs⟩ := hp e he
  exact raisedPortSupport_later S hh r0 x0 hx0 z c i hr hX e' hs
private theorem global_same_owner_raised_zero (S : OddScale) (a : Word F (RawTwo S).Q)
    (r : (RawOne S).Q) (z : (RawOne S).Z) (hz : (RawOne S).qz r z=true)
    (hu : ∀ z', (RawOne S).qz r z'=true → z'=z)
    (x x' : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (hx' : (RawOne S).xq x' r=true) (c : BDL26FiniteTannerSquare.Two)
    (i : Fin (S.half-1))
    (hr : Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)< i.val)
    (hX : Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)< i.val)
    (horder : Encodable.encode (executableCoordinate S
      (.inr ⟨r,chosenPort (RawOne S) S r x hx c (some i)⟩))<
        Encodable.encode (executableCoordinate S
          (.inr ⟨r,chosenPort (RawOne S) S r x' hx' c (some i)⟩))) :
    BDL26GlobalLookupLinearity.actualGlobal S (tannerCoboundary1 (RawTwo S) a)
      (.inr ⟨r,chosenPort (RawOne S) S r x hx c (some i)⟩)=0 := by
  obtain ⟨p,hp⟩ := exists_raised_path_later_OldXBounded_QECert S r r x x hx hx z hz c i hr hX
  obtain ⟨p',hp'⟩ := exists_raised_path_later_OldXBounded_QECert S r r x x' hx hx' z hz c i hr hX
  exact global_zero_of_same_owner_pair_OldXCore_QECert S a r z hz hu _ _
    (actualRaisedRoots S (by have := i.isLt; omega) c z) p p' horder hp hp'
private theorem gamma_code_gt_one (S : OddScale) (j : Fin 2) (n : Fin S.half)
    (hn : 0<j.val+n.val) :
    1<Encodable.encode (gammaRadial S j n :
      (BDL26LevelTwoDecoder.executableLevelOne S).Q) := by
  erw [encoded_gammaRadial_OldXCore_QECert]
  have hl := Nat.left_le_pair (2*j.val) n.val
  have hr := Nat.right_le_pair (2*j.val) n.val
  have hp : 0<Nat.pair (2*j.val) n.val := by omega
  have hp4 : 0<(Nat.pair (2*j.val) n.val)^4 := pow_pos hp _
  omega
theorem global_radial_minor_interior_zero_OldXBounded_QECert (S : OddScale)
    (a : Word F (RawTwo S).Q) (j : Fin 2) (n : Fin S.half)
    (hn : 0<j.val+n.val) (x : (RawOne S).X)
    (hx : (RawOne S).xq x (gammaRadial S j n)=true)
    (hne : x≠oldLargestX S (gammaRadial S j n))
    (c : BDL26FiniteTannerSquare.Two) (i : Fin (S.half-1)) :
    BDL26GlobalLookupLinearity.actualGlobal S (tannerCoboundary1 (RawTwo S) a)
      (.inr ⟨gammaRadial S j n,(c,.inr (⟨x,hx⟩,i))⟩)=0 := by
  let r := gammaRadial S j n
  let K := Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)
  have hK : 0<K := gamma_code_pos_OldXCore_QECert S j n hn
  have hK1 : 1<K := gamma_code_gt_one S j n hn
  have hxle := oldLargestX_upper_OldXCore_QECert S 0 (.inl (0,.inl (seedRadial j,n))) x hx
  change Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
    Encodable.encode (oldLargestX S r :
      (BDL26LevelTwoDecoder.executableLevelOne S).X) at hxle
  have hstrict : Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)<
      Encodable.encode (oldLargestX S r :
        (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
    have hnc : Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)≠
        Encodable.encode (oldLargestX S r :
          (BDL26LevelTwoDecoder.executableLevelOne S).X) :=
      fun he => hne (Encodable.encode_injective he)
    omega
  have hX : Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)<K^2 :=
    hstrict.trans_le (gammaLargestX_le_square_OldXCore_QECert S j n hn)
  have hR : K<K^2 := by nlinarith
  have hz : (RawOne S).qz r (seedRadialCheck S j n)=true :=
    (seedRadial_degree_one S j n).1
  have horder := chosenPort_order_same_owner_OldXCore_QECert S r x (oldLargestX S r) hx
    (oldLargestX_incident S r) c (some i) hstrict
  by_cases hi : i.val<K^2
  · have hidepth : ∀ k, some i=some k → k.val<K^2 := by
      intro k he
      cases he
      exact hi
    exact global_same_owner_direct_zero S a r (seedRadialCheck S j n) hz
      (seedRadial_degree_one S j n).2 x (oldLargestX S r) hx
      (oldLargestX_incident S r) c (some i) K hK le_rfl hR.le hX.le hidepth horder
  · have hr : K< i.val := by omega
    have hx' : Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)<
        i.val := by omega
    exact global_same_owner_raised_zero S a r (seedRadialCheck S j n) hz
      (seedRadial_degree_one S j n).2 x (oldLargestX S r) hx
      (oldLargestX_incident S r) c i hr hx' horder
private theorem radial_perp_tag_gt (j : Fin 2) (i : Nat)
    (hex : j.val≠1 ∨ i≠0) :
    2*Nat.pair (2*j.val) i<4*Nat.pair j.val (Nat.pair i 0)+3 := by
  fin_cases j
  · change 2*Nat.pair 0 i<4*Nat.pair 0 (Nat.pair i 0)+3
    rw [pair_zero_left_sq_OldXCore_QECert]
    have hsq : i^2≤Nat.pair i 0 := by
      simpa only [max_eq_left (Nat.zero_le i),min_eq_right (Nat.zero_le i),add_zero] using
        Nat.max_sq_add_min_le_pair i 0
    have hl := Nat.right_le_pair 0 (Nat.pair i 0)
    omega
  · change 1≠1 ∨ i≠0 at hex
    change 2*Nat.pair 2 i<4*Nat.pair 1 (Nat.pair i 0)+3
    have hi : 0 < i := by omega
    by_cases hone : i=1
    · subst i
      decide
    · have hi2 : 2 ≤ i := by omega
      have hp : Nat.pair 2 i<(i+1)^2 := by
        simpa only [max_eq_right hi2] using Nat.pair_lt_max_add_one_sq 2 i
      have hl : i^2≤Nat.pair i 0 := by
        simpa only [max_eq_left (Nat.zero_le i),min_eq_right (Nat.zero_le i),add_zero] using
          Nat.max_sq_add_min_le_pair i 0
      have hli : i+1≤Nat.pair i 0 := by nlinarith
      have hs := Nat.pow_le_pow_left hli 2
      have hlow := Nat.max_sq_add_min_le_pair 1 (Nat.pair i 0)
      have hs' := Nat.pow_le_pow_left (Nat.le_max_right 1 (Nat.pair i 0)) 2
      have hlow' : max 1 (Nat.pair i 0)^2≤Nat.pair 1 (Nat.pair i 0) := by omega
      have hpair := hp.trans_le (hs.trans (hs'.trans hlow'))
      omega
private theorem old_local_subedge_order (S : OddScale)
    (e e' : SubdivisionEdge baseTannerSquarePresentation (0 : BaseX) S)
    (h : subEdgeCode 0 S e<subEdgeCode 0 S e') :
    Encodable.encode (.inl ⟨(0 : BaseX),.inl (0,e)⟩ :
      (BDL26LevelTwoDecoder.executableLevelOne S).Q)<
      Encodable.encode (.inl ⟨(0 : BaseX),.inl (0,e')⟩ :
        (BDL26LevelTwoDecoder.executableLevelOne S).Q) := by
  erw [encoded_old_local_Q_OldXCore_QECert,encoded_old_local_Q_OldXCore_QECert]
  have hi := Nat.pair_lt_pair_right 0 h
  have ho := Nat.pair_lt_pair_right 0 (show 2*Nat.pair 0 (subEdgeCode 0 S e)<
      2*Nat.pair 0 (subEdgeCode 0 S e') by omega)
  simp only [Fin.val_zero,Fin.val_one,Fin.val_mk] at *
  omega
private theorem radialInterior_minimum (S : OddScale) (j : Fin 2)
    (i : Fin (S.half-1)) (hex : j.val≠1 ∨ i.val≠0)
    (r : (RawOne S).Q) (hr : (RawOne S).xq (radialInteriorX S j i) r=true)
    (hne : r≠gammaRadial S j (radialPrevious S i)) :
    Encodable.encode (gammaRadial S j (radialPrevious S i) :
      (BDL26LevelTwoDecoder.executableLevelOne S).Q)<
      Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q) := by
  rcases radialInterior_neighbours S j i r hr with h | h | h
  · exact False.elim (hne h)
  · subst r
    apply old_local_subedge_order S
    change 2*Nat.pair (baseEdgeCode (seedRadial j).val) i.val<
      2*Nat.pair (baseEdgeCode (seedRadial j).val) (i.val+1)
    have := Nat.pair_lt_pair_right (baseEdgeCode (seedRadial j).val)
      (Nat.lt_succ_self i.val)
    simp only [Nat.succ_eq_add_one,Fin.val_mk] at *
    omega
  · subst r
    apply old_local_subedge_order S
    change 2*Nat.pair (baseEdgeCode (seedRadial j).val) i.val<
      4*Nat.pair j.val (Nat.pair i.val 0)+3
    rw [seedRadial_code_OldXCore_QECert]
    exact radial_perp_tag_gt j i.val hex
private theorem radialInterior_is_end (S : OddScale) (j : Fin 2)
    (i : Fin (S.half-1)) :
    oldLocalEnd S 0 (.inl (0,.inl (seedRadial j,radialPrevious S i)))=
      radialInteriorX S j i := by
  have hn : (radialPrevious S i).val+1≠S.half := by
    have := i.isLt
    dsimp [radialPrevious]
    omega
  simp only [oldLocalEnd,tannerDoubleCylinderEdgeEnd,subdivisionEdgeEnd,
    subdivisionSegmentEnd,dif_neg hn]
  apply congrArg (fun v => (⟨(0 : BaseX),(0,v)⟩ : (RawOne S).X))
  apply congrArg Sum.inr
  apply congrArg Sum.inl
  apply Prod.ext rfl
  apply Fin.ext
  rfl
private theorem radialInterior_incident (S : OddScale) (j : Fin 2)
    (i : Fin (S.half-1)) :
    (RawOne S).xq (radialInteriorX S j i)
      (gammaRadial S j (radialPrevious S i))=true := by
  apply (old_local_incidence S _ 0
    (.inl (0,.inl (seedRadial j,radialPrevious S i)))).2
  right
  exact (radialInterior_is_end S j i).symm
private theorem radialInterior_largest (S : OddScale) (j : Fin 2)
    (i : Fin (S.half-1)) :
    oldLargestX S (gammaRadial S j (radialPrevious S i))=radialInteriorX S j i := by
  have horder : Encodable.encode (oldLocalStart S 0
      (.inl (0,.inl (seedRadial j,radialPrevious S i))) :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (oldLocalEnd S 0
        (.inl (0,.inl (seedRadial j,radialPrevious S i))) :
          (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
    rw [radialInterior_is_end]
    change Encodable.encode (⟨(0 : BaseX),(0,
      subdivisionSegmentStart baseTannerSquarePresentation 0 S (seedRadial j)
        (radialPrevious S i))⟩ : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (⟨(0 : BaseX),(0,.inr (.inl (seedRadial j,i)))⟩ :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)
    erw [encoded_old_X_copy0_OldXCore_QECert,encoded_old_X_copy0_OldXCore_QECert]
    unfold subdivisionSegmentStart
    split_ifs with hz
    · simp only [subVertexCode,seedRadial_start_code_OldXCore_QECert,mul_zero,zero_pow (by decide : (4:Nat)≠0)]
      exact Nat.zero_le _
    · apply Nat.pow_le_pow_left _ 4
      change 4*Nat.pair (baseEdgeCode (seedRadial j).val) (i.val-1)+1≤
        4*Nat.pair (baseEdgeCode (seedRadial j).val) i.val+1
      have := pair_mono_right_OldXCore_QECert (baseEdgeCode (seedRadial j).val) (i.val-1) i.val
        (Nat.sub_le _ _)
      omega
  change (if _ then _ else _)=_
  erw [if_pos horder]
  exact radialInterior_is_end S j i
theorem global_nonterminal_large_port_zero_OldXBounded_QECert (S : OddScale)
    (a : Word F (RawTwo S).Q) (j : Fin 2) (i : Fin (S.half-1))
    (hex : j.val≠1 ∨ i.val≠0) (c : BDL26FiniteTannerSquare.Two)
    (depth : Option (Fin (S.half-1))) :
    BDL26GlobalLookupLinearity.actualGlobal S (tannerCoboundary1 (RawTwo S) a)
      (.inr ⟨gammaRadial S j (radialPrevious S i),
        largePorts S c depth (gammaRadial S j (radialPrevious S i))⟩)=0 := by
  have hx := radialInterior_incident S j i
  have hl := radialInterior_largest S j i
  cases depth with
  | none =>
    change BDL26GlobalLookupLinearity.actualGlobal S _
      (.inr ⟨_,(c,.inl (.inr ⟨_,_⟩))⟩)=0
    simp only [hl]
    exact global_endpoint_of_least_old_neighbor_OldXCore_QECert S a _ _ hx c
      (radialInterior_minimum S j i hex)
  | some k =>
    by_cases hk : k.val+2<S.half
    · exact global_interior_zero_before_last S a _ _ _ c k hk
    · have hh : 2≤S.half := by have := k.isLt; omega
      have hlast : k=lastInterior S hh := by
        apply Fin.ext
        have := k.isLt
        dsimp [lastInterior]
        omega
      subst k
      change BDL26GlobalLookupLinearity.actualGlobal S _
        (.inr ⟨_,(c,.inr (⟨_,_⟩,lastInterior S hh))⟩)=0
      simp only [hl]
      exact global_last_interior_of_least_old_neighbor_OldXCore_QECert S hh a _ _ hx c
        (radialInterior_minimum S j i hex)
theorem firstCutOldKernel_support_OldXBounded_QECert (S : OddScale)
    (r : (RawOne S).Q) (hr : firstCutOldKernel S r≠0) :
    ∃ (x : BaseX) (c : BDL26FiniteTannerSquare.Two) (row : Fin (S.half+1)),
      r=firstCutHorizontal S x c row := by
  change RX1 baseTannerSquarePresentation S at r
  rcases r with ⟨x,e⟩ | ⟨q,v⟩
  · rcases e with ⟨c,e⟩ | v
    · rcases subdivision_edge_grid_cover_OldXCore_QECert baseTannerSquarePresentation
        baseTannerSquareAdmissibleV4 x S e with hh | hv
      · obtain ⟨f,i,row,he⟩ := hh
        subst e
        erw [firstCutOldKernel_horizontal_OldXCore_QECert] at hr
        have h : f=stripFace 1 x ∧ i.val=0 := by
          by_contra hn
          rw [if_neg hn] at hr
          exact hr rfl
        rcases h with ⟨hf,hi⟩
        subst f
        have hi0 : i=⟨0,S.half_pos⟩ := Fin.ext hi
        subst i
        exact ⟨x,c,row,rfl⟩
      · obtain ⟨f,column,i,he⟩ := hv
        subst e
        erw [firstCutOldKernel_vertical_OldXCore_QECert] at hr
        exact False.elim (hr rfl)
    · erw [firstCutOldKernel,Pi.add_apply,rawSeedLift,
        BDL26ReplacementCochainMaps.rxMap1Coord_localEdge,zero_add,
        rx_local_gradient] at hr
      change ((if firstCutMember x S v.val then (1:F) else 0)+
        (if firstCutMember x S v.val then (1:F) else 0))≠0 at hr
      exact False.elim (hr (ZModModule.add_self _))
  · exact False.elim (hr (firstCutOldKernel_q_zero_OldXCore_QECert S q v))
private theorem firstCut_subedge_lower (S : OddScale) (x : BaseX)
    (row : Fin (S.half+1)) :
    9≤ subEdgeCode x S (subdivisionHorizontalEdge baseTannerSquarePresentation x S
      (stripFace 1 x) ⟨0,S.half_pos⟩ row) := by
  unfold subdivisionHorizontalEdge
  split_ifs with hzero hlast
  · change 9≤2*Nat.pair (baseEdgeCode
      (xStarFaceXQEdge baseTannerSquarePresentation x (stripFace 1 x) 0).val) 0
    rw [stripFace_xq_code_OldXCore_QECert]
    fin_cases x <;> decide
  · change 9≤2*Nat.pair (baseEdgeCode
      (xStarFaceQZEdge baseTannerSquarePresentation x (stripFace 1 x) 1).val) 0
    rw [stripFace_qz_code_OldXCore_QECert]
    decide
  · change 9≤4*Nat.pair (1+2*x.val) (Nat.pair 0 (row.val-1))+1
    have hl := Nat.max_sq_add_min_le_pair (1+2*x.val) (Nat.pair 0 (row.val-1))
    have hs := Nat.pow_le_pow_left (Nat.le_max_left (1+2*x.val)
      (Nat.pair 0 (row.val-1))) 2
    have hx : 1≤1+2*x.val := by omega
    have hp : 2≤Nat.pair (1+2*x.val) (Nat.pair 0 (row.val-1)) := by
      rw [Nat.pair]
      split_ifs with h
      · have := Nat.pow_le_pow_left h.le 2
        nlinarith
      · nlinarith
    omega
theorem firstCut_oldQ_lower_OldXBounded_QECert (S : OddScale) (x : BaseX)
    (c : BDL26FiniteTannerSquare.Two) (row : Fin (S.half+1)) :
    52488≤Encodable.encode (firstCutHorizontal S x c row :
      (BDL26LevelTwoDecoder.executableLevelOne S).Q) := by
  erw [firstCutHorizontal,encoded_old_local_Q_OldXCore_QECert]
  have hE := firstCut_subedge_lower S x row
  let E := subEdgeCode x S (subdivisionHorizontalEdge baseTannerSquarePresentation x S
    (stripFace 1 x) ⟨0,S.half_pos⟩ row)
  have hi := pair_mono_right_OldXCore_QECert 0 9 E hE
  have hc := pair_mono_left_OldXCore_QECert 0 c.val E (Nat.zero_le _)
  have hm : 2*Nat.pair 0 9≤2*Nat.pair c.val E := by omega
  have ho := pair_mono_right_OldXCore_QECert 0 _ _ hm
  have hx := pair_mono_left_OldXCore_QECert 0 x.val (2*Nat.pair c.val E) (Nat.zero_le _)
  have hconstant : 2*Nat.pair 0 (2*Nat.pair 0 9)=52488 := by decide
  have ho' : 2*Nat.pair 0 (2*Nat.pair 0 9)≤
      2*Nat.pair 0 (2*Nat.pair c.val E) := Nat.mul_le_mul_left 2 ho
  rw [hconstant] at ho'
  exact ho'.trans (Nat.mul_le_mul_left 2 hx)
theorem largePorts_later_of_X_OldXBounded_QECert (S : OddScale)
    (r0 r : (RawOne S).Q) (c : BDL26FiniteTannerSquare.Two)
    (depth : Option (Fin (S.half-1)))
    (hX : Encodable.encode (oldLargestX S r0 :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)<
      Encodable.encode (oldLargestX S r : (BDL26LevelTwoDecoder.executableLevelOne S).X))
    (hR : Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q)<
      (Encodable.encode (oldLargestX S r :
        (BDL26LevelTwoDecoder.executableLevelOne S).X))^2) :
    Encodable.encode (executableCoordinate S (.inr ⟨r0,largePorts S c depth r0⟩))<
      Encodable.encode (executableCoordinate S (.inr ⟨r,largePorts S c depth r⟩)) := by
  let X0 := Encodable.encode (oldLargestX S r0 :
    (BDL26LevelTwoDecoder.executableLevelOne S).X)
  let X := Encodable.encode (oldLargestX S r :
    (BDL26LevelTwoDecoder.executableLevelOne S).X)
  have htail : ∀ V : Nat, X≤V →
      Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q)<
        Nat.pair c.val V := by
    intro V hV
    have hs := Nat.pow_le_pow_left hV 2
    have hl := Nat.max_sq_add_min_le_pair c.val V
    have hm := Nat.pow_le_pow_left (Nat.le_max_right c.val V) 2
    dsimp only [X,X0] at *
    omega
  cases depth with
  | none =>
    rw [encoded_largePorts_OldXCore_QECert,encoded_largePorts_OldXCore_QECert]
    dsimp only
    apply q_before_larger_port_code_OldXCore_QECert _ _ _ _ c (by omega)
    exact htail _ (by omega)
  | some i =>
    rw [encoded_largePorts_OldXCore_QECert,encoded_largePorts_OldXCore_QECert]
    dsimp only
    have hp := Nat.pair_lt_pair_left i.val hX
    apply q_before_larger_port_code_OldXCore_QECert _ _ _ _ c (by omega)
    apply htail
    have hl := Nat.left_le_pair X i.val
    dsimp only [X,X0] at *
    omega
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
end
end


