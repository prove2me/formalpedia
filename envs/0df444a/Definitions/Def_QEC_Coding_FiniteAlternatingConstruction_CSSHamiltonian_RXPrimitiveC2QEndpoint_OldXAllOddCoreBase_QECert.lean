-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_OldXAllOddCoreBase_QECert
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_OldXAllOddCoreBase_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T20:36:43.909856+00:00
-- url     : https://prove2.me/theorems/e8cf845b-b3a2-4545-b5fd-08e83bcc602a
-- title:
--   All-odd OldX readout core base
-- statement:
--   Initial exact support lemmas for the all-odd OldX dual-readout proof.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L18360-L18373

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_LiteralPart1_QECert
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
theorem base_faceX_value_OldXCore_QECert (f : BaseFace) :
    baseTannerSquarePresentation.faceX f=baseFaceX f := rfl
theorem base_faceZ_value_OldXCore_QECert (f : BaseFace) :
    baseTannerSquarePresentation.faceZ f=baseFaceZ f := rfl
theorem base_faceQ_value_OldXCore_QECert (f : BaseFace) (c : BDL26FiniteTannerSquare.Two) :
    baseTannerSquarePresentation.faceQ f c=baseFaceQ f c := rfl
theorem base_xq_matrix_value_OldXCore_QECert (x : BaseX) (q : BaseQubit) :
    baseTannerSquarePresentation.xq x q=decide (baseBoundary1Matrix x q≠0) := rfl
theorem base_qz_matrix_value_OldXCore_QECert (q : BaseQubit) (z : BaseZ) :
    baseTannerSquarePresentation.qz q z=decide (baseBoundary2Matrix q z≠0) := rfl
theorem base_X_eq_value_OldXBounded_QECert (x y : baseTannerSquarePresentation.X) :
    x=y ↔ (x : BaseX).val=(y : BaseX).val := @Fin.ext_iff 2 x y
theorem base_Q_eq_value_OldXBounded_QECert (q r : baseTannerSquarePresentation.Q) :
    q=r ↔ (q : BaseQubit).val=(r : BaseQubit).val := @Fin.ext_iff 5 q r
theorem base_Z_eq_value_OldXBounded_QECert (z w : baseTannerSquarePresentation.Z) :
    z=w ↔ (z : BaseZ).val=(w : BaseZ).val := @Fin.ext_iff 2 z w
private theorem base_face_eq_value (f g : baseTannerSquarePresentation.Face) :
    f=g ↔ (f : BaseFace).val=(g : BaseFace).val := @Fin.ext_iff 4 f g
theorem raw_two_eq_value_OldXBounded_QECert (a b : Fin 2) :
    a=b ↔ a.val=b.val := base_Z_eq_value_OldXBounded_QECert a b
theorem raw_four_eq_value_OldXBounded_QECert (a b : Fin 4) :
    a=b ↔ a.val=b.val := base_face_eq_value a b
theorem raw_five_eq_value_OldXBounded_QECert (a b : Fin 5) :
    a=b ↔ a.val=b.val := base_Q_eq_value_OldXBounded_QECert a b
theorem star_edge_xq_view_OldXCore_QECert (P : TannerSquarePresentation) (x : P.X)
    (e : XQEdge P) :
    xStarEdgeMember P x (.inl e)=decide (∃ f : P.Face,
      xStarFaceMember P x f=true ∧ (e=faceXQEdge P f 0 ∨ e=faceXQEdge P f 1)) := by
  change decide (∃ f : P.Face, xStarFaceMember P x f=true ∧
    decide (e=faceXQEdge P f 0 ∨ e=faceXQEdge P f 1)=true)=_
  apply Bool.decide_congr
  simp only [decide_eq_true_eq]
attribute [local simp] basis_value
theorem two_indicators_zero_OldXBounded_QECert {I : Type} (q q0 q1 : I) (c : F)
    (h0 : q≠q0) (h1 : q≠q1) :
    ((if q=q0 then (1:F) else 0)+(if q=q1 then 1 else 0))+c=c := by
  simp only [if_neg h0,if_neg h1,zero_add]
private theorem gradient_two_basis (P : TannerSquarePresentation)
    (u v : P.X) (q : P.Q) :
    tannerCoboundary0 P (canonicalBasisWord (F:=F) u+canonicalBasisWord v) q=
      (if P.xq u q=true then (1:F) else 0)+(if P.xq v q=true then 1 else 0) := by
  calc
    _ = tannerCoboundary0 P (canonicalBasisWord u) q+
        tannerCoboundary0 P (canonicalBasisWord v) q :=
      congrArg (fun w : Word F P.Q => w q) (map_add (tannerCoboundary0 P) _ _)
    _ = _ := congrArg₂ (fun a b : F => a+b)
      (tannerCoboundary0_canonicalBasis_apply P u q)
      (tannerCoboundary0_canonicalBasis_apply P v q)
theorem two_basis_value_OldXBounded_QECert {I : Type} (u v x : I) :
    ((canonicalBasisWord (F:=F) u+canonicalBasisWord (F:=F) v : Word F I)) x=
      (if x=u then 1 else 0)+(if x=v then 1 else 0) := by
  change canonicalBasisWord (F:=F) u x+canonicalBasisWord v x=_
  rw [basis_value,basis_value]
theorem gradient_two_basis_second_OldXCore_QECert (P : TannerSquarePresentation)
    (u v : P.X) (q : P.Q)
    (hu : ¬P.xq u q=true)
    (h : tannerCoboundary0 P
      (canonicalBasisWord (F:=F) u+canonicalBasisWord v) q≠0) :
    P.xq v q=true := by
  rw [gradient_two_basis,if_neg hu,zero_add] at h
  by_contra hv
  rw [if_neg hv] at h
  exact h rfl
theorem word_sum_eval_OldXBounded_QECert {J I : Type} [Fintype J]
    (w : J → Word F I) (i : I) : (∑ j, w j) i=∑ j, w j i := by
  simp only [Finset.sum_apply]
attribute [local simp] word_add_eval word_smul_eval word_zero_eval
theorem code_larger_left_OldXBounded_QECert {I : Type} [Encodable I] (a b : I) :
    Encodable.encode a≤Encodable.encode
      (if Encodable.encode a≤Encodable.encode b then b else a) := by
  by_cases h : Encodable.encode a≤Encodable.encode b
  · rw [if_pos h]; exact h
  · rw [if_neg h]
theorem code_larger_right_OldXBounded_QECert {I : Type} [Encodable I] (a b : I) :
    Encodable.encode b≤Encodable.encode
      (if Encodable.encode a≤Encodable.encode b then b else a) := by
  by_cases h : Encodable.encode a≤Encodable.encode b
  · rw [if_pos h]
  · rw [if_neg h]; exact (Nat.lt_of_not_ge h).le
theorem code_larger_upper_OldXBounded_QECert {I : Type} [Encodable I] (a b : I) (B : Nat)
    (ha : Encodable.encode a≤B) (hb : Encodable.encode b≤B) :
    Encodable.encode (if Encodable.encode a≤Encodable.encode b then b else a)≤B := by
  by_cases h : Encodable.encode a≤Encodable.encode b
  · simpa only [if_pos h] using hb
  · simpa only [if_neg h] using ha
theorem words_cancel_middle_OldXBounded_QECert {I : Type} (a b : Word F I) : a+(b+a)=b := by
  rw [add_left_comm]
  have hz : a+a=0 := by funext i; exact ZModModule.add_self (a i)
  rw [hz,add_zero]
theorem three_words_cancel_OldXBounded_QECert {I : Type} (a b c : Word F I) :
    a+b+((c+a)+(c+b))=0 := by
  have hz (w : Word F I) : w+w=0 := by
    funext i
    exact ZModModule.add_self (w i)
  calc
    _ = (a+a)+((b+b)+(c+c)) := by abel
    _ = 0 := by rw [hz a,hz b,hz c,zero_add,zero_add]
theorem sum_scaled_words_apply_OldXBounded_QECert {J I : Type} [Fintype J]
    (a : J → F) (w : J → Word F I) (q : I) :
    (∑ j, a j • w j) q=∑ j, a j*w j q := by
  erw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rfl
theorem collect_indicator_sums_OldXBounded_QECert {J K I : Type} [Fintype J] [Fintype K]
    (a : J → F) (rel : J → K → Bool) (w : K → Word F I) :
    (∑ j, a j • (∑ k, if rel j k=true then w k else 0))=
      ∑ k, (∑ j, a j*(if rel j k=true then 1 else 0)) • w k := by
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : rel j k=true <;> simp [h]
theorem generic_basis_plus_value_OldXBounded_QECert {I : Type} (q target : I)
    (w : Word F I) (hw : w target=0) :
    ((canonicalBasisWord (F:=F) q+w : Word F I)) target=(if target=q then 1 else 0) := by
  calc
    _ = canonicalBasisWord (F:=F) q target+w target := rfl
    _ = _ := by rw [basis_value,hw,add_zero]
theorem two_units_apply_OldXBounded_QECert {I : Type} (a b q : I) (w : Word F I) :
    ((canonicalBasisWord (F:=F) a+canonicalBasisWord (F:=F) b+w : Word F I)) q=
      ((if q=a then 1 else 0)+(if q=b then 1 else 0))+w q := by
  change canonicalBasisWord (F:=F) a q+canonicalBasisWord (F:=F) b q+w q=_
  rw [basis_value,basis_value]
theorem extend_edge_at_same_OldXBounded_QECert (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (w : Word F (ZDoubleCylinderEdge P z S))
    (e : ZDoubleCylinderEdge P z S) : extendZEdgeWord P S z w (.inl ⟨z,e⟩)=w e := by
  simp [extendZEdgeWord]
theorem extend_edge_at_other_OldXBounded_QECert (P : TannerSquarePresentation) (S : OddScale)
    (z z' : P.Z) (w : Word F (ZDoubleCylinderEdge P z S))
    (e : ZDoubleCylinderEdge P z' S) (h : z'≠z) :
    extendZEdgeWord P S z w (.inl ⟨z',e⟩)=0 := by
  exact dif_neg h
theorem extend_edge_at_port_OldXBounded_QECert (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (w : Word F (ZDoubleCylinderEdge P z S))
    (q : P.Q) (v : QDoubleCylinderVertex (transposePresentation P) q S) :
    extendZEdgeWord P S z w (.inr ⟨q,v⟩)=0 := rfl
theorem conditional_word_sum_apply_OldXBounded_QECert {J I : Type} [Fintype J]
    (condition : J → Prop) [DecidablePred condition]
    (words : ∀ j, condition j → Word F I) (q : I) :
    (∑ j, if h : condition j then words j h else 0) q=
      ∑ j, if h : condition j then words j h q else 0 := by
  erw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : condition j
  · rw [dif_pos h,dif_pos h]
  · simp only [dif_neg h,word_zero_eval]
private theorem map_conditional_word_sum {J I K : Type} [Fintype J]
    (D : Word F I →ₗ[F] Word F K)
    (condition : J → Prop) [DecidablePred condition]
    (words : ∀ j, condition j → Word F I) :
    D (∑ j, if h : condition j then words j h else 0)=
      ∑ j, if h : condition j then D (words j h) else 0 := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [map_zero]
theorem mapped_shifted_sum_cancel_OldXBounded_QECert {J I K : Type} [Fintype J]
    (D : Word F I →ₗ[F] Word F K) (a : Word F I)
    (condition : J → Prop) [DecidablePred condition]
    (words : ∀ j, condition j → Word F I)
    (ends mids locals : ∀ j, condition j → Word F K)
    (ha : D a=∑ j, if h : condition j then ends j h else 0)
    (he : ∀ j h, D (words j h)=(mids j h+ends j h)+locals j h) :
    D (a+∑ j, if h : condition j then words j h else 0)=
      ∑ j, if h : condition j then mids j h+locals j h else 0 := by
  rw [map_add,ha,map_conditional_word_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : condition j
  · rw [dif_pos h,dif_pos h,dif_pos h,he j h]
    calc
      _ = (ends j h+(mids j h+ends j h))+locals j h := by abel
      _ = _ := by rw [words_cancel_middle_OldXBounded_QECert]
  · simp only [dif_neg h,zero_add]
theorem disjoint_conditional_basis_apply_OldXBounded_QECert {J I : Type} [Fintype J]
    (condition : J → Prop) [DecidablePred condition]
    (labels : ∀ j, condition j → I) (q : I)
    (hne : ∀ j h, q≠labels j h) :
    (∑ j, if h : condition j then canonicalBasisWord (F:=F) (labels j h) else 0) q=0 := by
  rw [conditional_word_sum_apply_OldXBounded_QECert condition
    (fun j h => canonicalBasisWord (labels j h)) q]
  apply Finset.sum_eq_zero
  intro j _
  by_cases h : condition j
  · rw [dif_pos h,basis_value,if_neg (hne j h)]
  · rw [dif_neg h]
theorem horizontal_inner_start_grid_OldXBounded_QECert (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x)
    (i : Fin S.half) (k : Fin (S.half-1)) :
    subdivisionEdgeStart P x S (.inr (.inl (f,i,k)))=
      subdivisionGridVertex P x S f (finCastGrid i) (finInteriorGrid S k) := rfl
theorem horizontal_inner_end_grid_OldXBounded_QECert (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x)
    (i : Fin S.half) (k : Fin (S.half-1)) :
    subdivisionEdgeEnd P x S (.inr (.inl (f,i,k)))=
      subdivisionGridVertex P x S f (finSuccGrid i) (finInteriorGrid S k) := rfl
theorem horizontal_inner_eq_OldXBounded_QECert (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (i : Fin S.half)
    (row : Fin (S.half+1)) (h0 : row.val≠0) (hh : row.val≠S.half) :
    subdivisionHorizontalEdge P x S f i row=
      .inr (.inl (f,i,finInteriorIndex S row h0 hh)) := by
  unfold subdivisionHorizontalEdge
  simp only [dif_neg h0,dif_neg hh]
  apply congrArg (fun k : Fin (S.half-1) =>
    (Sum.inr (Sum.inl (f,i,k)) : SubdivisionEdge P x S))
  apply Fin.ext
  rfl
theorem horizontal_last_eq_OldXBounded_QECert (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (i : Fin S.half)
    (row : Fin (S.half+1)) (h : row.val=S.half) :
    subdivisionHorizontalEdge P x S f i row=.inl (xStarFaceQZEdge P x f 1,i) := by
  have h0 : row.val≠0 := by have := S.half_pos; omega
  unfold subdivisionHorizontalEdge
  rw [dif_neg h0,dif_pos h]
theorem vertical_inner_eq_OldXCore_QECert (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (row : Fin (S.half+1))
    (i : Fin S.half) (h0 : row.val≠0) (hh : row.val≠S.half) :
    subdivisionVerticalEdge P x S f row i=
      .inr (.inr (f,finInteriorIndex S row h0 hh,i)) := by
  unfold subdivisionVerticalEdge
  rw [dif_neg h0,dif_neg hh]
  apply congrArg (fun k : Fin (S.half-1) =>
    (Sum.inr (Sum.inr (f,k,i)) : SubdivisionEdge P x S))
  apply Fin.ext
  rfl
private theorem original_support_mem {I : Type} [Fintype I]
    (w : Word F I) (q : I) : q∈hammingSupport w ↔ w q≠0 := by
  simp only [hammingSupport,Finset.mem_filter,Finset.mem_univ,true_and]
theorem seedRadial_start_OldXBounded_QECert (j : Fin 2) :
    xStarEdgeStart _ _ (seedRadial j)=seedCenter := by fin_cases j <;> rfl
private theorem radialPath_support (S : OddScale) (j : Fin 2) (n : Nat)
    (hn : n≤S.half) (e : DoubleCylinderEdge baseTannerSquarePresentation (0 : BaseX) S)
    (he : pathChain (radialPath S j n hn) e≠0) :
    ∃ i : Fin S.half, e=.inl (0,.inl (seedRadial j,i)) := by
  revert hn
  induction n with
  | zero =>
    intro hn he
    simp [radialPath,pathChain] at he
  | succ n ih =>
    intro hn he
    let i : Fin S.half := ⟨n,by omega⟩
    have hs : pathChain (radialPath S j (n+1) hn)=
        pathChain (radialPath S j n (by omega))+
          Pi.single (.inl (0,.inl (seedRadial j,i))) (1:F) := rfl
    rw [hs,Pi.add_apply] at he
    by_cases hp : pathChain (radialPath S j n (by omega)) e=0
    · rw [hp,zero_add,Pi.single_apply] at he
      by_cases heq : e=.inl (0,.inl (seedRadial j,i))
      · exact ⟨i,heq⟩
      · exact False.elim (he (if_neg heq))
    · exact ih (by omega) hp
theorem rawDualReadout_zero_OldXCore_QECert (S : OddScale) (w : Word F (RawOne S).Q)
    (h0 : w (.inr ⟨(0 : BaseQubit),(0,.inl (.inl ()))⟩)=0)
    (h1 : w (.inr ⟨(1 : BaseQubit),(0,.inl (.inl ()))⟩)=0)
    (hpath : ∀ (j : Fin 2) (i : Fin S.half),
      w (.inl ⟨(0 : BaseX),.inl (0,.inl (seedRadial j,i))⟩)=0) :
    rawDualReadout S w=0 := by
  have hp (j : Fin 2) : wordPairing (radialChain S j)
      (fun e => w (.inl ⟨(0 : BaseX),e⟩))=0 := by
    change (∑ e, radialChain S j e*w (.inl ⟨(0 : BaseX),e⟩))=0
    apply Finset.sum_eq_zero
    intro e _
    by_cases he : radialChain S j e=0
    · rw [he,zero_mul]
    · obtain ⟨i,rfl⟩ := radialPath_support S j S.half (Nat.le_refl _) e he
      exact (congrArg (fun v : F =>
        radialChain S j (.inl (0,.inl (seedRadial j,i)))*v) (hpath j i)).trans
        (mul_zero _)
  change w (.inr ⟨(0 : BaseQubit),(0,.inl (.inl ()))⟩)+
    w (.inr ⟨(1 : BaseQubit),(0,.inl (.inl ()))⟩)+
    wordPairing (radialChain S 0+radialChain S 1)
      (fun e => w (.inl ⟨(0 : BaseX),e⟩))=0
  rw [h0,h1,map_add,LinearMap.add_apply,hp,hp]
  simp
theorem seed_cone_gradient_OldXBounded_QECert (S : OddScale) (j : Fin 2)
    (p : Word F (RX0 baseTannerSquarePresentation S)) :
    BDL26ReplacementCochainMaps.rxCoboundary0 baseTannerSquarePresentation S p
      (.inr ⟨seedQ j,(0,.inl (.inl ()))⟩)=p ⟨0,(0,.inl (seedQVertex j))⟩ := by
  unfold BDL26ReplacementCochainMaps.rxCoboundary0 rxBoundary1
  rw [wordLinearMapTranspose_toLin'_apply]
  simp_rw [seed_cone_incidence]
  simp
private theorem differential0_heq {U V : TannerSquarePresentation} (h : U=V) :
    HEq (tannerCoboundary0 U) (tannerCoboundary0 V) := by cases h; exact HEq.rfl
private theorem encoded_coordinates_strict {I : Type} [Fintype I] [Encodable I] :
    (BDL26LevelTwoDecoder.coordinates I).Pairwise
      (fun a b => Encodable.encode a<Encodable.encode b) := by
  letI : LinearOrder I := LinearOrder.lift' Encodable.encode Encodable.encode_injective
  have hs : (BDL26LevelTwoDecoder.coordinates I).Pairwise
      (fun a b => Encodable.encode a≤Encodable.encode b) := by
    change (Finset.univ.sort (· ≤ ·) : List I).Pairwise (· ≤ ·)
    exact Finset.pairwise_sort _ _
  have hn : (BDL26LevelTwoDecoder.coordinates I).Nodup := by
    change (Finset.univ.sort (· ≤ ·) : List I).Nodup
    exact Finset.sort_nodup _ _
  have hi (xs : List I) (hs : xs.Pairwise (fun a b => Encodable.encode a≤Encodable.encode b))
      (hn : xs.Nodup) : xs.Pairwise (fun a b => Encodable.encode a<Encodable.encode b) := by
    revert hs hn
    induction xs with
    | nil => intro hs hn; exact List.Pairwise.nil
    | cons a xs ih =>
      intro hs hn
      apply List.pairwise_cons.mpr
      constructor
      · intro b hb
        have hle := (List.pairwise_cons.mp hs).1 b hb
        have hne : Encodable.encode a≠Encodable.encode b := by
          intro he
          have hab := Encodable.encode_injective he
          exact (List.nodup_cons.mp hn).1 (hab.symm ▸ hb)
        omega
      · exact ih (List.pairwise_cons.mp hs).2 (List.nodup_cons.mp hn).2
  exact hi _ hs hn
private theorem before_add_of_encoded_kernel {I : Type} [Encodable I]
    (xs : List I) (hs : xs.Pairwise (fun a b => Encodable.encode a<Encodable.encode b))
    (q : I) (hm : q∈xs) (r k : Word F I)
    (hp : ∀ i, Encodable.encode i<Encodable.encode q → k i=0)
    (hq : k q=1) (hr : r q=1) : BDL26GlobalLookupLinearity.Before xs (r+k) r := by
  revert hs hm
  induction xs with
  | nil => intro hs hm; cases hm
  | cons a xs ih =>
    intro hs hm
    by_cases ha : a=q
    · subst a
      apply Or.inl
      refine ⟨?_,hr⟩
      change r q+k q=0
      rw [hr,hq]
      exact ZModModule.add_self _
    · have hmem : q∈xs := (List.mem_cons.mp hm).resolve_left (Ne.symm ha)
      have hlt := (List.pairwise_cons.mp hs).1 q hmem
      apply Or.inr
      constructor
      · change r a+k a=r a
        rw [hp a hlt,add_zero]
      · exact ih (List.pairwise_cons.mp hs).2 hmem
theorem global_zero_of_encoded_kernel_OldXBounded_QECert {I J : Type} [Fintype I]
    [DecidableEq I] [Encodable I] [Fintype J] [DecidableEq J]
    (L : Word F I →ₗ[F] Word F J) (a : Word F I) (q : I)
    (k : Word F I) (hk : L k=0)
    (hp : ∀ i, Encodable.encode i<Encodable.encode q → k i=0) (hq : k q=1) :
    BDL26GlobalLookupLinearity.G L (L a) q=0 := by
  let r := BDL26GlobalLookupLinearity.G L (L a)
  rcases BDL26RXQEdgePairTransport.bit_cases (r q) with hz | ho
  · exact hz
  · have hpre : L r=L a := BDL26GlobalLookupLinearity.global_preimage L _ ⟨a,rfl⟩
    have hsum : L (r+k)=L a := by rw [map_add,hpre,hk,add_zero]
    have hmin := BDL26GlobalLookupLinearity.global_minimal L (L a) ⟨a,rfl⟩ (r+k) hsum
    exact False.elim (hmin (before_add_of_encoded_kernel _ encoded_coordinates_strict
      q (BDL26LevelTwoDecoder.mem_coordinates I q) r k hp hq ho))
private theorem cast_rz_radial_image (S : OddScale) {P Q : TannerSquarePresentation}
    (h : P=Q) (A : TannerSquareAdmissible Q) (r : Q.Q) (x : Q.X)
    (hx : Q.xq x r=true) (z : Q.Z) (hz : Q.qz r z=true)
    (c : BDL26FiniteTannerSquare.Two) (i : Fin S.half) :
    cast (congrArg (fun P => RZQ P S) h).symm
      (.inl ⟨z,qToZDoubleCylinderEdge Q A r z hz S (.inl (c,(⟨x,hx⟩,i)))⟩)=
    .inl ⟨cast (congrArg TannerSquarePresentation.Z h).symm z,
      qToZDoubleCylinderEdge P (h.symm ▸ A)
        (cast (congrArg TannerSquarePresentation.Q h).symm r)
        (cast (congrArg TannerSquarePresentation.Z h).symm z)
        (cast_qz h r z hz) S
        (.inl (c,(⟨cast (congrArg TannerSquarePresentation.X h).symm x,
          cast_xq h r x hx⟩,i)))⟩ := by
  cases h
  rfl
private theorem encoded_radial_image (S : OddScale) (r : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (z : (RawOne S).Z) (hz : (RawOne S).qz r z=true)
    (c : BDL26FiniteTannerSquare.Two) (i : Fin S.half) :
    Encodable.encode (executableCoordinate S
      (.inl ⟨z,qToZDoubleCylinderEdge (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible
        r z hz S (.inl (c,(⟨x,hx⟩,i)))⟩))=
      2*Nat.pair
        (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
        (2*Nat.pair c.val
          (2*Nat.pair
            (2*Nat.pair
              (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
              (Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X))+1)
            i.val)) := by
  change Encodable.encode (cast (congrArg (fun P => RZQ P S)
      (executableLevelOne_eq_raw S)).symm _) = _
  erw [cast_rz_radial_image S (executableLevelOne_eq_raw S)
    (rxState S baseState).admissible.toTannerSquareAdmissible r x hx z hz c i]
  rfl
private theorem cast_rz_endpoint (S : OddScale) {P Q : TannerSquarePresentation}
    (h : P=Q) (r : Q.Q) (x : Q.X) (hx : Q.xq x r=true)
    (c : BDL26FiniteTannerSquare.Two) :
    cast (congrArg (fun P => RZQ P S) h).symm
      (.inr ⟨r,(c,.inl (.inr ⟨x,hx⟩))⟩)=
    .inr ⟨cast (congrArg TannerSquarePresentation.Q h).symm r,
      (c,.inl (.inr ⟨cast (congrArg TannerSquarePresentation.X h).symm x,
        cast_xq h r x hx⟩))⟩ := by
  cases h
  rfl
private theorem cast_rz_interior (S : OddScale) {P Q : TannerSquarePresentation}
    (h : P=Q) (r : Q.Q) (x : Q.X) (hx : Q.xq x r=true)
    (c : BDL26FiniteTannerSquare.Two) (i : Fin (S.half-1)) :
    cast (congrArg (fun P => RZQ P S) h).symm
      (.inr ⟨r,(c,.inr (⟨x,hx⟩,i))⟩)=
    .inr ⟨cast (congrArg TannerSquarePresentation.Q h).symm r,
      (c,.inr (⟨cast (congrArg TannerSquarePresentation.X h).symm x,
        cast_xq h r x hx⟩,i))⟩ := by
  cases h
  rfl
theorem encoded_endpoint_OldXCore_QECert (S : OddScale) (r : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (c : BDL26FiniteTannerSquare.Two) :
    Encodable.encode (executableCoordinate S (.inr ⟨r,(c,.inl (.inr ⟨x,hx⟩))⟩))=
      2*Nat.pair
        (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
        (Nat.pair c.val
          (2*(2*Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)+1)))+1 := by
  change Encodable.encode (cast (congrArg (fun P => RZQ P S)
      (executableLevelOne_eq_raw S)).symm _) = _
  erw [cast_rz_endpoint S (executableLevelOne_eq_raw S) r x hx c]
  rfl
theorem encoded_interior_OldXBounded_QECert (S : OddScale) (r : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (c : BDL26FiniteTannerSquare.Two) (i : Fin (S.half-1)) :
    Encodable.encode (executableCoordinate S (.inr ⟨r,(c,.inr (⟨x,hx⟩,i))⟩))=
      2*Nat.pair
        (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
        (Nat.pair c.val
          (2*Nat.pair
            (Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)) i.val+1))+1 := by
  change Encodable.encode (cast (congrArg (fun P => RZQ P S)
      (executableLevelOne_eq_raw S)).symm _) = _
  erw [cast_rz_interior S (executableLevelOne_eq_raw S) r x hx c i]
  rfl
theorem q_before_local_code_OldXBounded_QECert (r z u v : Nat)
    (c : BDL26FiniteTannerSquare.Two) (huv : u<v)
    (hr : r<2*Nat.pair c.val v) :
    2*Nat.pair r (Nat.pair c.val u)+1 <
      2*Nat.pair z (2*Nat.pair c.val v) := by
  have htail := Nat.pair_lt_pair_right c.val huv
  have hmax : max r (Nat.pair c.val u)+1≤2*Nat.pair c.val v := by omega
  have hup := Nat.pair_lt_max_add_one_sq r (Nat.pair c.val u)
  have hlow := Nat.max_sq_add_min_le_pair z (2*Nat.pair c.val v)
  have hsq := Nat.pow_le_pow_left
    (hmax.trans (Nat.le_max_right z (2*Nat.pair c.val v))) 2
  omega
private theorem interior_before_later_radial_code (r r' x z j k : Nat)
    (c : BDL26FiniteTannerSquare.Two) (hrr : r≤r') (hjk : j<k) :
    2*Nat.pair r (Nat.pair c.val (2*Nat.pair x j+1))+1 <
      2*Nat.pair z
        (2*Nat.pair c.val (2*Nat.pair (2*Nat.pair r' x+1) k)) := by
  have hx := Nat.right_le_pair r' x
  have hr := Nat.left_le_pair r' x
  have hfirst : x<2*Nat.pair r' x+1 := by omega
  have hsub := Nat.pair_lt_pair_left j hfirst
  have hsub' := Nat.pair_lt_pair_right (2*Nat.pair r' x+1) hjk
  have huv : 2*Nat.pair x j+1<2*Nat.pair (2*Nat.pair r' x+1) k := by omega
  have htail := Nat.left_le_pair (2*Nat.pair r' x+1) k
  have hout := Nat.right_le_pair c.val (2*Nat.pair (2*Nat.pair r' x+1) k)
  apply q_before_local_code_OldXBounded_QECert _ _ _ _ c huv
  omega
theorem interior_before_grid_code_OldXCore_QECert (r x z f i a b tag : Nat)
    (c : BDL26FiniteTannerSquare.Two) (hri : r< i) (hxi : x< i)
    (hi : i≤ max a b) (htag : 1≤tag) :
    2*Nat.pair r (Nat.pair c.val (2*Nat.pair x i+1))+1 <
      2*Nat.pair z (2*Nat.pair c.val (4*Nat.pair f (Nat.pair a b)+tag)) := by
  have hp : Nat.pair x i=i*i+x := by simp [Nat.pair,hxi]
  have hsq := Nat.pow_le_pow_left hi 2
  have hlow := Nat.max_sq_add_min_le_pair a b
  have hright := Nat.right_le_pair f (Nat.pair a b)
  have hiP : i^2≤Nat.pair f (Nat.pair a b) :=
    hsq.trans (((Nat.le_add_right ((max a b)^2) (min a b)).trans hlow).trans hright)
  have hiP' : i≤Nat.pair f (Nat.pair a b) :=
    (Nat.le_self_pow (by decide) i).trans hiP
  have huv : 2*Nat.pair x i+1<4*Nat.pair f (Nat.pair a b)+tag := by
    rw [hp]
    have hisq : i*i≤Nat.pair f (Nat.pair a b) := by simpa only [pow_two] using hiP
    have hxP : x+1≤Nat.pair f (Nat.pair a b) := (Nat.succ_le_of_lt hxi).trans hiP'
    omega
  have htail := Nat.right_le_pair c.val (4*Nat.pair f (Nat.pair a b)+tag)
  apply q_before_local_code_OldXBounded_QECert _ _ _ _ c huv
  omega
theorem encoded_interior_lt_OldXBounded_QECert (S : OddScale) (r r' : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (hx' : (RawOne S).xq x r'=true) (c : BDL26FiniteTannerSquare.Two)
    (i : Fin (S.half-1))
    (hlt : Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)<
      Encodable.encode (r' : (BDL26LevelTwoDecoder.executableLevelOne S).Q)) :
    Encodable.encode (executableCoordinate S (.inr ⟨r,(c,.inr (⟨x,hx⟩,i))⟩))<
      Encodable.encode (executableCoordinate S (.inr ⟨r',(c,.inr (⟨x,hx'⟩,i))⟩)) := by
  have hp := Nat.pair_lt_pair_left
    (Nat.pair c.val (2*Nat.pair
      (Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)) i.val+1)) hlt
  have hn : 2*Nat.pair
      (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
      (Nat.pair c.val (2*Nat.pair
        (Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)) i.val+1))+1 <
      2*Nat.pair (Encodable.encode (r' : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
      (Nat.pair c.val (2*Nat.pair
        (Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)) i.val+1))+1 := by omega
  exact (encoded_interior_OldXBounded_QECert S r x hx c i).trans_lt
    (hn.trans_eq (encoded_interior_OldXBounded_QECert S r' x hx' c i).symm)
theorem encoded_interior_before_radial_OldXBounded_QECert (S : OddScale)
    (r r' : (RawOne S).Q) (x : (RawOne S).X)
    (hx : (RawOne S).xq x r=true) (hx' : (RawOne S).xq x r'=true)
    (z : (RawOne S).Z) (hz : (RawOne S).qz r' z=true)
    (c : BDL26FiniteTannerSquare.Two) (i : Fin (S.half-1)) (k : Fin S.half)
    (hrr : Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)≤
      Encodable.encode (r' : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
    (hik : i.val<k.val) :
    Encodable.encode (executableCoordinate S (.inr ⟨r,(c,.inr (⟨x,hx⟩,i))⟩))<
      Encodable.encode (executableCoordinate S (.inl ⟨z,qToZDoubleCylinderEdge (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible r' z hz S
        (.inl (c,(⟨x,hx'⟩,k)))⟩)) := by
  have hn := interior_before_later_radial_code
    (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
    (Encodable.encode (r' : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
    (Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X))
    (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
    i.val k.val c hrr hik
  exact (encoded_interior_OldXBounded_QECert S r x hx c i).trans_lt
    (hn.trans_eq (encoded_radial_image S r' x hx' z hz c k).symm)
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
end
end


