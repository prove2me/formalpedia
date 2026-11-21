-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_OldXAllOddCoreFirstCutHead_QECert
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_OldXAllOddCoreFirstCutHead_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T22:10:58.918974+00:00
-- url     : https://prove2.me/theorems/9eee9fff-e0dd-4b24-b6e8-977066b3eb9c
-- title:
--   All-odd OldX first-cut Head
-- statement:
--   Exact first-cut support lemmas for the all-odd OldX proof.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L18360-L18373

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_OldXAllOddCorePorts_QECert
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
private theorem two_basis_value_with_decisions {I : Type} (u v x : I)
    (du : Decidable (x=u)) (dv : Decidable (x=v)) :
    ((canonicalBasisWord (F:=F) u+canonicalBasisWord v : Word F I)) x=
      @ite F (x=u) du 1 0+@ite F (x=v) dv 1 0 := by
  have h := two_basis_value_OldXBounded_QECert u v x
  exact h.trans (congrArg₂ (fun a b : F => a+b)
    (@indicator_iff (x=u) (x=u) (Classical.propDecidable _) du Iff.rfl)
    (@indicator_iff (x=v) (x=v) (Classical.propDecidable _) dv Iff.rfl))
private theorem halfOneTinyPotential_value (S : OddScale)
    (x : RX0 baseTannerSquarePresentation S) :
    halfOneTinyPotential S x=
      (if x=⟨(0 : BaseX),(0,.inl seedCenter)⟩ then (1:F) else 0)+
      (if x=⟨(0 : BaseX),(0,.inl (seedQVertex 0))⟩ then 1 else 0) := by
  change ((canonicalBasisWord (F:=F)
      (⟨(0 : BaseX),(0,.inl seedCenter)⟩ : RX0 baseTannerSquarePresentation S)+
    canonicalBasisWord (F:=F)
      (⟨(0 : BaseX),(0,.inl (seedQVertex 0))⟩ : RX0 baseTannerSquarePresentation S) :
        Word F (RX0 baseTannerSquarePresentation S)) x)=_
  exact two_basis_value_with_decisions _ _ x _ _
theorem halfOneTinyPotential_local_value_OldXCore_QECert (S : OddScale) (x : BaseX)
    (c : BDL26FiniteTannerSquare.Two)
    (v : SubdivisionVertex baseTannerSquarePresentation x S) :
    halfOneTinyPotential S ⟨x,(c,v)⟩=
      if x.val=0 ∧ c.val=0 then
        match v with
        | .inl node => match node.val with
            | .x y => if y.val=0 then (1:F) else 0
            | .q q => if q.val=0 then 1 else 0
            | .z _ => 0
        | .inr _ => 0
      else 0 := by
  have hvalue := halfOneTinyPotential_value S
    (⟨x,(c,v)⟩ : RX0 baseTannerSquarePresentation S)
  have h0 := old_X_coordinate_eq_OldXBounded_QECert S x (0 : BaseX) c 0 v (.inl seedCenter)
  have h1 := old_X_coordinate_eq_OldXBounded_QECert S x (0 : BaseX) c 0 v (.inl (seedQVertex 0))
  have hn : halfOneTinyPotential S ⟨x,(c,v)⟩=
      (if x=(0 : BaseX) ∧ c=0 ∧ HEq v (.inl seedCenter : SubdivisionVertex baseTannerSquarePresentation (0 : BaseX) S) then (1:F) else 0)+
      (if x=(0 : BaseX) ∧ c=0 ∧ HEq v (.inl (seedQVertex 0) : SubdivisionVertex baseTannerSquarePresentation (0 : BaseX) S) then 1 else 0) := by
    exact hvalue.trans (congrArg₂ (fun a b : F => a+b)
      (indicator_iff _ _ h0) (indicator_iff _ _ h1))
  rw [hn]
  by_cases hx : x=(0 : BaseX)
  · subst x
    by_cases hc : c=0
    · subst c
      rcases v with ⟨v,hv⟩ | ⟨⟨edge,he⟩,i⟩ | ⟨f,i,k⟩
      · cases v with
        | x y =>
            simp [seedCenter,seedQVertex,seedQ,heq_eq_eq,Subtype.ext_iff,
              base_X_eq_value_OldXBounded_QECert,Fin.ext_iff]
            have hz : ((0 : baseTannerSquarePresentation.X) : BaseX).val=0 := rfl
            simpa only [hz]
        | q q =>
            simp [seedCenter,seedQVertex,seedQ,heq_eq_eq,Subtype.ext_iff,
              base_Q_eq_value_OldXBounded_QECert,Fin.ext_iff]
            apply indicator_iff
            constructor
            · intro h
              have hq : q=(0 : BaseQubit) := Vertex.q.inj h
              exact congrArg (fun r : BaseQubit => r.val) hq
            · intro h
              have hq : q=(0 : BaseQubit) := Fin.ext h
              exact congrArg (fun r : baseTannerSquarePresentation.Q =>
                (Vertex.q r : Vertex baseTannerSquarePresentation)) hq
        | z z =>
            simp [seedCenter,seedQVertex,seedQ,heq_eq_eq,Subtype.ext_iff]
      · simp [heq_eq_eq]
      · simp [heq_eq_eq]
    · have hcv : c.val≠0 := by
        intro h
        exact hc (Fin.ext h)
      simp only [hc,false_and,and_false,if_false,zero_add,Fin.val_zero,hcv]
  · have hxv : x.val≠0 := by
      intro h
      exact hx (Fin.ext h)
    simp only [hx,false_and,if_false,zero_add,hxv]
theorem halfOneTinyKernel_closed_OldXCore_QECert (S : OddScale) :
    tannerCoboundary1 (RawOne S) (halfOneTinyKernel S)=0 := by
  have h := LinearMap.congr_fun
    (BDL26LevelTwoDistance.tannerCoboundary_squared (RawOne S))
    (halfOneTinyPotential S)
  exact h
theorem halfOneTinyKernel_target_OldXCore_QECert (S : OddScale) :
    halfOneTinyKernel S (.inr ⟨seedQ 0,(0,.inl (.inl ()))⟩)=1 := by
  erw [halfOneTinyKernel,
    BDL26RXLocalReplacement.rxPresentation_coboundary0_eq
      baseTannerSquarePresentation baseTannerSquareAdmissibleV4
      baseTannerSquareCellularRegular S,
    seed_cone_gradient_OldXBounded_QECert]
  change ((canonicalBasisWord (F:=F)
    (⟨(0 : BaseX),(0,.inl seedCenter)⟩ : (RawOne S).X)+
    canonicalBasisWord (F:=F)
    (⟨(0 : BaseX),(0,.inl (seedQVertex 0))⟩ : (RawOne S).X)) :
    Word F (RawOne S).X) ⟨(0 : BaseX),(0,.inl (seedQVertex 0))⟩=1
  rw [word_add_eval,basis_value,basis_value]
  have hne : (⟨(0 : BaseX),(0,Sum.inl (seedQVertex 0))⟩ : (RawOne S).X)≠
      ⟨(0 : BaseX),(0,Sum.inl seedCenter)⟩ := by
    intro h
    have hv := congrArg Prod.snd (sigma_same_index_inj _ _ h)
    have hvertex := congrArg Subtype.val (Sum.inl.inj hv)
    cases hvertex
  simp only [if_neg hne,if_pos rfl,if_true,zero_add]
theorem firstCutOldKernel_closed_OldXCore_QECert (S : OddScale) :
    tannerCoboundary1 (RawOne S) (firstCutOldKernel S)=0 := by
  have hrx := LinearMap.congr_fun
    (BDL26ReplacementCochainMaps.rxMap_commutes_coboundary1
      baseTannerSquarePresentation S) (stripSeedCocycle 1)
  change BDL26ReplacementCochainMaps.rxCoboundary1 baseTannerSquarePresentation S
      (BDL26ReplacementCochainMaps.rxMap1Coord baseTannerSquarePresentation S
        (stripSeedCocycle 1))=
    BDL26ReplacementCochainMaps.rxMap2Coord baseTannerSquarePresentation S
      (tannerCoboundary1 baseTannerSquarePresentation (stripSeedCocycle 1)) at hrx
  rw [stripSeedCocycle_closed_OldXBounded_QECert,map_zero] at hrx
  have hmap : tannerCoboundary1 (RawOne S)
      (BDL26ReplacementCochainMaps.rxMap1Coord baseTannerSquarePresentation S
        (stripSeedCocycle 1))=0 := by
    erw [BDL26RXLocalReplacement.rxPresentation_coboundary1_eq
      baseTannerSquarePresentation baseTannerSquareAdmissibleV4
      baseTannerSquareCellularRegular S]
    exact hrx
  have hb := LinearMap.congr_fun
    (BDL26LevelTwoDistance.tannerCoboundary_squared (RawOne S)) (firstCutPotential S)
  change tannerCoboundary1 (RawOne S)
    (tannerCoboundary0 (RawOne S) (firstCutPotential S))=0 at hb
  have hmap' : tannerCoboundary1 (RawOne S) (rawSeedLift S 1)=0 := hmap
  exact linear_word_add_zero_OldXBounded_QECert (tannerCoboundary1 (RawOne S))
    (rawSeedLift S 1) (tannerCoboundary0 (RawOne S) (firstCutPotential S)) hmap' hb
private theorem firstCutMember_face_x (S : OddScale) (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) :
    firstCutMember x S (.inl (xStarFaceXVertex _ _ f))=false := rfl
private theorem firstCutMember_face_q (S : OddScale) (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) (c : BDL26FiniteTannerSquare.Two) :
    firstCutMember x S (.inl (xStarFaceQVertex _ _ f c))=
      decide (f=stripFace 1 x ∧ c=0) := by
  dsimp only [firstCutMember,xStarFaceQVertex]
  apply Bool.decide_congr
  obtain ⟨k,rfl⟩ := base_star_face_cases_OldXBounded_QECert x f
  dsimp only [stripFace,stripQ,XStarFace,TannerSquarePresentation.X,
    TannerSquarePresentation.Q,TannerSquarePresentation.Z,TannerSquarePresentation.Face,
    TannerSquarePresentation.faceX,TannerSquarePresentation.faceQ,TannerSquarePresentation.faceZ,
    TannerSquarePresentation.xq,TannerSquarePresentation.qz,
    baseTannerSquarePresentation,baseTannerSquareData,baseZeroX,
    BaseX,BaseQubit,BaseZ,BaseFace,BDL26FiniteTannerSquare.Two] at *
  fin_cases x <;> fin_cases k <;> fin_cases c
  all_goals
    norm_num [baseFaceQ,baseFaceZ,Subtype.ext_iff,
      raw_two_eq_value_OldXBounded_QECert,raw_four_eq_value_OldXBounded_QECert,raw_five_eq_value_OldXBounded_QECert,
      Fin.val_mk,Fin.val_zero,Fin.val_one]
  all_goals first | rfl | omega
private theorem firstCutMember_face_z (S : OddScale) (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) :
    firstCutMember x S (.inl (xStarFaceZVertex _ _ f))=
      decide (f=stripFace 1 x) := by
  dsimp only [firstCutMember,xStarFaceZVertex]
  apply Bool.decide_congr
  obtain ⟨k,rfl⟩ := base_star_face_cases_OldXBounded_QECert x f
  dsimp only [stripFace,stripQ,XStarFace,TannerSquarePresentation.X,
    TannerSquarePresentation.Q,TannerSquarePresentation.Z,TannerSquarePresentation.Face,
    TannerSquarePresentation.faceX,TannerSquarePresentation.faceQ,TannerSquarePresentation.faceZ,
    TannerSquarePresentation.xq,TannerSquarePresentation.qz,
    baseTannerSquarePresentation,baseTannerSquareData,baseZeroX,
    BaseX,BaseQubit,BaseZ,BaseFace,BDL26FiniteTannerSquare.Two] at *
  fin_cases x <;> fin_cases k
  all_goals
    norm_num [baseFaceQ,baseFaceZ,Subtype.ext_iff,
      raw_two_eq_value_OldXBounded_QECert,raw_four_eq_value_OldXBounded_QECert,raw_five_eq_value_OldXBounded_QECert,
      Fin.val_mk,Fin.val_zero,Fin.val_one]
  all_goals first | rfl | omega
private theorem firstCutMember_face_xq (S : OddScale) (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) (c : BDL26FiniteTannerSquare.Two)
    (i : Fin (S.half-1)) :
    firstCutMember x S (.inr (.inl (xStarFaceXQEdge _ _ f c,i)))=
      decide (f=stripFace 1 x ∧ c=0) := by
  dsimp only [firstCutMember,xStarFaceXQEdge,faceXQEdge]
  apply Bool.decide_congr
  obtain ⟨k,rfl⟩ := base_star_face_cases_OldXBounded_QECert x f
  dsimp only [stripFace,stripQ,XStarFace,TannerSquarePresentation.X,
    TannerSquarePresentation.Q,TannerSquarePresentation.Z,TannerSquarePresentation.Face,
    TannerSquarePresentation.faceX,TannerSquarePresentation.faceQ,TannerSquarePresentation.faceZ,
    TannerSquarePresentation.xq,TannerSquarePresentation.qz,
    baseTannerSquarePresentation,baseTannerSquareData,baseZeroX,
    BaseX,BaseQubit,BaseZ,BaseFace,BDL26FiniteTannerSquare.Two] at *
  fin_cases x <;> fin_cases k <;> fin_cases c
  all_goals
    norm_num [baseFaceQ,baseFaceZ,Subtype.ext_iff,
      raw_two_eq_value_OldXBounded_QECert,raw_four_eq_value_OldXBounded_QECert,raw_five_eq_value_OldXBounded_QECert,
      Fin.val_mk,Fin.val_zero,Fin.val_one]
  all_goals first | rfl | omega
private theorem firstCutMember_face_qz (S : OddScale) (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) (c : BDL26FiniteTannerSquare.Two)
    (i : Fin (S.half-1)) :
    firstCutMember x S (.inr (.inl (xStarFaceQZEdge _ _ f c,i)))=
      decide (f=stripFace 1 x) := by
  dsimp only [firstCutMember,xStarFaceQZEdge,faceQZEdge]
  apply Bool.decide_congr
  obtain ⟨k,rfl⟩ := base_star_face_cases_OldXBounded_QECert x f
  dsimp only [stripFace,stripQ,XStarFace,TannerSquarePresentation.X,
    TannerSquarePresentation.Q,TannerSquarePresentation.Z,TannerSquarePresentation.Face,
    TannerSquarePresentation.faceX,TannerSquarePresentation.faceQ,TannerSquarePresentation.faceZ,
    TannerSquarePresentation.xq,TannerSquarePresentation.qz,
    baseTannerSquarePresentation,baseTannerSquareData,baseZeroX,
    BaseX,BaseQubit,BaseZ,BaseFace,BDL26FiniteTannerSquare.Two] at *
  fin_cases x <;> fin_cases k <;> fin_cases c
  all_goals
    norm_num [baseFaceQ,baseFaceZ,Subtype.ext_iff,
      raw_two_eq_value_OldXBounded_QECert,raw_four_eq_value_OldXBounded_QECert,raw_five_eq_value_OldXBounded_QECert,
      Fin.val_mk,Fin.val_zero,Fin.val_one]
  all_goals first | rfl | omega
private theorem firstCutMember_face_cell (S : OddScale) (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) (i k : Fin (S.half-1)) :
    firstCutMember x S (.inr (.inr (f,i,k)))=decide (f=stripFace 1 x) := rfl
private theorem firstCutMember_grid (S : OddScale) (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) (a b : Fin (S.half+1)) :
    firstCutMember x S (subdivisionGridVertex baseTannerSquarePresentation x S f a b)=
      decide (f=stripFace 1 x ∧ a.val≠0) := by
  have hm : S.half≠0 := S.half_pos.ne'
  have h01 : (0 : BDL26FiniteTannerSquare.Two)≠1 := by decide
  have h10 : (1 : BDL26FiniteTannerSquare.Two)≠0 := by decide
  by_cases hf : f=stripFace 1 x
  all_goals erw [grid_vertex_view_OldXBounded_QECert]
  all_goals split_ifs
  all_goals simp_all only [firstCutMember_face_x,firstCutMember_face_q,firstCutMember_face_z,
    firstCutMember_face_xq,firstCutMember_face_qz,firstCutMember_face_cell,hm,Ne.symm hm,h01,h10,
    true_and,false_and,and_true,and_false,decide_true,decide_false,
    Bool.false_eq_true,Bool.true_eq_false,not_true_eq_false,not_false_eq_true]
  all_goals simp_all
theorem firstCutOldKernel_horizontal_OldXCore_QECert (S : OddScale)
    (x : BaseX) (c : BDL26FiniteTannerSquare.Two)
    (f : XStarFace baseTannerSquarePresentation x) (i : Fin S.half)
    (row : Fin (S.half+1)) :
    firstCutOldKernel S (.inl ⟨x,.inl (c,
      subdivisionHorizontalEdge baseTannerSquarePresentation x S f i row)⟩)=
      if f=stripFace 1 x ∧ i.val=0 then 1 else 0 := by
  erw [firstCutOldKernel,Pi.add_apply,rawSeedLift,
    BDL26ReplacementCochainMaps.rxMap1Coord_localEdge,zero_add,rx_local_gradient]
  change (if firstCutMember x S (subdivisionEdgeStart baseTannerSquarePresentation x S
      (subdivisionHorizontalEdge baseTannerSquarePresentation x S f i row)) then
      (1:F) else 0)+
    (if firstCutMember x S (subdivisionEdgeEnd baseTannerSquarePresentation x S
      (subdivisionHorizontalEdge baseTannerSquarePresentation x S f i row)) then
      (1:F) else 0)=_
  erw [own_horizontal_start,own_horizontal_end,
    firstCutMember_grid,firstCutMember_grid]
  by_cases hf : f=stripFace 1 x <;> by_cases hi : i.val=0
  all_goals simp [finCastGrid,finSuccGrid,hf,hi,ZModModule.add_self]
theorem firstCutOldKernel_vertical_OldXCore_QECert (S : OddScale)
    (x : BaseX) (c : BDL26FiniteTannerSquare.Two)
    (f : XStarFace baseTannerSquarePresentation x) (column : Fin (S.half+1))
    (i : Fin S.half) :
    firstCutOldKernel S (.inl ⟨x,.inl (c,
      subdivisionVerticalEdge baseTannerSquarePresentation x S f column i)⟩)=0 := by
  erw [firstCutOldKernel,Pi.add_apply,rawSeedLift,
    BDL26ReplacementCochainMaps.rxMap1Coord_localEdge,zero_add,rx_local_gradient]
  change (if firstCutMember x S (subdivisionEdgeStart baseTannerSquarePresentation x S
      (subdivisionVerticalEdge baseTannerSquarePresentation x S f column i)) then
      (1:F) else 0)+
    (if firstCutMember x S (subdivisionEdgeEnd baseTannerSquarePresentation x S
      (subdivisionVerticalEdge baseTannerSquarePresentation x S f column i)) then
      (1:F) else 0)=0
  erw [own_vertical_start,own_vertical_end,
    firstCutMember_grid,firstCutMember_grid]
  exact ZModModule.add_self _
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
end
end


