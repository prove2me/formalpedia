-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_OldXAllOddCoreFirstCutStripOrder_QECert
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_OldXAllOddCoreFirstCutStripOrder_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T22:13:05.240857+00:00
-- url     : https://prove2.me/theorems/c6130d44-9ebe-476b-9569-2cc7182f0722
-- title:
--   All-odd OldX first-cut StripOrder
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
theorem stripFace_xq_code_OldXCore_QECert (j : Fin 2) (x : BaseX) :
    baseEdgeCode (xStarFaceXQEdge baseTannerSquarePresentation x (stripFace j x) 0).val=
      2*Nat.pair x.val (j.val+2*x.val) := by
  fin_cases j <;> fin_cases x <;> decide
theorem stripFace_qz_code_OldXCore_QECert (j : Fin 2) (x : BaseX) :
    baseEdgeCode (xStarFaceQZEdge baseTannerSquarePresentation x (stripFace j x) 1).val=
      41+2*j.val := by
  fin_cases j <;> fin_cases x <;> decide
private theorem strip_inner_edge_code (j : Fin 2) (x : BaseX) (n k : Nat)
    (hn : 1≤n) (hk : k<n) :
    2*Nat.pair (2*j.val) n<4*Nat.pair (j.val+2*x.val) (Nat.pair n k)+1 := by
  have hf := pair_mono_left_OldXCore_QECert j.val (j.val+2*x.val) (Nat.pair n k) (by omega)
  suffices h : 2*Nat.pair (2*j.val) n<4*Nat.pair j.val (Nat.pair n k)+1 by omega
  fin_cases j
  · change 2*Nat.pair 0 n<4*Nat.pair 0 (Nat.pair n k)+1
    rw [pair_zero_left_sq_OldXCore_QECert,pair_zero_left_sq_OldXCore_QECert]
    have hs := Nat.pow_le_pow_left (Nat.left_le_pair n k) 2
    omega
  · change 2*Nat.pair 2 n<4*Nat.pair 1 (Nat.pair n k)+1
    by_cases h1 : n=1
    · subst n
      have hk0 : k=0 := by omega
      subst k
      decide
    · have hn2 : 2≤n := by omega
      have hu := Nat.pair_lt_max_add_one_sq 2 n
      rw [max_eq_right hn2] at hu
      have hna : n^2≤Nat.pair n k := by
        have hl := Nat.max_sq_add_min_le_pair n k
        have hs := Nat.pow_le_pow_left (Nat.le_max_left n k) 2
        omega
      have ha : n+1≤Nat.pair n k := by nlinarith
      have hs := Nat.pow_le_pow_left ha 2
      have hl := Nat.max_sq_add_min_le_pair 1 (Nat.pair n k)
      have hs' := Nat.pow_le_pow_left (Nat.le_max_right 1 (Nat.pair n k)) 2
      omega
private theorem strip_subEdge_code_lower (S : OddScale) (j : Fin 2) (x : BaseX)
    (row : Fin (S.half+1)) :
    2*Nat.pair (2*j.val) (S.half-1)≤
      subEdgeCode x S (subdivisionHorizontalEdge baseTannerSquarePresentation x S
        (stripFace j x) (lastSegment S) row) := by
  unfold subdivisionHorizontalEdge
  split_ifs with hzero hlast
  · change 2*Nat.pair (2*j.val) (S.half-1)≤
      2*Nat.pair (baseEdgeCode
        (xStarFaceXQEdge baseTannerSquarePresentation x (stripFace j x) 0).val) (S.half-1)
    rw [stripFace_xq_code_OldXCore_QECert]
    have hright := Nat.right_le_pair x.val (j.val+2*x.val)
    have hm := pair_mono_left_OldXCore_QECert (2*j.val)
      (2*Nat.pair x.val (j.val+2*x.val)) (S.half-1) (by omega)
    omega
  · change 2*Nat.pair (2*j.val) (S.half-1)≤
      2*Nat.pair (baseEdgeCode
        (xStarFaceQZEdge baseTannerSquarePresentation x (stripFace j x) 1).val) (S.half-1)
    rw [stripFace_qz_code_OldXCore_QECert]
    have hm := pair_mono_left_OldXCore_QECert (2*j.val) (41+2*j.val) (S.half-1) (by omega)
    omega
  · change 2*Nat.pair (2*j.val) (S.half-1)≤
      4*Nat.pair (j.val+2*x.val) (Nat.pair (S.half-1) (row.val-1))+1
    have hh : 2≤S.half := by have := row.isLt; have := S.half_pos; omega
    have hk : row.val-1<S.half-1 := by have := row.isLt; omega
    exact (strip_inner_edge_code j x (S.half-1) (row.val-1) (by omega) hk).le
private theorem strip_oldQ_code_lower (S : OddScale) (j : Fin 2) (x : BaseX)
    (c : BDL26FiniteTannerSquare.Two) (row : Fin (S.half+1)) :
    Encodable.encode (gammaRadial S j (lastSegment S) :
      (BDL26LevelTwoDecoder.executableLevelOne S).Q)≤
      Encodable.encode (stripHorizontal S j x c row :
        (BDL26LevelTwoDecoder.executableLevelOne S).Q) := by
  erw [gammaRadial,stripHorizontal,encoded_old_local_Q_OldXCore_QECert,encoded_old_local_Q_OldXCore_QECert]
  have hE := strip_subEdge_code_lower S j x row
  have hEt : subEdgeCode 0 S (.inl (seedRadial j,lastSegment S))=
      2*Nat.pair (2*j.val) (S.half-1) := by
    simp only [subEdgeCode,seedRadial_code_OldXCore_QECert,lastSegment]
  erw [hEt]
  have h0 := pair_mono_right_OldXCore_QECert 0 _ _ hE
  have h1 := pair_mono_left_OldXCore_QECert 0 c.val
    (subEdgeCode x S (subdivisionHorizontalEdge baseTannerSquarePresentation x S
      (stripFace j x) (lastSegment S) row)) (Nat.zero_le _)
  have hinner : 2*Nat.pair 0 (2*Nat.pair (2*j.val) (S.half-1))≤
      2*Nat.pair c.val (subEdgeCode x S
        (subdivisionHorizontalEdge baseTannerSquarePresentation x S
          (stripFace j x) (lastSegment S) row)) := by omega
  have hout := pair_mono_right_OldXCore_QECert 0 _ _ hinner
  have howner := pair_mono_left_OldXCore_QECert 0 x.val
    (2*Nat.pair c.val (subEdgeCode x S
      (subdivisionHorizontalEdge baseTannerSquarePresentation x S
        (stripFace j x) (lastSegment S) row))) (Nat.zero_le _)
  simp only [Fin.val_zero,Fin.val_one,Fin.val_mk] at *
  omega
theorem oldX_tag_lower_OldXCore_QECert (u v x c : Nat) (h : u≤v) :
    u^4≤Nat.pair x (Nat.pair c v) := by
  have hi := pair_mono_right_OldXCore_QECert 0 u v h
  have hc := pair_mono_left_OldXCore_QECert 0 c v (Nat.zero_le _)
  have hinner : Nat.pair 0 u≤Nat.pair c v := hi.trans hc
  calc
    u^4=Nat.pair 0 (Nat.pair 0 u) := by rw [pair_zero_left_sq_OldXCore_QECert,pair_zero_left_sq_OldXCore_QECert]; ring
    _≤Nat.pair 0 (Nat.pair c v) := pair_mono_right_OldXCore_QECert 0 _ _ hinner
    _≤Nat.pair x (Nat.pair c v) := pair_mono_left_OldXCore_QECert 0 x _ (Nat.zero_le _)
private theorem terminalX_le_tag (S : OddScale) (j : Fin 2) :
    Encodable.encode (oldLargestX S (gammaRadial S j (lastSegment S)) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤(terminalTag S j)^4 := by
  have hstart : Encodable.encode (oldLocalStart S 0
      (.inl (0,.inl (seedRadial j,lastSegment S))) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤(terminalTag S j)^4 := by
    change Encodable.encode (⟨(0 : BaseX),(0,
      subdivisionSegmentStart baseTannerSquarePresentation 0 S (seedRadial j)
        (lastSegment S))⟩ : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤_
    erw [encoded_old_X_copy0_OldXCore_QECert]
    unfold subdivisionSegmentStart
    split_ifs with hzero
    · erw [seedRadial_start_OldXBounded_QECert]
      change (0 : Nat)≤_
      exact Nat.zero_le _
    · apply Nat.pow_le_pow_left _ 4
      change 4*Nat.pair (baseEdgeCode (seedRadial j).val) ((S.half-1)-1)+1≤terminalTag S j
      rw [seedRadial_code_OldXCore_QECert]
      have hs : (S.half-1)-1=S.half-2 := by omega
      rw [hs]
      exact Nat.le_max_right _ _
  have hend : Encodable.encode (oldLocalEnd S 0
      (.inl (0,.inl (seedRadial j,lastSegment S))) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤(terminalTag S j)^4 := by
    change Encodable.encode (⟨(0 : BaseX),(0,
      subdivisionSegmentEnd baseTannerSquarePresentation 0 S (seedRadial j)
        (lastSegment S))⟩ : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤_
    erw [encoded_old_X_copy0_OldXCore_QECert]
    have hlast : (lastSegment S).val+1=S.half := by have := S.half_pos; dsimp [lastSegment]; omega
    unfold subdivisionSegmentEnd
    simp only [dif_pos hlast]
    change (2*(4*j.val+1))^4≤(terminalTag S j)^4
    exact Nat.pow_le_pow_left (Nat.le_max_left _ _) 4
  change Encodable.encode (oldLargestX S (.inl ⟨(0 : BaseX),
    .inl (0,.inl (seedRadial j,lastSegment S))⟩) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤_
  exact code_larger_upper_OldXBounded_QECert _ _ _ hstart hend
theorem oldLargestX_le_of_ends_OldXCore_QECert (S : OddScale) (x : BaseX)
    (e : DoubleCylinderEdge baseTannerSquarePresentation x S) (B : Nat)
    (hs : Encodable.encode (oldLocalStart S x e :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤B)
    (ht : Encodable.encode (oldLocalEnd S x e :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤B) :
    Encodable.encode (oldLargestX S (.inl ⟨x,e⟩) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤B := by
  exact code_larger_upper_OldXBounded_QECert _ _ _ hs ht
theorem stripFace_q0_vertex_code_OldXCore_QECert (j : Fin 2) (x : BaseX) :
    baseVertexCode (xStarFaceQVertex baseTannerSquarePresentation x (stripFace j x) 0).val=
      4*(j.val+2*x.val)+1 := by
  fin_cases j <;> fin_cases x <;> decide
private theorem strip_row0_X_lower (S : OddScale) (j : Fin 2) (x : BaseX)
    (c : BDL26FiniteTannerSquare.Two) :
    Encodable.encode (oldLargestX S (gammaRadial S j (lastSegment S)) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (oldLargestX S (stripHorizontal S j x c 0) :
        (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
  let e0 : DoubleCylinderEdge baseTannerSquarePresentation (0 : BaseX) S :=
    .inl (0,.inl (seedRadial j,lastSegment S))
  let e : DoubleCylinderEdge baseTannerSquarePresentation x S :=
    .inl (c,.inl (xStarFaceXQEdge baseTannerSquarePresentation x (stripFace j x) 0,
      lastSegment S))
  have hbase : 2*j.val≤baseEdgeCode
      (xStarFaceXQEdge baseTannerSquarePresentation x (stripFace j x) 0).val := by
    rw [stripFace_xq_code_OldXCore_QECert]
    have := Nat.right_le_pair x.val (j.val+2*x.val)
    omega
  have hs : Encodable.encode (oldLocalStart S 0 e0 :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (oldLocalStart S x e :
        (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
    change Encodable.encode (⟨(0 : BaseX),(0,
      subdivisionSegmentStart baseTannerSquarePresentation 0 S (seedRadial j)
        (lastSegment S))⟩ : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (⟨x,(c,subdivisionSegmentStart baseTannerSquarePresentation x S
        (xStarFaceXQEdge baseTannerSquarePresentation x (stripFace j x) 0)
        (lastSegment S))⟩ : (BDL26LevelTwoDecoder.executableLevelOne S).X)
    erw [encoded_old_X_copy0_OldXCore_QECert,encoded_old_X_OldXCore_QECert]
    unfold subdivisionSegmentStart
    split_ifs with hzero
    · erw [seedRadial_start_OldXBounded_QECert]
      change (0 : Nat)≤_
      exact Nat.zero_le _
    · apply oldX_tag_lower_OldXCore_QECert
      change 4*Nat.pair (baseEdgeCode (seedRadial j).val) ((S.half-1)-1)+1≤
        4*Nat.pair (baseEdgeCode
          (xStarFaceXQEdge baseTannerSquarePresentation x (stripFace j x) 0).val)
          ((S.half-1)-1)+1
      rw [seedRadial_code_OldXCore_QECert]
      have hm := pair_mono_left_OldXCore_QECert _ _ ((S.half-1)-1) hbase
      omega
  have ht : Encodable.encode (oldLocalEnd S 0 e0 :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (oldLocalEnd S x e :
        (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
    change Encodable.encode (⟨(0 : BaseX),(0,
      subdivisionSegmentEnd baseTannerSquarePresentation 0 S (seedRadial j)
        (lastSegment S))⟩ : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (⟨x,(c,subdivisionSegmentEnd baseTannerSquarePresentation x S
        (xStarFaceXQEdge baseTannerSquarePresentation x (stripFace j x) 0)
        (lastSegment S))⟩ : (BDL26LevelTwoDecoder.executableLevelOne S).X)
    erw [encoded_old_X_copy0_OldXCore_QECert,encoded_old_X_OldXCore_QECert]
    have hlast : (lastSegment S).val+1=S.half := by have := S.half_pos; dsimp [lastSegment]; omega
    unfold subdivisionSegmentEnd
    simp only [dif_pos hlast]
    apply oldX_tag_lower_OldXCore_QECert
    change 2*(4*j.val+1)≤2*baseVertexCode
      (xStarFaceQVertex baseTannerSquarePresentation x (stripFace j x) 0).val
    rw [stripFace_q0_vertex_code_OldXCore_QECert]
    omega
  change Encodable.encode (oldLargestX S (.inl ⟨(0 : BaseX),e0⟩) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
    Encodable.encode (oldLargestX S (.inl ⟨x,e⟩) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)
  apply oldLargestX_le_of_ends_OldXCore_QECert
  · exact hs.trans (oldLargestX_start_le_OldXBounded_QECert S x e)
  · exact ht.trans (oldLargestX_end_le_OldXCore_QECert S x e)
private theorem stripFace_q1_vertex_code (j : Fin 2) (x : BaseX) :
    baseVertexCode (xStarFaceQVertex baseTannerSquarePresentation x (stripFace j x) 1).val=17 := by
  fin_cases j <;> fin_cases x <;> decide
private theorem terminalTag_le_qz_start (S : OddScale) (j : Fin 2) (x : BaseX) :
    terminalTag S j ≤ subVertexCode x S
      (subdivisionSegmentStart baseTannerSquarePresentation x S
        (xStarFaceQZEdge baseTannerSquarePresentation x (stripFace j x) 1)
        (lastSegment S)) := by
  unfold subdivisionSegmentStart
  split_ifs with hzero
  · have hh : S.half=1 := by have := S.half_pos; dsimp [lastSegment] at hzero; omega
    change terminalTag S j≤2*baseVertexCode
      (xStarEdgeStart baseTannerSquarePresentation x
        (xStarFaceQZEdge baseTannerSquarePresentation x (stripFace j x) 1)).val
    erw [xStarEdgeStart_faceQZEdge,stripFace_q1_vertex_code]
    fin_cases j <;> norm_num [terminalTag,hh,Nat.pair]
  · change terminalTag S j≤4*Nat.pair (baseEdgeCode
      (xStarFaceQZEdge baseTannerSquarePresentation x (stripFace j x) 1).val)
      ((S.half-1)-1)+1
    rw [stripFace_qz_code_OldXCore_QECert]
    have hs : (S.half-1)-1=S.half-2 := by omega
    rw [hs]
    apply max_le
    · have hj := j.isLt
      have hl := Nat.left_le_pair (41+2*j.val) (S.half-2)
      omega
    · have hm := pair_mono_left_OldXCore_QECert (2*j.val) (41+2*j.val) (S.half-2) (by omega)
      omega
private theorem strip_rowh_X_lower (S : OddScale) (j : Fin 2) (x : BaseX)
    (c : BDL26FiniteTannerSquare.Two) :
    Encodable.encode (oldLargestX S (gammaRadial S j (lastSegment S)) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (oldLargestX S
        (stripHorizontal S j x c (gridAt S S.half le_rfl)) :
          (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
  let e : DoubleCylinderEdge baseTannerSquarePresentation x S :=
    .inl (c,.inl (xStarFaceQZEdge baseTannerSquarePresentation x (stripFace j x) 1,
      lastSegment S))
  have hs : (terminalTag S j)^4≤Encodable.encode (oldLocalStart S x e :
      (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
    change (terminalTag S j)^4≤Encodable.encode (⟨x,(c,
      subdivisionSegmentStart baseTannerSquarePresentation x S
        (xStarFaceQZEdge baseTannerSquarePresentation x (stripFace j x) 1)
        (lastSegment S))⟩ : (BDL26LevelTwoDecoder.executableLevelOne S).X)
    erw [encoded_old_X_OldXCore_QECert]
    exact oldX_tag_lower_OldXCore_QECert _ _ _ _ (terminalTag_le_qz_start S j x)
  have h := (terminalX_le_tag S j).trans (hs.trans (oldLargestX_start_le_OldXBounded_QECert S x e))
  have hedge := horizontal_last_eq_OldXBounded_QECert baseTannerSquarePresentation x S (stripFace j x)
    (lastSegment S) (gridAt S S.half le_rfl) rfl
  have he := congrArg (fun edge : SubdivisionEdge baseTannerSquarePresentation x S =>
    Encodable.encode (oldLargestX S (.inl ⟨x,.inl (c,edge)⟩) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)) hedge
  exact h.trans_eq he.symm
private theorem terminalTag_inner_bound (j : Fin 2) (x : BaseX) (m k : Nat) :
    max (2*(4*j.val+1)) (4*Nat.pair (2*j.val) m+1)≤
      max (4*Nat.pair (j.val+2*x.val) (Nat.pair m k)+3)
        (4*Nat.pair (2*Nat.pair (j.val+2*x.val) j.val+1) k+1) := by
  fin_cases j
  · simp only [Fin.val_mk,Nat.zero_add,Nat.mul_zero,Nat.add_zero]
    change max 2 (4*Nat.pair 0 m+1)≤
      max (4*Nat.pair (2*x.val) (Nat.pair m k)+3)
        (4*Nat.pair (2*Nat.pair (2*x.val) 0+1) k+1)
    apply le_trans _ (Nat.le_max_left _ _)
    have hm := Nat.pow_le_pow_left (Nat.left_le_pair m k) 2
    have hf := pair_mono_left_OldXCore_QECert 0 (2*x.val) (Nat.pair m k) (Nat.zero_le _)
    rw [pair_zero_left_sq_OldXCore_QECert] at hf
    rw [pair_zero_left_sq_OldXCore_QECert]
    apply max_le <;> omega
  · simp only [Fin.val_mk]
    norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.reduceMod]
    change max 10 (4*Nat.pair 2 m+1)≤
      max (4*Nat.pair (1+2*x.val) (Nat.pair m k)+3)
        (4*Nat.pair (2*Nat.pair (1+2*x.val) 1+1) k+1)
    by_cases hm : m≤1
    · apply le_trans _ (Nat.le_max_right _ _)
      have hsmall : Nat.pair 2 m≤7 := by interval_cases m <;> decide
      have hpair := pair_mono_left_OldXCore_QECert 1 (1+2*x.val) 1 (by omega)
      have h11 : Nat.pair 1 1=3 := rfl
      rw [h11] at hpair
      have he : 7≤2*Nat.pair (1+2*x.val) 1+1 := by omega
      have hs := Nat.pow_le_pow_left he 2
      have hl := Nat.max_sq_add_min_le_pair (2*Nat.pair (1+2*x.val) 1+1) k
      have hs' := Nat.pow_le_pow_left
        (Nat.le_max_left (2*Nat.pair (1+2*x.val) 1+1) k) 2
      apply max_le <;> omega
    · apply le_trans _ (Nat.le_max_left _ _)
      have hm2 : 2 ≤ m := by omega
      have hu := Nat.pair_lt_max_add_one_sq 2 m
      rw [max_eq_right hm2] at hu
      have hma : m^2≤Nat.pair m k := by
        have hl := Nat.max_sq_add_min_le_pair m k
        have hs := Nat.pow_le_pow_left (Nat.le_max_left m k) 2
        omega
      have ha : m+1≤Nat.pair m k := by nlinarith
      have hs := Nat.pow_le_pow_left ha 2
      have hl := Nat.max_sq_add_min_le_pair (1+2*x.val) (Nat.pair m k)
      have hs' := Nat.pow_le_pow_left
        (Nat.le_max_right (1+2*x.val) (Nat.pair m k)) 2
      apply max_le <;> omega
private theorem stripFace_qz0_code (j : Fin 2) (x : BaseX) :
    baseEdgeCode (xStarFaceQZEdge baseTannerSquarePresentation x (stripFace j x) 0).val=
      2*Nat.pair (j.val+2*x.val) j.val+1 := by
  fin_cases j <;> fin_cases x <;> decide
private theorem strip_inner_start_code (S : OddScale) (j : Fin 2) (x : BaseX)
    (k : Fin (S.half-1)) :
    subVertexCode x S (subdivisionEdgeStart baseTannerSquarePresentation x S
      (.inr (.inl (stripFace j x,lastSegment S,k))))=
      4*Nat.pair (j.val+2*x.val) (Nat.pair (S.half-2) k.val)+3 := by
  have hh : 2≤S.half := by have := k.isLt; omega
  have hc0 : S.half-1≠0 := by omega
  have hch : S.half-1≠S.half := by omega
  have hk0 : k.val+1≠0 := by omega
  have hkh : k.val+1≠S.half := by have := k.isLt; omega
  have hs : (S.half-1)-1=S.half-2 := by omega
  erw [horizontal_inner_start_grid_OldXBounded_QECert,grid_vertex_view_OldXBounded_QECert]
  simp only [finCastGrid,finInteriorGrid,lastSegment,Fin.val_mk]
  simp only [hc0,hch,hk0,hkh,↓reduceDIte]
  change 4*Nat.pair (j.val+2*x.val)
    (Nat.pair ((S.half-1)-1) ((k.val+1)-1))+3=_
  rw [hs,Nat.add_sub_cancel]
private theorem strip_inner_end_code (S : OddScale) (j : Fin 2) (x : BaseX)
    (k : Fin (S.half-1)) :
    subVertexCode x S (subdivisionEdgeEnd baseTannerSquarePresentation x S
      (.inr (.inl (stripFace j x,lastSegment S,k))))=
      4*Nat.pair (2*Nat.pair (j.val+2*x.val) j.val+1) k.val+1 := by
  have hh : 2≤S.half := by have := k.isLt; omega
  have hl : S.half-1+1=S.half := by omega
  have hk0 : k.val+1≠0 := by omega
  have hkh : k.val+1≠S.half := by have := k.isLt; omega
  erw [horizontal_inner_end_grid_OldXBounded_QECert,grid_vertex_view_OldXBounded_QECert]
  simp only [finSuccGrid,finInteriorGrid,lastSegment,Fin.val_mk]
  simp only [hl,S.half_pos.ne',hk0,hkh,↓reduceDIte]
  change 4*Nat.pair (baseEdgeCode
    (xStarFaceQZEdge baseTannerSquarePresentation x (stripFace j x) 0).val)
      ((k.val+1)-1)+1=_
  erw [stripFace_qz0_code,Nat.add_sub_cancel]
theorem localLargestX_ge_tag_OldXCore_QECert (S : OddScale) (x : BaseX)
    (c : BDL26FiniteTannerSquare.Two) (e : SubdivisionEdge baseTannerSquarePresentation x S)
    (T : Nat) (hT : T≤ max
      (subVertexCode x S (subdivisionEdgeStart baseTannerSquarePresentation x S e))
      (subVertexCode x S (subdivisionEdgeEnd baseTannerSquarePresentation x S e))) :
    T^4≤Encodable.encode (oldLargestX S (.inl ⟨x,.inl (c,e)⟩) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
  rcases le_max_iff.mp hT with hs | ht
  · have h : T^4≤Encodable.encode (oldLocalStart S x (.inl (c,e)) :
        (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
      change T^4≤Encodable.encode (⟨x,(c,
        subdivisionEdgeStart baseTannerSquarePresentation x S e)⟩ :
          (BDL26LevelTwoDecoder.executableLevelOne S).X)
      erw [encoded_old_X_OldXCore_QECert]
      exact oldX_tag_lower_OldXCore_QECert _ _ _ _ hs
    exact h.trans (oldLargestX_start_le_OldXBounded_QECert S x (.inl (c,e)))
  · have h : T^4≤Encodable.encode (oldLocalEnd S x (.inl (c,e)) :
        (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
      change T^4≤Encodable.encode (⟨x,(c,
        subdivisionEdgeEnd baseTannerSquarePresentation x S e)⟩ :
          (BDL26LevelTwoDecoder.executableLevelOne S).X)
      erw [encoded_old_X_OldXCore_QECert]
      exact oldX_tag_lower_OldXCore_QECert _ _ _ _ ht
    exact h.trans (oldLargestX_end_le_OldXCore_QECert S x (.inl (c,e)))
private theorem strip_inner_X_lower (S : OddScale) (j : Fin 2) (x : BaseX)
    (c : BDL26FiniteTannerSquare.Two) (k : Fin (S.half-1)) :
    Encodable.encode (oldLargestX S (gammaRadial S j (lastSegment S)) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (oldLargestX S (.inl ⟨x,
        .inl (c,.inr (.inl (stripFace j x,lastSegment S,k)))⟩) :
          (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
  apply (terminalX_le_tag S j).trans
  apply localLargestX_ge_tag_OldXCore_QECert
  erw [strip_inner_start_code,strip_inner_end_code]
  exact terminalTag_inner_bound j x (S.half-2) k.val
private theorem strip_oldX_code_lower (S : OddScale) (j : Fin 2) (x : BaseX)
    (c : BDL26FiniteTannerSquare.Two) (row : Fin (S.half+1)) :
    Encodable.encode (oldLargestX S (gammaRadial S j (lastSegment S)) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (oldLargestX S (stripHorizontal S j x c row) :
        (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
  by_cases h0 : row.val=0
  · have he : row=0 := Fin.ext h0
    subst row
    exact strip_row0_X_lower S j x c
  · by_cases hh : row.val=S.half
    · have he : row=gridAt S S.half le_rfl := Fin.ext hh
      subst row
      exact strip_rowh_X_lower S j x c
    · have h := strip_inner_X_lower S j x c (finInteriorIndex S row h0 hh)
      have hedge := horizontal_inner_eq_OldXBounded_QECert baseTannerSquarePresentation x S
        (stripFace j x) (lastSegment S) row h0 hh
      have he := congrArg (fun edge : SubdivisionEdge baseTannerSquarePresentation x S =>
        Encodable.encode (oldLargestX S (.inl ⟨x,.inl (c,edge)⟩) :
          (BDL26LevelTwoDecoder.executableLevelOne S).X)) hedge
      exact h.trans_eq he.symm
theorem global_terminal_large_port_zero_OldXCore_QECert (S : OddScale)
    (a : Word F (RawTwo S).Q) (j : Fin 2) (c : BDL26FiniteTannerSquare.Two)
    (depth : Option (Fin (S.half-1)))
    (hn : 0<j.val+(lastSegment S).val) :
    BDL26GlobalLookupLinearity.actualGlobal S (tannerCoboundary1 (RawTwo S) a)
      (.inr ⟨gammaRadial S j (lastSegment S),
        largePorts S c depth (gammaRadial S j (lastSegment S))⟩)=0 := by
  apply global_zero_of_port_kernel_OldXCore_QECert S a (largePorts S c depth) (directRoots S c)
    (directPaths S c depth) (terminalOldKernel S j) (terminalOldKernel_closed_OldXBounded_QECert S j)
    (gammaRadial S j (lastSegment S)) (terminalOldKernel_gamma_OldXBounded_QECert S j)
  · intro r hr hne
    obtain ⟨x,c',row,rfl⟩ := terminalOldKernel_support_OldXBounded_QECert S j r hr
    exact largePorts_later_OldXCore_QECert S c depth _ _ hne
      (strip_oldQ_code_lower S j x c' row) (strip_oldX_code_lower S j x c' row)
  · intro r hr z hz e he
    obtain ⟨x,c',row,rfl⟩ := terminalOldKernel_support_OldXBounded_QECert S j r hr
    apply directPaths_later_OldXBounded_QECert S c depth (gammaRadial S j (lastSegment S))
      (stripHorizontal S j x c' row) z hz (gamma_code_pos_OldXCore_QECert S j (lastSegment S) hn)
      (strip_oldQ_code_lower S j x c' row)
      (gammaLargestX_le_square_OldXCore_QECert S j (lastSegment S) hn) _ e he
    intro i _
    have hi : i.val<(lastSegment S).val := by have := i.isLt; dsimp [lastSegment]; omega
    have hindex := gamma_index_le_code_OldXBounded_QECert S j (lastSegment S)
    have hself : Encodable.encode (gammaRadial S j (lastSegment S) :
        (BDL26LevelTwoDecoder.executableLevelOne S).Q)≤
      (Encodable.encode (gammaRadial S j (lastSegment S) :
        (BDL26LevelTwoDecoder.executableLevelOne S).Q))^2 := Nat.le_self_pow (by decide) _
    exact hi.trans_le (hindex.trans hself)
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
end
end


