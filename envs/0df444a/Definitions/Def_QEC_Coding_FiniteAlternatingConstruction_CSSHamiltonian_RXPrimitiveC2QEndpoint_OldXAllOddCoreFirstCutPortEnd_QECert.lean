-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_OldXAllOddCoreFirstCutPortEnd_QECert
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_OldXAllOddCoreFirstCutPortEnd_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T22:46:21.903312+00:00
-- url     : https://prove2.me/theorems/d19452f6-5b4a-4e7d-aa7f-10373b0d569b
-- title:
--   All-odd OldX first-cut PortEnd
-- statement:
--   Exact first-cut support lemmas for the all-odd OldX proof.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L18360-L18373

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_OldXAllOddCoreFirstCutHead_QECert
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
theorem exists_direct_path_later_OldXCore_QECert (S : OddScale)
    (r0 r : (RawOne S).Q) (x0 x : (RawOne S).X)
    (hx0 : (RawOne S).xq x0 r0=true) (hx : (RawOne S).xq x r=true)
    (z : (RawOne S).Z) (hz : (RawOne S).qz r z=true)
    (c : BDL26FiniteTannerSquare.Two) (depth : Option (Fin (S.half-1)))
    (K : Nat) (hK : 0<K)
    (hr : K≤Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
    (hr0 : Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q)≤K^2)
    (hX0 : Encodable.encode (x0 : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤K^2)
    (hi : ∀ i, depth=some i → i.val<K^2) :
    ∃ p : UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation (RawOne S)) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) z S)
      (zCenter (RawOne S) S z c)
      (qToZDoubleCylinderVertex (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S
        (chosenPort (RawOne S) S r x hx c depth)),
      ∀ e, pathChain p e≠0 →
        Encodable.encode (executableCoordinate S
          (.inr ⟨r0,chosenPort (RawOne S) S r0 x0 hx0 c depth⟩))<
          Encodable.encode (executableCoordinate S (.inl ⟨z,e⟩)) := by
  apply direct_port_path_property_OldXBounded_QECert (RawOne S)
    (rxState S baseState).admissible.toTannerSquareAdmissible S r x z hx hz c depth
    (fun edge => Encodable.encode (executableCoordinate S
      (.inr ⟨r0,chosenPort (RawOne S) S r0 x0 hx0 c depth⟩))<
        Encodable.encode (executableCoordinate S (.inl ⟨z,edge⟩)))
  intro a k ha
  exact direct_segment_later_OldXBounded_QECert S r0 r x0 x hx0 hx z hz c depth
    K hK hr hr0 hX0 hi a k ha
private theorem firstCutPotential_port_cone (S : OddScale)
    (x : BaseX) (q : BaseQubit) (hx : baseTannerSquarePresentation.xq x q=true)
    (root : QStarEdge baseTannerSquarePresentation q) (c : BDL26FiniteTannerSquare.Two) :
    firstCutPotential S ⟨x,qToXDoubleCylinderVertexAtRoot baseTannerSquarePresentation
      q x hx S root (c,.inl (.inl ()))⟩=
        if decide (q=stripQ 1 x) then 1 else 0 := by
  dsimp only [firstCutPotential,firstCutMember,qToXDoubleCylinderVertexAtRoot,
    qToXSubdivisionVertexAtRoot,qToXBoundaryVertexAtRoot,qToXBoundaryEdge,
    xBoundaryEdgeStart,xBoundaryEdgeEnd,xStarBoundaryVertexToStar,xStarBoundaryEdgeToStar]
  apply indicator_iff
  simp only [decide_eq_true_eq]
  all_goals rfl
private theorem firstCutPotential_port_endpoint (S : OddScale)
    (x : BaseX) (q : BaseQubit) (hx : baseTannerSquarePresentation.xq x q=true)
    (root edge : QStarEdge baseTannerSquarePresentation q) (c : BDL26FiniteTannerSquare.Two) :
    firstCutPotential S ⟨x,qToXDoubleCylinderVertexAtRoot baseTannerSquarePresentation
      q x hx S root (c,.inl (.inr edge))⟩=
        if decide (edge.val=(1 : BaseZ)) then 1 else 0 := rfl
private theorem firstCutPotential_port_interior (S : OddScale)
    (x : BaseX) (q : BaseQubit) (hx : baseTannerSquarePresentation.xq x q=true)
    (root edge : QStarEdge baseTannerSquarePresentation q) (c : BDL26FiniteTannerSquare.Two)
    (i : Fin (S.half-1)) :
    firstCutPotential S ⟨x,qToXDoubleCylinderVertexAtRoot baseTannerSquarePresentation
      q x hx S root (c,.inr (edge,i))⟩=
        if decide (edge.val=(1 : BaseZ)) then 1 else 0 := rfl
private theorem firstCutPotential_q_gradient (S : OddScale) (q : BaseQubit)
    (v : QDoubleCylinderVertex baseTannerSquarePresentation q S) :
    tannerCoboundary0 (RawOne S) (firstCutPotential S) (.inr ⟨q,v⟩)=
      stripSeedCocycle 1 q := by
  erw [BDL26RXLocalReplacement.rxPresentation_coboundary0_eq
    baseTannerSquarePresentation baseTannerSquareAdmissibleV4
    baseTannerSquareCellularRegular S]
  erw [rx_q_gradient_OldXBounded_QECert baseTannerSquarePresentation baseTannerSquareAdmissible S]
  change (∑ x : BaseX, if hx : baseTannerSquarePresentation.xq x q=true then
    firstCutPotential S ⟨x,qToXDoubleCylinderVertexAtRoot baseTannerSquarePresentation
      q x hx S (baseTannerSquareAdmissible.qzRoot q) v⟩ else 0)=stripSeedCocycle 1 q
  rcases v with ⟨c,(cone | endpoint) | ⟨edge,i⟩⟩
  · cases cone
    simp_rw [firstCutPotential_port_cone]
    exact strip_sum_cone_OldXBounded_QECert 1 q
  · rcases endpoint with ⟨z,hz⟩
    change BaseZ at z
    simp_rw [firstCutPotential_port_endpoint]
    exact strip_sum_endpoint_OldXBounded_QECert 1 q z hz
  · rcases edge with ⟨z,hz⟩
    change BaseZ at z
    simp_rw [firstCutPotential_port_interior]
    exact strip_sum_endpoint_OldXBounded_QECert 1 q z hz
theorem firstCutOldKernel_q_zero_OldXCore_QECert (S : OddScale) (q : BaseQubit)
    (v : QDoubleCylinderVertex baseTannerSquarePresentation q S) :
    firstCutOldKernel S (.inr ⟨q,v⟩)=0 := by
  erw [firstCutOldKernel,Pi.add_apply,rawSeedLift,
    BDL26ReplacementCochainMaps.rxMap1Coord_qVertex,firstCutPotential_q_gradient]
  exact ZModModule.add_self _
theorem firstCutOldKernel_gamma_OldXCore_QECert (S : OddScale) :
    firstCutOldKernel S (gammaRadial S 1 ⟨0,S.half_pos⟩)=1 := by
  have h := firstCutOldKernel_horizontal_OldXCore_QECert S (0 : BaseX) 0 (seedFace 1) (⟨0,S.half_pos⟩) 0
  have hedge : subdivisionHorizontalEdge baseTannerSquarePresentation (0 : BaseX) S
      (seedFace 1) (⟨0,S.half_pos⟩) 0=(.inl (seedRadial 1,⟨0,S.half_pos⟩) :
        SubdivisionEdge baseTannerSquarePresentation 0 S) := by
    simp only [subdivisionHorizontalEdge,Fin.val_zero,↓reduceDIte]
    exact congrArg (fun e : XStarEdge baseTannerSquarePresentation (0 : BaseX) =>
      (Sum.inl (e,⟨0,S.half_pos⟩) : SubdivisionEdge baseTannerSquarePresentation 0 S))
        ((seedRadial_face_zero 1 (seedFace 1)).mpr rfl).symm
  erw [hedge] at h
  apply h.trans
  apply if_pos
  constructor
  · rfl
  · rfl
theorem oldLargestX_upper_OldXCore_QECert (S : OddScale) (x : BaseX)
    (e : DoubleCylinderEdge baseTannerSquarePresentation x S) (v : (RawOne S).X)
    (hv : (RawOne S).xq v (.inl ⟨x,e⟩)=true) :
    Encodable.encode (v : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (oldLargestX S (.inl ⟨x,e⟩) :
        (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
  rcases (old_local_incidence S v x e).mp hv with rfl | rfl
  · exact oldLargestX_start_le_OldXBounded_QECert S x e
  · exact oldLargestX_end_le_OldXCore_QECert S x e
theorem chosenPort_order_same_owner_OldXCore_QECert (S : OddScale) (r : (RawOne S).Q)
    (x y : (RawOne S).X) (hx : (RawOne S).xq x r=true) (hy : (RawOne S).xq y r=true)
    (c : BDL26FiniteTannerSquare.Two) (depth : Option (Fin (S.half-1)))
    (hxy : Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)<
      Encodable.encode (y : (BDL26LevelTwoDecoder.executableLevelOne S).X)) :
    Encodable.encode (executableCoordinate S
      (.inr ⟨r,chosenPort (RawOne S) S r x hx c depth⟩))<
      Encodable.encode (executableCoordinate S
        (.inr ⟨r,chosenPort (RawOne S) S r y hy c depth⟩)) := by
  cases depth with
  | none =>
    rw [encoded_chosenPort_OldXCore_QECert,encoded_chosenPort_OldXCore_QECert]
    dsimp only
    have ht : 2*(2*Encodable.encode (x :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)+1)<
      2*(2*Encodable.encode (y : (BDL26LevelTwoDecoder.executableLevelOne S).X)+1) := by omega
    have hc := Nat.pair_lt_pair_right c.val ht
    have hr := Nat.pair_lt_pair_right
      (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)) hc
    omega
  | some i =>
    rw [encoded_chosenPort_OldXCore_QECert,encoded_chosenPort_OldXCore_QECert]
    dsimp only
    have hi := Nat.pair_lt_pair_left i.val hxy
    have ht : 2*Nat.pair (Encodable.encode (x :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)) i.val+1<
      2*Nat.pair (Encodable.encode (y :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)) i.val+1 := by omega
    have hc := Nat.pair_lt_pair_right c.val ht
    have hr := Nat.pair_lt_pair_right
      (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)) hc
    omega
theorem global_zero_of_same_owner_pair_OldXCore_QECert (S : OddScale) (a : Word F (RawTwo S).Q)
    (r : (RawOne S).Q) (z : (RawOne S).Z) (hz : (RawOne S).qz r z=true)
    (hu : ∀ z', (RawOne S).qz r z'=true → z'=z)
    (v v' : QDoubleCylinderVertex (transposePresentation (RawOne S)) r S)
    (root : ZDoubleCylinderVertex (RawOne S) z S)
    (p : UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation (RawOne S)) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) z S)
      root (qToZDoubleCylinderVertex (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S v))
    (p' : UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation (RawOne S)) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) z S)
      root (qToZDoubleCylinderVertex (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S v'))
    (horder : Encodable.encode (executableCoordinate S (.inr ⟨r,v⟩))<
      Encodable.encode (executableCoordinate S (.inr ⟨r,v'⟩)))
    (hp : ∀ e, pathChain p e≠0 →
      Encodable.encode (executableCoordinate S (.inr ⟨r,v⟩))<
        Encodable.encode (executableCoordinate S (.inl ⟨z,e⟩)))
    (hp' : ∀ e, pathChain p' e≠0 →
      Encodable.encode (executableCoordinate S (.inr ⟨r,v⟩))<
        Encodable.encode (executableCoordinate S (.inl ⟨z,e⟩))) :
    BDL26GlobalLookupLinearity.actualGlobal S (tannerCoboundary1 (RawTwo S) a)
      (.inr ⟨r,v⟩)=0 := by
  have hne : (Sum.inr ⟨r,v⟩ : (RawTwo S).Q)≠Sum.inr ⟨r,v'⟩ := by
    intro he
    have hcode := congrArg (fun q : (RawTwo S).Q =>
      Encodable.encode (executableCoordinate S q)) he
    exact Nat.lt_irrefl _ (horder.trans_eq hcode.symm)
  have eval (q : (RawTwo S).Q) :
      twoArmKernel S r r z hz hz v v' root p p' q=
        ((if q=.inr ⟨r,v⟩ then 1 else 0)+(if q=.inr ⟨r,v'⟩ then 1 else 0))+
          extendZEdgeWord (RawOne S) S z (pathChain p+pathChain p') q :=
    two_units_apply_OldXBounded_QECert _ _ _ _
  apply actualGlobal_zero_of_encoded_kernel_OldXBounded_QECert S a
    (twoArmKernel S r r z hz hz v v' root p p') (.inr ⟨r,v⟩)
  · exact twoArmKernel_closed_OldXBounded_QECert S r r z hz hz hu hu v v' root p p'
  · have hlocal := extend_edge_at_port_OldXBounded_QECert (RawOne S) S z (pathChain p+pathChain p') r v
    exact (eval _).trans (by erw [if_pos rfl,if_neg hne,hlocal,add_zero,add_zero])
  · intro q hq
    change (RawTwo S).Q at q
    have hq0 : q≠Sum.inr ⟨r,v⟩ := by
      intro he
      have hcode := congrArg (fun out : (RawTwo S).Q =>
        Encodable.encode (executableCoordinate S out)) he
      exact Nat.lt_irrefl _ (hq.trans_eq hcode.symm)
    have hq1 : q≠Sum.inr ⟨r,v'⟩ := by
      intro he
      have hcode := congrArg (fun out : (RawTwo S).Q =>
        Encodable.encode (executableCoordinate S out)) he
      exact Nat.lt_asymm (hcode.symm.trans_lt hq) horder
    have hbase : twoArmKernel S r r z hz hz v v' root p p' q=
        extendZEdgeWord (RawOne S) S z (pathChain p+pathChain p') q :=
      (eval q).trans (two_indicators_zero_OldXBounded_QECert q (.inr ⟨r,v⟩) (.inr ⟨r,v'⟩) _ hq0 hq1)
    apply hbase.trans
    change RZQ (RawOne S) S at q
    rcases q with ⟨z',e⟩ | ⟨q,vq⟩
    · by_cases he : z'=z
      · subst z'
        have h0 : pathChain p e=0 := by
          by_contra hn
          exact Nat.lt_asymm hq (hp e hn)
        have h1 : pathChain p' e=0 := by
          by_contra hn
          exact Nat.lt_asymm hq (hp' e hn)
        exact (extend_edge_at_same_OldXBounded_QECert (RawOne S) S z (pathChain p+pathChain p') e).trans
          ((word_add_eval (pathChain p) (pathChain p') e).trans
            (by rw [h0,h1,zero_add]))
      · exact extend_edge_at_other_OldXBounded_QECert (RawOne S) S z z' (pathChain p+pathChain p') e he
    · exact extend_edge_at_port_OldXBounded_QECert (RawOne S) S z (pathChain p+pathChain p') q vq
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
end
end


