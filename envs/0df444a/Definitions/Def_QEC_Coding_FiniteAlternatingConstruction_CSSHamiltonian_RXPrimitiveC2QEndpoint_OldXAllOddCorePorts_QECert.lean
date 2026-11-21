-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_OldXAllOddCorePorts_QECert
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_OldXAllOddCorePorts_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T21:28:28.142319+00:00
-- url     : https://prove2.me/theorems/3d5646b6-e239-44bb-ab3c-a545a8b3f79c
-- title:
--   All-odd OldX readout port lemmas
-- statement:
--   Exact support lemmas for ports and path substitutions in the all-odd OldX proof.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L18360-L18373

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_OldXAllOddCoreLocal_QECert
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
theorem global_zero_of_port_kernel_OldXCore_QECert (S : OddScale)
    (a : Word F (RawTwo S).Q) (vertices : PortVertices S)
    (roots : PortRoots S) (paths : PortPaths S vertices roots)
    (w : Word F (RawOne S).Q) (hw : tannerCoboundary1 (RawOne S) w=0)
    (r : (RawOne S).Q) (hr : w r=1)
    (hq : ∀ r', w r'≠0 → r'≠r →
      Encodable.encode (executableCoordinate S (.inr ⟨r,vertices r⟩))<
        Encodable.encode (executableCoordinate S (.inr ⟨r',vertices r'⟩)))
    (hz : ∀ r', w r'≠0 → ∀ z (h : (RawOne S).qz r' z=true) e,
      pathChain (paths r' z h) e≠0 →
        Encodable.encode (executableCoordinate S (.inr ⟨r,vertices r⟩))<
          Encodable.encode (executableCoordinate S (.inl ⟨z,e⟩))) :
    BDL26GlobalLookupLinearity.actualGlobal S
      (tannerCoboundary1 (RawTwo S) a) (.inr ⟨r,vertices r⟩)=0 := by
  apply actualGlobal_zero_of_encoded_kernel_OldXBounded_QECert S a
    (portKernel S vertices roots paths w) (.inr ⟨r,vertices r⟩)
  · exact portKernel_closed_OldXBounded_QECert S vertices roots paths w hw
  · erw [portKernel_q_OldXBounded_QECert,hr,if_pos rfl,mul_one]
  · intro p hp
    cases p with
    | inr q =>
      rcases q with ⟨r',v⟩
      erw [portKernel_q_OldXBounded_QECert]
      by_cases hr' : w r'=0
      · erw [hr',zero_mul]
      · by_cases hv : v=vertices r'
        · subst v
          by_cases he : r'=r
          · subst r'
            exact False.elim (Nat.lt_irrefl _ hp)
          · exact False.elim (Nat.lt_asymm hp (hq r' hr' he))
        · erw [if_neg hv,mul_zero]
    | inl edge =>
      rcases edge with ⟨z,e⟩
      erw [portKernel,Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro r' _
      by_cases hr' : w r'=0
      · change w r'*portBasis S vertices roots paths r' (.inl ⟨z,e⟩)=0
        rw [hr',zero_mul]
      · have he : portBasis S vertices roots paths r' (.inl ⟨z,e⟩)=0 := by
          erw [portBasis,Pi.add_apply]
          have hbase : canonicalBasisWord (F:=F)
              (Sum.inr ⟨r',vertices r'⟩ : (RawTwo S).Q) (.inl ⟨z,e⟩)=0 := by
            simp [canonicalBasisWord]
          erw [hbase,zero_add,Finset.sum_apply]
          apply Finset.sum_eq_zero
          intro z' _
          by_cases h : (RawOne S).qz r' z'=true
          · erw [dif_pos h]
            by_cases hzz : z=z'
            · subst z'
              have hpath : pathChain (paths r' z h) e=0 := by
                by_contra hn
                exact Nat.lt_asymm hp (hz r' hr' z h e hn)
              simp [extendZEdgeWord,hpath]
            · exact dif_neg hzz
          · simp only [dif_neg h,word_zero_eval]
        change w r'*portBasis S vertices roots paths r' (.inl ⟨z,e⟩)=0
        rw [he,mul_zero]
theorem q_before_larger_port_code_OldXCore_QECert (r r' u v : Nat)
    (c : BDL26FiniteTannerSquare.Two) (huv : u<v)
    (hr : r<Nat.pair c.val v) :
    2*Nat.pair r (Nat.pair c.val u)+1<
      2*Nat.pair r' (Nat.pair c.val v)+1 := by
  have ht := Nat.pair_lt_pair_right c.val huv
  have hb : max r (Nat.pair c.val u)+1≤Nat.pair c.val v := by omega
  have hu := Nat.pair_lt_max_add_one_sq r (Nat.pair c.val u)
  have hl := Nat.max_sq_add_min_le_pair r' (Nat.pair c.val v)
  have hsq := Nat.pow_le_pow_left
    (hb.trans (Nat.le_max_right r' (Nat.pair c.val v))) 2
  omega
private theorem interior_before_any_root_code (r x z A i k : Nat)
    (c : BDL26FiniteTannerSquare.Two) (hr : r<A) (hx : x<A) (hi : i<A) :
    2*Nat.pair r (Nat.pair c.val (2*Nat.pair x i+1))+1<
      2*Nat.pair z (2*Nat.pair c.val (2*Nat.pair A k)) := by
  have hmax : max x i+1≤A := by omega
  have hu := Nat.pair_lt_max_add_one_sq x i
  have hs := Nat.pow_le_pow_left hmax 2
  have hl := Nat.max_sq_add_min_le_pair A k
  have hA := Nat.le_max_left A k
  have hs' := Nat.pow_le_pow_left hA 2
  have huv : 2*Nat.pair x i+1<2*Nat.pair A k := by omega
  apply q_before_local_code_OldXBounded_QECert _ _ _ _ c huv
  have ha := Nat.left_le_pair A k
  have hc := Nat.right_le_pair c.val (2*Nat.pair A k)
  omega
private theorem endpoint_before_any_root_code (r x z A k : Nat)
    (c : BDL26FiniteTannerSquare.Two) (hr : r<A) (hx : x<A) (hA : 1<A) :
    2*Nat.pair r (Nat.pair c.val (2*(2*x+1)))+1<
      2*Nat.pair z (2*Nat.pair c.val (2*Nat.pair A k)) := by
  have hl : A^2+A≤Nat.pair A k := by
    rw [Nat.pair]
    split_ifs with h
    · have hs := Nat.pow_le_pow_left h.le 2
      nlinarith
    · nlinarith
  have huv : 2*(2*x+1)<2*Nat.pair A k := by nlinarith
  apply q_before_local_code_OldXBounded_QECert _ _ _ _ c huv
  have ha := Nat.left_le_pair A k
  have hc := Nat.right_le_pair c.val (2*Nat.pair A k)
  omega
private theorem pathChain_reverse_eq {V E : Type} [Fintype E] [DecidableEq E]
    {start finish : E → V} {u v : V} (p : UndirectedPath start finish u v) :
    pathChain p.reverse=pathChain p := by
  induction p with
  | nil => rfl
  | @step a b p edge connects ih =>
    let reversedEdge : UndirectedPath start finish b a :=
      .step .nil edge (by
        rcases connects with h | h
        · exact Or.inr h
        · exact Or.inl h)
    change pathChain (reversedEdge.append p.reverse)=pathChain p+Pi.single edge (1:F)
    rw [pathChain_append_eq,ih]
    change (0+Pi.single edge (1:F))+pathChain p=pathChain p+Pi.single edge (1:F)
    simpa only [zero_add] using add_comm (Pi.single edge (1:F)) (pathChain p)
theorem exists_path_substitution_OldXCore_QECert {V E V' E' : Type}
    [Fintype E'] [DecidableEq E']
    {start finish : E → V} {start' finish' : E' → V'}
    (f : V → V') (P : E' → Prop)
    (segments : ∀ e, ∃ p : UndirectedPath start' finish'
      (f (start e)) (f (finish e)), ∀ e', pathChain p e'≠0 → P e')
    {u v : V} (p : UndirectedPath start finish u v) :
    ∃ p' : UndirectedPath start' finish' (f u) (f v),
      ∀ e', pathChain p' e'≠0 → P e' := by
  induction p with
  | nil =>
    refine ⟨.nil,?_⟩
    intro e he
    exact False.elim (he (by simp [pathChain]))
  | @step a b p edge connects ih =>
    obtain ⟨initialPath,hprefix⟩ := ih
    obtain ⟨segment,hsegment⟩ := segments edge
    rcases connects with h | h
    · rcases h with ⟨hstart,hend⟩
      cases hstart
      cases hend
      exact ⟨initialPath.append segment,
        path_append_support P initialPath segment hprefix hsegment⟩
    · rcases h with ⟨hstart,hend⟩
      cases hstart
      cases hend
      refine ⟨initialPath.append segment.reverse,
        path_append_support P initialPath segment.reverse hprefix ?_⟩
      intro e he
      apply hsegment e
      simpa only [pathChain_reverse_eq] using he
theorem seedRadial_start_code_OldXCore_QECert (j : Fin 2) :
    baseVertexCode (xStarEdgeStart baseTannerSquarePresentation 0 (seedRadial j)).val=0 := by
  fin_cases j <;> decide
theorem seedRadial_end_code_OldXCore_QECert (j : Fin 2) :
    baseVertexCode (xStarEdgeEnd baseTannerSquarePresentation 0 (seedRadial j)).val=
      4*j.val+1 := by
  fin_cases j <;> decide
theorem stripFace_qz1_start_code_OldXCore_QECert (j : Fin 2) (x : BaseX) :
    baseVertexCode (xStarEdgeStart baseTannerSquarePresentation x
      (xStarFaceQZEdge baseTannerSquarePresentation x (stripFace j x) 1)).val=17 := by
  fin_cases j <;> fin_cases x <;> decide
theorem encoded_old_X_OldXCore_QECert (S : OddScale) (x : BaseX)
    (c : BDL26FiniteTannerSquare.Two)
    (v : SubdivisionVertex baseTannerSquarePresentation x S) :
    Encodable.encode (⟨x,(c,v)⟩ : (BDL26LevelTwoDecoder.executableLevelOne S).X)=
      Nat.pair x.val (Nat.pair c.val (subVertexCode x S v)) := by
  rcases v with ⟨v,hv⟩ | ⟨⟨e,he⟩,i⟩ | ⟨f,i,j⟩
  · cases v with
    | x a => rfl
    | q a =>
      change Nat.pair x.val (Nat.pair c.val (2*(2*(2*a.val)+1)))=
        Nat.pair x.val (Nat.pair c.val (2*(4*a.val+1)))
      apply congrArg (fun n => Nat.pair x.val (Nat.pair c.val n))
      omega
    | z a =>
      change Nat.pair x.val (Nat.pair c.val (2*(2*(2*a.val+1)+1)))=
        Nat.pair x.val (Nat.pair c.val (2*(4*a.val+3)))
      apply congrArg (fun n => Nat.pair x.val (Nat.pair c.val n))
      omega
  · cases e with
    | inl a =>
      change Nat.pair x.val (Nat.pair c.val
        (2*(2*Nat.pair (2*Nat.pair a.val.1.val a.val.2.val) i.val)+1))=
        Nat.pair x.val (Nat.pair c.val
          (4*Nat.pair (2*Nat.pair a.val.1.val a.val.2.val) i.val+1))
      apply congrArg (fun n => Nat.pair x.val (Nat.pair c.val n))
      omega
    | inr a =>
      change Nat.pair x.val (Nat.pair c.val
        (2*(2*Nat.pair (2*Nat.pair a.val.1.val a.val.2.val+1) i.val)+1))=
        Nat.pair x.val (Nat.pair c.val
          (4*Nat.pair (2*Nat.pair a.val.1.val a.val.2.val+1) i.val+1))
      apply congrArg (fun n => Nat.pair x.val (Nat.pair c.val n))
      omega
  · change Nat.pair x.val (Nat.pair c.val
      (2*(2*Nat.pair f.val.val (Nat.pair i.val j.val)+1)+1))=
        Nat.pair x.val (Nat.pair c.val
          (4*Nat.pair f.val.val (Nat.pair i.val j.val)+3))
    apply congrArg (fun n => Nat.pair x.val (Nat.pair c.val n))
    omega
theorem encoded_old_local_Q_OldXCore_QECert (S : OddScale) (x : BaseX)
    (c : BDL26FiniteTannerSquare.Two)
    (e : SubdivisionEdge baseTannerSquarePresentation x S) :
    Encodable.encode (.inl ⟨x,.inl (c,e)⟩ :
      (BDL26LevelTwoDecoder.executableLevelOne S).Q)=
      2*Nat.pair x.val (2*Nat.pair c.val (subEdgeCode x S e)) := by
  rcases e with ⟨⟨e,he⟩,i⟩ | ⟨f,i,j⟩ | ⟨f,i,j⟩
  · cases e <;> rfl
  · change 2*Nat.pair x.val (2*Nat.pair c.val
      (2*(2*Nat.pair f.val.val (Nat.pair i.val j.val))+1))=
        2*Nat.pair x.val (2*Nat.pair c.val
          (4*Nat.pair f.val.val (Nat.pair i.val j.val)+1))
    apply congrArg (fun n => 2*Nat.pair x.val (2*Nat.pair c.val n))
    omega
  · change 2*Nat.pair x.val (2*Nat.pair c.val
      (2*(2*Nat.pair f.val.val (Nat.pair i.val j.val)+1)+1))=
        2*Nat.pair x.val (2*Nat.pair c.val
          (4*Nat.pair f.val.val (Nat.pair i.val j.val)+3))
    apply congrArg (fun n => 2*Nat.pair x.val (2*Nat.pair c.val n))
    omega
theorem oldLargestX_start_le_OldXBounded_QECert (S : OddScale) (x : BaseX)
    (e : DoubleCylinderEdge baseTannerSquarePresentation x S) :
    Encodable.encode (oldLocalStart S x e : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (oldLargestX S (.inl ⟨x,e⟩) :
        (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
  exact code_larger_left_OldXBounded_QECert
    (oldLocalStart S x e : (BDL26LevelTwoDecoder.executableLevelOne S).X)
    (oldLocalEnd S x e)
theorem oldLargestX_end_le_OldXCore_QECert (S : OddScale) (x : BaseX)
    (e : DoubleCylinderEdge baseTannerSquarePresentation x S) :
    Encodable.encode (oldLocalEnd S x e : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (oldLargestX S (.inl ⟨x,e⟩) :
        (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
  exact code_larger_right_OldXBounded_QECert
    (oldLocalStart S x e : (BDL26LevelTwoDecoder.executableLevelOne S).X)
    (oldLocalEnd S x e)
theorem encoded_largePorts_OldXCore_QECert (S : OddScale)
    (c : BDL26FiniteTannerSquare.Two) (depth : Option (Fin (S.half-1)))
    (r : (RawOne S).Q) :
    Encodable.encode (executableCoordinate S (.inr ⟨r,largePorts S c depth r⟩))=
      match depth with
      | none => 2*Nat.pair
          (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
          (Nat.pair c.val (2*(2*Encodable.encode (oldLargestX S r :
            (BDL26LevelTwoDecoder.executableLevelOne S).X)+1)))+1
      | some i => 2*Nat.pair
          (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
          (Nat.pair c.val (2*Nat.pair (Encodable.encode (oldLargestX S r :
            (BDL26LevelTwoDecoder.executableLevelOne S).X)) i.val+1))+1 := by
  cases depth with
  | none => exact encoded_endpoint_OldXCore_QECert S r (oldLargestX S r) (oldLargestX_incident S r) c
  | some i => exact encoded_interior_OldXBounded_QECert S r (oldLargestX S r) (oldLargestX_incident S r) c i
theorem terminalOldKernel_gamma_OldXBounded_QECert (S : OddScale) (j : Fin 2) :
    terminalOldKernel S j (gammaRadial S j (lastSegment S))=1 :=
  terminalOldKernel_target_OldXBounded_QECert S j 0
theorem encoded_chosenPort_OldXCore_QECert (S : OddScale) (r : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (c : BDL26FiniteTannerSquare.Two) (depth : Option (Fin (S.half-1))) :
    Encodable.encode (executableCoordinate S
      (.inr ⟨r,chosenPort (RawOne S) S r x hx c depth⟩))=
      match depth with
      | none => 2*Nat.pair
          (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
          (Nat.pair c.val (2*(2*Encodable.encode (x :
            (BDL26LevelTwoDecoder.executableLevelOne S).X)+1)))+1
      | some i => 2*Nat.pair
          (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
          (Nat.pair c.val (2*Nat.pair (Encodable.encode (x :
            (BDL26LevelTwoDecoder.executableLevelOne S).X)) i.val+1))+1 := by
  cases depth with
  | none => exact encoded_endpoint_OldXCore_QECert S r x hx c
  | some i => exact encoded_interior_OldXBounded_QECert S r x hx c i
theorem direct_port_path_property_OldXBounded_QECert (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (r : P.Q) (x : P.X) (z : P.Z)
    (hx : P.xq x r=true) (hz : P.qz r z=true) (c : BDL26FiniteTannerSquare.Two)
    (depth : Option (Fin (S.half-1)))
    (property : ZDoubleCylinderEdge P z S → Prop)
    (hproperty : ∀ (a : XStarEdge (transposePresentation P) z) (k : Fin S.half),
      (a.val=Sum.inl ⟨(z,r),hz⟩ ∨ a.val=Sum.inr ⟨(r,x),hx⟩) →
        property (.inl (c,.inl (a,k)))) :
    ∃ p : UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
      (zCenter P S z c)
      (qToZDoubleCylinderVertex P A r z hz S (chosenPort P S r x hx c depth)),
      ∀ e, pathChain p e≠0 → property e := by
  obtain ⟨p,hp⟩ := exists_direct_port_path P A S r x z hx hz c depth
  refine ⟨p,?_⟩
  intro e he
  obtain ⟨a,k,rfl,ha⟩ := hp e he
  exact hproperty a k ha
theorem between_direct_ports_OldXCore_QECert (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (r0 r : P.Q) (x0 x : P.X)
    (z : P.Z) (hx0 : P.xq x0 r0=true) (hx : P.xq x r=true)
    (hz0 : P.qz r0 z=true) (hz : P.qz r z=true)
    (c : BDL26FiniteTannerSquare.Two) (depth : Option (Fin (S.half-1))) :
    Nonempty (UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
      (qToZDoubleCylinderVertex P A r0 z hz0 S (chosenPort P S r0 x0 hx0 c depth))
      (qToZDoubleCylinderVertex P A r z hz S (chosenPort P S r x hx c depth))) := by
  obtain ⟨p0,_⟩ := exists_direct_port_path P A S r0 x0 z hx0 hz0 c depth
  obtain ⟨p,_⟩ := exists_direct_port_path P A S r x z hx hz c depth
  exact ⟨p0.reverse.append p⟩
private theorem directPaths_support (S : OddScale) (c : BDL26FiniteTannerSquare.Two)
    (depth : Option (Fin (S.half-1))) (r : (RawOne S).Q) (z : (RawOne S).Z)
    (hz : (RawOne S).qz r z=true) (e : ZDoubleCylinderEdge (RawOne S) z S)
    (he : pathChain (directPaths S c depth r z hz) e≠0) :
    ∃ (a : XStarEdge (transposePresentation (RawOne S)) z) (k : Fin S.half),
      e=.inl (c,.inl (a,k)) ∧
        (a.val=Sum.inl ⟨(z,r),hz⟩ ∨
          a.val=Sum.inr ⟨(r,oldLargestX S r),oldLargestX_incident S r⟩) :=
  Classical.choose_spec (exists_direct_port_path (RawOne S)
    (rxState S baseState).admissible.toTannerSquareAdmissible S r (oldLargestX S r) z
    (oldLargestX_incident S r) hz c depth) e he
private theorem cast_rz_root_segment (S : OddScale) {P Q : TannerSquarePresentation}
    (h : P=Q) (r : Q.Q) (z : Q.Z) (hz : Q.qz r z=true)
    (hm : xStarEdgeMember (transposePresentation Q) z (Sum.inl ⟨(z,r),hz⟩)=true)
    (c : BDL26FiniteTannerSquare.Two) (k : Fin S.half) :
    cast (congrArg (fun P => RZQ P S) h).symm
      (.inl ⟨z,.inl (c,.inl (⟨Sum.inl ⟨(z,r),hz⟩,hm⟩,k))⟩)=
      .inl ⟨cast (congrArg TannerSquarePresentation.Z h).symm z,
        .inl (c,.inl (⟨Sum.inl
          ⟨(cast (congrArg TannerSquarePresentation.Z h).symm z,
            cast (congrArg TannerSquarePresentation.Q h).symm r),cast_qz h r z hz⟩,
          cast_root_star_member h r z hz hm⟩,k))⟩ := by
  cases h
  rfl
private theorem encoded_root_segment (S : OddScale) (r : (RawOne S).Q)
    (z : (RawOne S).Z) (hz : (RawOne S).qz r z=true)
    (hm : xStarEdgeMember (transposePresentation (RawOne S)) z
      (Sum.inl ⟨(z,r),hz⟩)=true)
    (c : BDL26FiniteTannerSquare.Two) (k : Fin S.half) :
    Encodable.encode (executableCoordinate S
      (.inl ⟨z,.inl (c,.inl (⟨Sum.inl ⟨(z,r),hz⟩,hm⟩,k))⟩))=
      2*Nat.pair (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
        (2*Nat.pair c.val (2*Nat.pair
          (2*Nat.pair
            (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
            (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))) k.val)) := by
  change Encodable.encode (cast (congrArg (fun P => RZQ P S)
    (executableLevelOne_eq_raw S)).symm _) = _
  erw [cast_rz_root_segment S (executableLevelOne_eq_raw S) r z hz hm c k]
  rfl
private theorem cast_rz_x_segment (S : OddScale) {P Q : TannerSquarePresentation}
    (h : P=Q) (r : Q.Q) (x : Q.X) (hx : Q.xq x r=true) (z : Q.Z)
    (hm : xStarEdgeMember (transposePresentation Q) z (Sum.inr ⟨(r,x),hx⟩)=true)
    (c : BDL26FiniteTannerSquare.Two) (k : Fin S.half) :
    cast (congrArg (fun P => RZQ P S) h).symm
      (.inl ⟨z,.inl (c,.inl (⟨Sum.inr ⟨(r,x),hx⟩,hm⟩,k))⟩)=
      .inl ⟨cast (congrArg TannerSquarePresentation.Z h).symm z,
        .inl (c,.inl (⟨Sum.inr
          ⟨(cast (congrArg TannerSquarePresentation.Q h).symm r,
            cast (congrArg TannerSquarePresentation.X h).symm x),cast_xq h r x hx⟩,
          cast_x_star_member h r x hx z hm⟩,k))⟩ := by
  cases h
  rfl
private theorem encoded_x_segment (S : OddScale) (r : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true) (z : (RawOne S).Z)
    (hm : xStarEdgeMember (transposePresentation (RawOne S)) z
      (Sum.inr ⟨(r,x),hx⟩)=true)
    (c : BDL26FiniteTannerSquare.Two) (k : Fin S.half) :
    Encodable.encode (executableCoordinate S
      (.inl ⟨z,.inl (c,.inl (⟨Sum.inr ⟨(r,x),hx⟩,hm⟩,k))⟩))=
      2*Nat.pair (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
        (2*Nat.pair c.val (2*Nat.pair
          (2*Nat.pair
            (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
            (Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X))+1) k.val)) := by
  change Encodable.encode (cast (congrArg (fun P => RZQ P S)
    (executableLevelOne_eq_raw S)).symm _) = _
  erw [cast_rz_x_segment S (executableLevelOne_eq_raw S) r x hx z hm c k]
  rfl
private theorem chosen_code_before_root {m : Nat} (r x z A k : Nat)
    (c : BDL26FiniteTannerSquare.Two) (depth : Option (Fin m))
    (hr : r<A) (hx : x<A) (hA : 1<A)
    (hi : ∀ i, depth=some i → i.val<A) :
    (match depth with
      | none => 2*Nat.pair r (Nat.pair c.val (2*(2*x+1)))+1
      | some i => 2*Nat.pair r (Nat.pair c.val (2*Nat.pair x i.val+1))+1)<
      2*Nat.pair z (2*Nat.pair c.val (2*Nat.pair A k)) := by
  cases depth with
  | none => exact endpoint_before_any_root_code r x z A k c hr hx hA
  | some i => exact interior_before_any_root_code r x z A i.val k c hr hx (hi i rfl)
private theorem pair_parameter_bounds (r a b : Nat) (hr : 0<r) (h : r≤ max a b) :
    r<2*Nat.pair a b ∧ r^2<2*Nat.pair a b ∧ 1<2*Nat.pair a b := by
  have hsq := Nat.pow_le_pow_left h 2
  have hl := Nat.max_sq_add_min_le_pair a b
  have hself : r≤r^2 := Nat.le_self_pow (by decide) r
  have hpos : 0<r^2 := by positivity
  omega
private theorem direct_root_segment_later (S : OddScale)
    (r0 r : (RawOne S).Q) (x0 x : (RawOne S).X)
    (hx0 : (RawOne S).xq x0 r0=true) (hx : (RawOne S).xq x r=true)
    (z : (RawOne S).Z) (hz : (RawOne S).qz r z=true)
    (c : BDL26FiniteTannerSquare.Two) (depth : Option (Fin (S.half-1)))
    (K : Nat) (hK : 0<K)
    (hr : K≤Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
    (hr0 : Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q)≤K^2)
    (hX0 : Encodable.encode (x0 : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤K^2)
    (hi : ∀ i, depth=some i → i.val<K^2)
    (hm : xStarEdgeMember (transposePresentation (RawOne S)) z
      (Sum.inl ⟨(z,r),hz⟩)=true) (k : Fin S.half) :
    Encodable.encode (executableCoordinate S
      (.inr ⟨r0,chosenPort (RawOne S) S r0 x0 hx0 c depth⟩))<
      Encodable.encode (executableCoordinate S
      (.inl ⟨z,.inl (c,.inl (⟨Sum.inl ⟨(z,r),hz⟩,hm⟩,k))⟩)) := by
  have hroot := pair_parameter_bounds K
    (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
    (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)) hK
    (hr.trans (Nat.le_max_right _ _))
  have hnum := chosen_code_before_root
    (Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
    (Encodable.encode (x0 : (BDL26LevelTwoDecoder.executableLevelOne S).X))
    (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
    (2*Nat.pair
      (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
      (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)))
    k.val c depth (hr0.trans_lt hroot.2.1) (hX0.trans_lt hroot.2.1)
    hroot.2.2 (fun i he => (hi i he).trans hroot.2.1)
  cases depth with
  | none =>
      exact (encoded_chosenPort_OldXCore_QECert S r0 x0 hx0 c none).trans_lt
        (hnum.trans_eq (encoded_root_segment S r z hz hm c k).symm)
  | some i =>
      exact (encoded_chosenPort_OldXCore_QECert S r0 x0 hx0 c (some i)).trans_lt
        (hnum.trans_eq (encoded_root_segment S r z hz hm c k).symm)
private theorem direct_x_segment_later (S : OddScale)
    (r0 r : (RawOne S).Q) (x0 x : (RawOne S).X)
    (hx0 : (RawOne S).xq x0 r0=true) (hx : (RawOne S).xq x r=true)
    (z : (RawOne S).Z) (hz : (RawOne S).qz r z=true)
    (c : BDL26FiniteTannerSquare.Two) (depth : Option (Fin (S.half-1)))
    (K : Nat) (hK : 0<K)
    (hr : K≤Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
    (hr0 : Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q)≤K^2)
    (hX0 : Encodable.encode (x0 : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤K^2)
    (hi : ∀ i, depth=some i → i.val<K^2)
    (hm : xStarEdgeMember (transposePresentation (RawOne S)) z
      (Sum.inr ⟨(r,x),hx⟩)=true) (k : Fin S.half) :
    Encodable.encode (executableCoordinate S
      (.inr ⟨r0,chosenPort (RawOne S) S r0 x0 hx0 c depth⟩))<
      Encodable.encode (executableCoordinate S
      (.inl ⟨z,.inl (c,.inl (⟨Sum.inr ⟨(r,x),hx⟩,hm⟩,k))⟩)) := by
  let R := Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)
  let X := Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)
  have harm := pair_parameter_bounds K R X hK (hr.trans (Nat.le_max_left R X))
  have hR : Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q)<
      2*Nat.pair R X+1 := hr0.trans_lt (harm.2.1.trans_le (Nat.le_succ _))
  have hX : Encodable.encode (x0 : (BDL26LevelTwoDecoder.executableLevelOne S).X)<
      2*Nat.pair R X+1 := hX0.trans_lt (harm.2.1.trans_le (Nat.le_succ _))
  have hnum := chosen_code_before_root
    (Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
    (Encodable.encode (x0 : (BDL26LevelTwoDecoder.executableLevelOne S).X))
    (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
    (2*Nat.pair R X+1) k.val c depth hR hX (by omega)
    (fun i he => (hi i he).trans (harm.2.1.trans_le (Nat.le_succ _)))
  cases depth with
  | none =>
      exact (encoded_chosenPort_OldXCore_QECert S r0 x0 hx0 c none).trans_lt
        (hnum.trans_eq (encoded_x_segment S r x hx z hm c k).symm)
  | some i =>
      exact (encoded_chosenPort_OldXCore_QECert S r0 x0 hx0 c (some i)).trans_lt
        (hnum.trans_eq (encoded_x_segment S r x hx z hm c k).symm)
theorem direct_segment_later_OldXBounded_QECert (S : OddScale)
    (r0 r : (RawOne S).Q) (x0 x : (RawOne S).X)
    (hx0 : (RawOne S).xq x0 r0=true) (hx : (RawOne S).xq x r=true)
    (z : (RawOne S).Z) (hz : (RawOne S).qz r z=true)
    (c : BDL26FiniteTannerSquare.Two) (depth : Option (Fin (S.half-1)))
    (K : Nat) (hK : 0<K)
    (hr : K≤Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
    (hr0 : Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q)≤K^2)
    (hX0 : Encodable.encode (x0 : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤K^2)
    (hi : ∀ i, depth=some i → i.val<K^2)
    (a : XStarEdge (transposePresentation (RawOne S)) z) (k : Fin S.half)
    (ha : a.val=Sum.inl ⟨(z,r),hz⟩ ∨ a.val=Sum.inr ⟨(r,x),hx⟩) :
    Encodable.encode (executableCoordinate S
      (.inr ⟨r0,chosenPort (RawOne S) S r0 x0 hx0 c depth⟩))<
      Encodable.encode (executableCoordinate S (.inl ⟨z,.inl (c,.inl (a,k))⟩)) := by
  rcases a with ⟨a,hm⟩
  rcases ha with ha | ha
  · change a=_ at ha
    subst a
    exact direct_root_segment_later S r0 r x0 x hx0 hx z hz c depth
      K hK hr hr0 hX0 hi hm k
  · change a=_ at ha
    subst a
    exact direct_x_segment_later S r0 r x0 x hx0 hx z hz c depth
      K hK hr hr0 hX0 hi hm k
private theorem largePorts_eq_chosen (S : OddScale) (c : BDL26FiniteTannerSquare.Two)
    (depth : Option (Fin (S.half-1))) (r : (RawOne S).Q) :
    largePorts S c depth r=chosenPort (RawOne S) S r (oldLargestX S r)
      (oldLargestX_incident S r) c depth := by
  cases depth <;> rfl
theorem directPaths_later_OldXBounded_QECert (S : OddScale) (c : BDL26FiniteTannerSquare.Two)
    (depth : Option (Fin (S.half-1))) (r0 r : (RawOne S).Q) (z : (RawOne S).Z)
    (hz : (RawOne S).qz r z=true)
    (hr0 : 0<Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
    (hrr : Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q)≤
      Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
    (hx0 : Encodable.encode (oldLargestX S r0 :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      (Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q))^2)
    (hi : ∀ i, depth=some i → i.val<
      (Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q))^2)
    (e : ZDoubleCylinderEdge (RawOne S) z S)
    (he : pathChain (directPaths S c depth r z hz) e≠0) :
    Encodable.encode (executableCoordinate S (.inr ⟨r0,largePorts S c depth r0⟩))<
      Encodable.encode (executableCoordinate S (.inl ⟨z,e⟩)) := by
  obtain ⟨a,k,heq,ha⟩ := directPaths_support S c depth r z hz e he
  rw [heq,largePorts_eq_chosen]
  exact direct_segment_later_OldXBounded_QECert S r0 r (oldLargestX S r0) (oldLargestX S r)
    (oldLargestX_incident S r0) (oldLargestX_incident S r) z hz c depth
    (Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
    hr0 hrr (Nat.le_self_pow (by decide) _) hx0 hi a k ha
theorem pair_zero_left_sq_OldXCore_QECert (n : Nat) : Nat.pair 0 n=n^2 := by
  rw [Nat.pair]
  split_ifs with h
  · ring
  · have hn : n=0 := by omega
    subst n
    rfl
theorem encoded_gammaRadial_OldXCore_QECert (S : OddScale) (j : Fin 2) (n : Fin S.half) :
    Encodable.encode (gammaRadial S j n :
      (BDL26LevelTwoDecoder.executableLevelOne S).Q)=
      128*(Nat.pair (2*j.val) n.val)^4 := by
  erw [gammaRadial,encoded_old_local_Q_OldXCore_QECert]
  change 2*Nat.pair 0 (2*Nat.pair 0
    (2*Nat.pair (2*Nat.pair 0 j.val) n.val))=128*(Nat.pair (2*j.val) n.val)^4
  simp only [pair_zero_left_sq_OldXCore_QECert]
  fin_cases j <;> norm_num <;> ring
theorem pair_mono_right_OldXCore_QECert (a b d : Nat) (h : b≤d) :
    Nat.pair a b≤Nat.pair a d := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact (Nat.pair_lt_pair_right a h).le
  · exact le_rfl
theorem seedRadial_code_OldXCore_QECert (j : Fin 2) :
    baseEdgeCode (seedRadial j).val=2*j.val := by
  fin_cases j <;> decide
theorem encoded_old_X_copy0_OldXCore_QECert (S : OddScale)
    (v : SubdivisionVertex baseTannerSquarePresentation (0 : BaseX) S) :
    Encodable.encode (⟨(0 : BaseX),(0,v)⟩ :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)=(subVertexCode 0 S v)^4 := by
  calc
    _ = Nat.pair 0 (Nat.pair 0 (subVertexCode 0 S v)) := encoded_old_X_OldXCore_QECert S 0 0 v
    _ = (subVertexCode 0 S v)^4 := by
      simp only [pair_zero_left_sq_OldXCore_QECert]
      ring
private theorem radial_tag_fourth_bound (p v : Nat) (hp : 0<p)
    (hv : v≤4*p+1 ∨ v≤10) : v^4≤(128*p^4)^2 := by
  have hp4 : 1≤p^4 := Nat.succ_le_of_lt (pow_pos hp 4)
  have hself : p^4≤(p^4)^2 := Nat.le_self_pow (by decide) (p^4)
  rcases hv with hv | hv
  · have hv' : v≤5*p := by omega
    have hpow := Nat.pow_le_pow_left hv' 4
    have hscaled : (5*p)^4=625*p^4 := by ring
    rw [hscaled] at hpow
    have hbig : 625*p^4≤(128*p^4)^2 := by nlinarith
    exact hpow.trans hbig
  · have hpow := Nat.pow_le_pow_left hv 4
    have hbig : 10^4≤(128*p^4)^2 := by nlinarith
    exact hpow.trans hbig
theorem gammaLargestX_le_square_OldXCore_QECert (S : OddScale) (j : Fin 2) (n : Fin S.half)
    (hn : 0<j.val+n.val) :
    Encodable.encode (oldLargestX S (gammaRadial S j n) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      (Encodable.encode (gammaRadial S j n :
        (BDL26LevelTwoDecoder.executableLevelOne S).Q))^2 := by
  let p := Nat.pair (2*j.val) n.val
  have hp : 0<p := by
    have hleft := Nat.left_le_pair (2*j.val) n.val
    have hright := Nat.right_le_pair (2*j.val) n.val
    dsimp [p]
    omega
  have hstart : Encodable.encode (oldLocalStart S 0
      (.inl (0,.inl (seedRadial j,n))) :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)≤(128*p^4)^2 := by
    change Encodable.encode (⟨(0 : BaseX),(0,
      subdivisionSegmentStart baseTannerSquarePresentation 0 S (seedRadial j) n)⟩ :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)≤_
    erw [encoded_old_X_copy0_OldXCore_QECert]
    unfold subdivisionSegmentStart
    split_ifs with hzero
    · erw [seedRadial_start_OldXBounded_QECert]
      change (0 : Nat)≤_
      exact Nat.zero_le _
    · apply radial_tag_fourth_bound p _ hp
      left
      change 4*Nat.pair (baseEdgeCode (seedRadial j).val) (n.val-1)+1≤4*p+1
      rw [seedRadial_code_OldXCore_QECert]
      have hm := pair_mono_right_OldXCore_QECert (2*j.val) (n.val-1) n.val (Nat.sub_le _ _)
      dsimp [p]
      omega
  have hend : Encodable.encode (oldLocalEnd S 0
      (.inl (0,.inl (seedRadial j,n))) :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)≤(128*p^4)^2 := by
    change Encodable.encode (⟨(0 : BaseX),(0,
      subdivisionSegmentEnd baseTannerSquarePresentation 0 S (seedRadial j) n)⟩ :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)≤_
    erw [encoded_old_X_copy0_OldXCore_QECert]
    unfold subdivisionSegmentEnd
    split_ifs with hlast
    · apply radial_tag_fourth_bound p _ hp
      right
      change 2*(4*j.val+1)≤10
      have := j.isLt
      omega
    · apply radial_tag_fourth_bound p _ hp
      left
      change 4*Nat.pair (baseEdgeCode (seedRadial j).val) n.val+1≤4*p+1
      rw [seedRadial_code_OldXCore_QECert]
  erw [encoded_gammaRadial_OldXCore_QECert]
  change Encodable.encode (oldLargestX S (.inl ⟨(0 : BaseX),
    .inl (0,.inl (seedRadial j,n))⟩) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤(128*p^4)^2
  exact code_larger_upper_OldXBounded_QECert _ _ _ hstart hend
theorem gamma_index_le_code_OldXBounded_QECert (S : OddScale) (j : Fin 2) (n : Fin S.half) :
    n.val≤Encodable.encode (gammaRadial S j n :
      (BDL26LevelTwoDecoder.executableLevelOne S).Q) := by
  erw [encoded_gammaRadial_OldXCore_QECert]
  have hright := Nat.right_le_pair (2*j.val) n.val
  have hself : Nat.pair (2*j.val) n.val≤(Nat.pair (2*j.val) n.val)^4 :=
    Nat.le_self_pow (by decide) _
  omega
theorem gamma_code_pos_OldXCore_QECert (S : OddScale) (j : Fin 2) (n : Fin S.half)
    (hn : 0<j.val+n.val) :
    0<Encodable.encode (gammaRadial S j n :
      (BDL26LevelTwoDecoder.executableLevelOne S).Q) := by
  erw [encoded_gammaRadial_OldXCore_QECert]
  have hleft := Nat.left_le_pair (2*j.val) n.val
  have hright := Nat.right_le_pair (2*j.val) n.val
  have hp : 0<Nat.pair (2*j.val) n.val := by omega
  positivity
theorem pair_mono_left_OldXCore_QECert (a b d : Nat) (h : a≤b) :
    Nat.pair a d≤Nat.pair b d := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact (Nat.pair_lt_pair_left d h).le
  · exact le_rfl
theorem largePorts_later_OldXCore_QECert (S : OddScale) (c : BDL26FiniteTannerSquare.Two)
    (depth : Option (Fin (S.half-1))) (r0 r : (RawOne S).Q) (hne : r≠r0)
    (hr : Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q)≤
      Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
    (hx : Encodable.encode (oldLargestX S r0 :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (oldLargestX S r :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)) :
    Encodable.encode (executableCoordinate S (.inr ⟨r0,largePorts S c depth r0⟩))<
      Encodable.encode (executableCoordinate S (.inr ⟨r,largePorts S c depth r⟩)) := by
  have hR : Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q)<
      Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q) := by
    have hne' : Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q)≠
        Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q) :=
      fun he => hne (Encodable.encode_injective he).symm
    omega
  cases depth with
  | none =>
    rw [encoded_largePorts_OldXCore_QECert,encoded_largePorts_OldXCore_QECert]
    dsimp only
    have ht := pair_mono_right_OldXCore_QECert c.val
      (2*(2*Encodable.encode (oldLargestX S r0 :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)+1))
      (2*(2*Encodable.encode (oldLargestX S r :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)+1)) (by omega)
    have hfirst := Nat.pair_lt_pair_left
      (Nat.pair c.val (2*(2*Encodable.encode (oldLargestX S r0 :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)+1))) hR
    have hsecond := pair_mono_right_OldXCore_QECert
      (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)) _ _ ht
    omega
  | some i =>
    rw [encoded_largePorts_OldXCore_QECert,encoded_largePorts_OldXCore_QECert]
    dsimp only
    have ht0 := pair_mono_left_OldXCore_QECert
      (Encodable.encode (oldLargestX S r0 : (BDL26LevelTwoDecoder.executableLevelOne S).X))
      (Encodable.encode (oldLargestX S r : (BDL26LevelTwoDecoder.executableLevelOne S).X))
      i.val hx
    have ht := pair_mono_right_OldXCore_QECert c.val
      (2*Nat.pair (Encodable.encode (oldLargestX S r0 :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)) i.val+1)
      (2*Nat.pair (Encodable.encode (oldLargestX S r :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)) i.val+1) (by omega)
    have hfirst := Nat.pair_lt_pair_left
      (Nat.pair c.val (2*Nat.pair (Encodable.encode (oldLargestX S r0 :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)) i.val+1)) hR
    have hsecond := pair_mono_right_OldXCore_QECert
      (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)) _ _ ht
    omega
theorem interior_before_far_last_radial_code_OldXCore_QECert (r x z A i k : Nat)
    (c : BDL26FiniteTannerSquare.Two) (hri : r< i) (hxi : x< i) (hik : i<k) :
    2*Nat.pair r (Nat.pair c.val (2*Nat.pair x i+1))+1 <
      2*Nat.pair z (2*Nat.pair c.val (2*Nat.pair A k)) := by
  have hp : Nat.pair x i=i*i+x := by simp [Nat.pair,hxi]
  have hik' : i+1≤k := by omega
  have hs := Nat.pow_le_pow_left hik' 2
  have hm := Nat.pow_le_pow_left (Nat.le_max_right A k) 2
  have hl := Nat.max_sq_add_min_le_pair A k
  have hsquare : (i+1)^2≤Nat.pair A k :=
    hs.trans (hm.trans ((Nat.le_add_right _ _).trans hl))
  have huv : 2*Nat.pair x i+1<2*Nat.pair A k := by
    rw [hp]
    nlinarith [hsquare]
  apply q_before_local_code_OldXBounded_QECert _ _ _ _ c huv
  have hk := Nat.right_le_pair A k
  have hc := Nat.right_le_pair c.val (2*Nat.pair A k)
  omega
theorem old_X_coordinate_eq_OldXBounded_QECert (S : OddScale) (x y : BaseX)
    (c d : BDL26FiniteTannerSquare.Two)
    (u : SubdivisionVertex baseTannerSquarePresentation x S)
    (v : SubdivisionVertex baseTannerSquarePresentation y S) :
    ((⟨x,(c,u)⟩ : RX0 baseTannerSquarePresentation S)=⟨y,(d,v)⟩) ↔
      x=y ∧ c=d ∧ HEq u v := by
  constructor
  · intro h
    rcases Sigma.mk.inj_iff.mp h with ⟨rfl,hpair⟩
    have hp := eq_of_heq hpair
    exact ⟨rfl,congrArg Prod.fst hp,heq_of_eq (congrArg Prod.snd hp)⟩
  · rintro ⟨rfl,rfl,h⟩
    have hv := eq_of_heq h
    cases hv
    rfl
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
end
end


