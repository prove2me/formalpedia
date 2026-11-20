-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_LiteralPart4_QECert
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_LiteralPart4_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T12:15:06.507098+00:00
-- url     : https://prove2.me/theorems/2b81ef71-5224-4e98-a9ef-e69def607426
-- title:
--   RX primitive C2Q endpoint: literal segment 4
-- statement:
--   Definitions and structural lemmas for RXPrimitive C2 QEndpoint, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_LiteralPart3_QECert
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


set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph BDL26LevelTwoCode
open BDL26ActualFailureReadout BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26OwnerIncidenceMasks
open BDL26TransposedStoppedDecoder BDL26CSSHamiltonian
open scoped Classical
noncomputable section
end
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph BDL26LevelTwoCode
open BDL26ActualFailureReadout BDL26TransposedStoppedDecoder BDL26CSSHamiltonian
open BDL26RZMap1CoordinateBridge BDL26RXPhysicalCoordinateTrace
open scoped Classical
noncomputable section
end
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26ActualFailureReadout BDL26RXPhysicalCoordinateTrace
open scoped Classical
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace OriginalOldXScaleExtension
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RXDecoderAdapter BDL26DecodingGraph
open BDL26TransposedStoppedDecoder BDL26ActualFailureReadout
open scoped Classical BigOperators
noncomputable section
def rayTail (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (copy : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q) (cut : Fin S.half) :
    Word BDL26Field (QDoubleCylinderVertex P q S) :=
  fun v => if v.1=copy then
    match v.2 with
    | .inl (.inl _) => 0
    | .inl (.inr t) => if t=z then 1 else 0
    | .inr (t,j) => if t=z ∧ cut.val ≤ j.val then 1 else 0
  else 0
def wholeCopy (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (copy : BDL26FiniteTannerSquare.Two) : Word BDL26Field (QDoubleCylinderVertex P q S) :=
  fun v => if v.1=copy then 1 else 0
def rayCut (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (copy : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q) (cut : Fin S.half) :
    QDoubleCylinderEdge P q S := .inl (copy,z,cut)
def toggleWord (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (a : QStarEdge P q) (cut0 cut1 : Fin S.half) :
    Word BDL26Field (QDoubleCylinderVertex P q S) :=
  rayTail P q S 0 a cut0+rayTail P q S 1 a cut1
def switchWord (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (a b c : QStarEdge P q) (cut0 : Fin S.half) :
    Word BDL26Field (QDoubleCylinderVertex P q S) :=
  wholeCopy P q S 0+rayTail P q S 0 a cut0+
    rayTail P q S 0 c ⟨0,S.half_pos⟩+rayTail P q S 1 b ⟨0,S.half_pos⟩
end
end OriginalOldXScaleExtension
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace OriginalOldXScaleExtension
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RXDecoderAdapter
open scoped Classical BigOperators
noncomputable section
theorem binary_path_sum (f : Nat → BDL26Field) (n : Nat) :
    (∑ i : Fin n,(f i.val+f (i.val+1)))=f 0+f n := by
  induction n with
  | zero => simp [CharTwo.add_self_eq_zero]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    change (∑ i : Fin n,(f i.val+f (i.val+1)))+(f n+f (n+1))=f 0+f (n+1)
    rw [ih]
    calc
      _=f 0+(f n+f n)+f (n+1) := by abel
      _=_ := by rw [repair3_scalar_add_self,add_zero]
def armValue (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S))
    (copy : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q) (i : Nat) : BDL26Field :=
  if hi : i < S.half then w (copy,qSubdivisionEdgeStart P q S (z,⟨i,hi⟩))
  else w (copy,.inl (.inr z))
theorem armValue_zero (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) (copy : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q) :
    armValue P q S w copy z 0=w (copy,.inl (.inl ())) := by
  simp [armValue,S.half_pos,qSubdivisionEdgeStart,qStarEdgeStart]
theorem armValue_last (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) (copy : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q) :
    armValue P q S w copy z S.half=w (copy,.inl (.inr z)) := by
  simp [armValue]
theorem armValue_step (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S))
    (copy : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q) (i : Fin S.half) :
    armValue P q S w copy z (i.val+1)=w (copy,qSubdivisionEdgeEnd P q S (z,i)) := by
  by_cases hi : i.val+1 < S.half
  · have hl : i.val+1≠S.half := by omega
    have hz : i.val+1≠0 := by omega
    simp [armValue,hi,qSubdivisionEdgeStart,qSubdivisionEdgeEnd,hl,hz]
  · have hl : i.val+1=S.half := by have := i.isLt;omega
    simp [armValue,hi,qSubdivisionEdgeEnd,hl,qStarEdgeEnd]
theorem q_ray_coboundary_sum (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (w : Word BDL26Field (QDoubleCylinderVertex P q S))
    (copy : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q) :
    (∑ k : Fin S.half,wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) w
      (rayCut P q S copy z k))=w (copy,.inl (.inl ()))+w (copy,.inl (.inr z)) := by
  calc
    _=(∑ k : Fin S.half,(armValue P q S w copy z k.val+
        armValue P q S w copy z (k.val+1))) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [qLocalCoboundary_apply,armValue_step]
      simp [armValue,k.isLt,rayCut,qDoubleCylinderEdgeStart,qDoubleCylinderEdgeEnd]
    _=armValue P q S w copy z 0+armValue P q S w copy z S.half := binary_path_sum _ _
    _=_ := by rw [armValue_zero,armValue_last]
def qBoundaryVertex (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (x : P.X) (hxq : P.xq x q=true) (S : OddScale)
    (v : QSubdivisionVertex P q S) : SubdivisionBoundaryVertex P x S := by
  refine ⟨qToXSubdivisionVertex P A q x hxq S v,?_⟩
  rcases v with v | ⟨z,k⟩
  · simpa [qToXSubdivisionVertex,subdivisionBoundaryVertexMember,
      xStarBoundaryVertexToStar] using (qToXBoundaryVertex P A q x hxq v).property
  · simpa [qToXSubdivisionVertex,subdivisionBoundaryVertexMember,
      xStarBoundaryEdgeToStar] using (qToXBoundaryEdge P q x hxq z).property
theorem qBoundaryVertex_start (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (x : P.X)
    (hxq : P.xq x q=true) (S : OddScale) (z : QStarEdge P q) (k : Fin S.half) :
    qBoundaryVertex P A q x hxq S (qSubdivisionEdgeStart P q S (z,k))=
      subdivisionBoundaryEdgeStart P x S (qToXSubdivisionBoundaryEdge P q x hxq S (z,k)) := by
  apply Subtype.ext
  change qToXSubdivisionVertex P A q x hxq S (qSubdivisionEdgeStart P q S (z,k))=_
  rw [subdivisionBoundaryEdgeStart_value]
  exact qToXSubdivisionEdge_start P A q x hxq S (z,k)
theorem qBoundaryVertex_end (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (x : P.X)
    (hxq : P.xq x q=true) (S : OddScale) (z : QStarEdge P q) (k : Fin S.half) :
    qBoundaryVertex P A q x hxq S (qSubdivisionEdgeEnd P q S (z,k))=
      subdivisionBoundaryEdgeEnd P x S (qToXSubdivisionBoundaryEdge P q x hxq S (z,k)) := by
  apply Subtype.ext
  change qToXSubdivisionVertex P A q x hxq S (qSubdivisionEdgeEnd P q S (z,k))=_
  rw [subdivisionBoundaryEdgeEnd_value]
  exact qToXSubdivisionEdge_end P A q x hxq S (z,k)
theorem qBoundaryVertex_terminal (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (x : P.X)
    (hxq : P.xq x q=true) (S : OddScale) (z : QStarEdge P q) :
    (Sum.inr (qBoundaryVertex P A q x hxq S (.inl (.inr z))) : DoubleCylinderEdge P x S)=
      qToXDoubleCylinderEdge P A q x hxq S (Sum.inr z) := by
  apply congrArg Sum.inr
  apply Subtype.ext
  rfl
def rayImage (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (z : QStarEdge P q) (copy : BDL26FiniteTannerSquare.Two) (k : Fin S.half) : RX2 P S :=
  .inl (.inr ⟨q,rayCut P q S copy z k⟩)
def rayFlowSum (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (f : Word BDL26Field (DoubleCylinderEdge P x S))
    (q : P.Q) (z : QStarEdge P q) : BDL26Field :=
  ∑ copy : BDL26FiniteTannerSquare.Two,∑ k : Fin S.half,xFlow P S x f (rayImage P q S z copy k)
theorem rayImage_value (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (x : P.X)
    (q : P.Q) (hxq : P.xq x q=true)
    (f : Word BDL26Field (DoubleCylinderEdge P x S))
    (z : QStarEdge P q) (copy : BDL26FiniteTannerSquare.Two) (k : Fin S.half) :
    xFlow P S x f (rayImage P q S z copy k)=
      f (Sum.inl (copy,(qToXSubdivisionBoundaryEdge P q x hxq S (z,k)).val)) := by
  unfold rayImage rayCut
  rw [xFlow_at_q P A]
  simp only [dif_pos hxq,rxXQDegreeOne,wordPullback_apply]
  rfl
def verticalReadback (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (x : P.X)
    (q : P.Q) (hxq : P.xq x q=true)
    (f : Word BDL26Field (DoubleCylinderEdge P x S)) :
    Word BDL26Field (QDoubleCylinderVertex P q S) :=
  fun v => f (Sum.inr (qBoundaryVertex P A q x hxq S v.2))
theorem rectangle_ray_step (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (x : P.X)
    (q : P.Q) (hxq : P.xq x q=true)
    (f : Word BDL26Field (DoubleCylinderEdge P x S))
    (z : QStarEdge P q) (k : Fin S.half) :
    doubleCylinderCoboundary1 P x S f
        (Sum.inr (qToXSubdivisionBoundaryEdge P q x hxq S (z,k)))=
      (xFlow P S x f (rayImage P q S z 0 k)+xFlow P S x f (rayImage P q S z 1 k))+
        wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
          (verticalReadback P A S x q hxq f) (rayCut P q S 0 z k) := by
  rw [original_rectangle_coboundary,rayImage_value P A,rayImage_value P A,
    qLocalCoboundary_apply]
  change _=(_+_)+(f (Sum.inr (qBoundaryVertex P A q x hxq S
      (qSubdivisionEdgeStart P q S (z,k))))+
    f (Sum.inr (qBoundaryVertex P A q x hxq S (qSubdivisionEdgeEnd P q S (z,k)))))
  rw [qBoundaryVertex_start,qBoundaryVertex_end]
theorem rectangle_ray_sum (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (x : P.X)
    (q : P.Q) (hxq : P.xq x q=true)
    (f : Word BDL26Field (DoubleCylinderEdge P x S)) (z : QStarEdge P q) :
    (∑ k : Fin S.half,doubleCylinderCoboundary1 P x S f
      (Sum.inr (qToXSubdivisionBoundaryEdge P q x hxq S (z,k))))=
      rayFlowSum P S x f q z+
        (f (Sum.inr (qBoundaryVertex P A q x hxq S (.inl (.inl ()))))+
          f (Sum.inr (qBoundaryVertex P A q x hxq S (.inl (.inr z))))) := by
  calc
    _=((∑ k : Fin S.half,xFlow P S x f (rayImage P q S z 0 k))+
        (∑ k : Fin S.half,xFlow P S x f (rayImage P q S z 1 k)))+
      (∑ k : Fin S.half,wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
        (verticalReadback P A S x q hxq f) (rayCut P q S 0 z k)) := by
      simp_rw [rectangle_ray_step P A S x q hxq f]
      simp only [Finset.sum_add_distrib]
    _=_ := by
      rw [q_ray_coboundary_sum]
      simp only [rayFlowSum,Fin.sum_univ_two,verticalReadback]
theorem rectangle_ray_pair (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (x : P.X)
    (q : P.Q) (hxq : P.xq x q=true)
    (f : Word BDL26Field (DoubleCylinderEdge P x S)) (z t : QStarEdge P q)
    (hz : f (qToXDoubleCylinderEdge P A q x hxq S (Sum.inr z))=0)
    (ht : f (qToXDoubleCylinderEdge P A q x hxq S (Sum.inr t))=0) :
    (∑ k : Fin S.half,doubleCylinderCoboundary1 P x S f
      (Sum.inr (qToXSubdivisionBoundaryEdge P q x hxq S (z,k))))+
    (∑ k : Fin S.half,doubleCylinderCoboundary1 P x S f
      (Sum.inr (qToXSubdivisionBoundaryEdge P q x hxq S (t,k))))=
      rayFlowSum P S x f q z+rayFlowSum P S x f q t := by
  rw [rectangle_ray_sum P A S x q hxq f z,rectangle_ray_sum P A S x q hxq f t,
    qBoundaryVertex_terminal,qBoundaryVertex_terminal,hz,ht]
  simp only [add_zero]
  calc
    _=(rayFlowSum P S x f q z+rayFlowSum P S x f q t)+
      (f (Sum.inr (qBoundaryVertex P A q x hxq S (.inl (.inl ()))))+
       f (Sum.inr (qBoundaryVertex P A q x hxq S (.inl (.inl ()))))) := by abel
    _=_ := by rw [repair3_scalar_add_self,add_zero]
theorem rayImage_injective (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (z : Fin 3 → QStarEdge P q) (hz : Function.Injective z) :
    Function.Injective (fun p : Fin 3 × BDL26FiniteTannerSquare.Two × Fin S.half =>
      rayImage P q S (z p.1) p.2.1 p.2.2) := by
  rintro ⟨i,c,k⟩ ⟨j,d,l⟩ h
  have hq := Sum.inr.inj (Sum.inl.inj h)
  have he := sigma_same_index_inj (I:=P.Q)
    (A:=fun r => QDoubleCylinderEdge P r S) (i:=q)
    (rayCut P q S c (z i) k) (rayCut P q S d (z j) l) hq
  change (rayCut P q S c (z i) k)=(rayCut P q S d (z j) l) at he
  have hp := Sum.inl.inj he
  have hc : c=d := congrArg Prod.fst hp
  have hr := congrArg Prod.snd hp
  have hi : i=j := hz (congrArg Prod.fst hr)
  have hk : k=l := congrArg Prod.snd hr
  exact Prod.ext hi (Prod.ext hc hk)
theorem two_ray_parities_force_actual_cut
    {I : Type} [Fintype I] [DecidableEq I] (S : OddScale)
    (w : Word BDL26Field I) (hw : HammingWeight w ≤ 1)
    (e : Fin 3 × BDL26FiniteTannerSquare.Two × Fin S.half → I) (hinj : Function.Injective e)
    (h02 : (∑ c : BDL26FiniteTannerSquare.Two,∑ k : Fin S.half,w (e (0,c,k)))+
      (∑ c : BDL26FiniteTannerSquare.Two,∑ k : Fin S.half,w (e (2,c,k)))=1)
    (h12 : (∑ c : BDL26FiniteTannerSquare.Two,∑ k : Fin S.half,w (e (1,c,k)))+
      (∑ c : BDL26FiniteTannerSquare.Two,∑ k : Fin S.half,w (e (2,c,k)))=0) :
    ∃ c : BDL26FiniteTannerSquare.Two,∃ k : Fin S.half,w=canonicalBasisWord (F:=BDL26Field) (e (0,c,k)) := by
  rcases flow_weight_le_one_word w hw with hzero | ⟨a,ha⟩
  · simp only [hzero,Pi.zero_apply,Finset.sum_const_zero,zero_add] at h02
    exact False.elim (zero_ne_one h02)
  subst w
  have hex : ∃ i : Fin 3,∃ c : BDL26FiniteTannerSquare.Two,∃ k : Fin S.half,a=e (i,c,k) := by
    by_contra hn
    have hval (i : Fin 3) (c : BDL26FiniteTannerSquare.Two) (k : Fin S.half) :
        canonicalBasisWord (F:=BDL26Field) a (e (i,c,k))=0 := by
      have hne : e (i,c,k)≠a := by intro h;exact hn ⟨i,c,k,h.symm⟩
      simp [basis_value,hne]
    simp [hval] at h02
  obtain ⟨i,c,k,hi⟩ := hex
  subst a
  have hsum (j : Fin 3) :
      (∑ d : BDL26FiniteTannerSquare.Two,∑ l : Fin S.half,
        canonicalBasisWord (F:=BDL26Field) (e (i,c,k)) (e (j,d,l)))=
        if j=i then 1 else 0 := by
    have hinner (d : BDL26FiniteTannerSquare.Two) :
        (∑ l : Fin S.half,canonicalBasisWord (F:=BDL26Field) (e (i,c,k)) (e (j,d,l)))=
          if j=i ∧ d=c then 1 else 0 := by
      rw [Fintype.sum_eq_single k]
      · simp [basis_value,hinj.eq_iff,Prod.mk.injEq]
      · intro l hl
        simp [basis_value,hinj.eq_iff,Prod.mk.injEq,hl]
    rw [Fin.sum_univ_two,hinner,hinner]
    by_cases hji : j=i <;> fin_cases c <;> simp [hji]
  rw [hsum,hsum] at h02 h12
  fin_cases i
  · exact ⟨c,k,rfl⟩
  · simp at h02
  · simp at h12
theorem actual_Cx_hub_ray_exit
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X) (q : P.Q) (hxq : P.xq x q=true)
    (z : Fin 3 → QStarEdge P q) (hz : Function.Injective z)
    (leaf : Fin 3 → P.Q) (hleaf : ∀ i,leaf i≠q)
    (hxleaf : ∀ i,P.xq x (leaf i)=true)
    (lz : ∀ i,QStarEdge P (leaf i)) (hlz : ∀ i,(lz i).val=(z i).val)
    (f : Word BDL26Field (DoubleCylinderEdge P x S))
    (hw : HammingWeight (xFlow P S x f) ≤ 1)
    (h02 : (∑ k : Fin S.half,doubleCylinderCoboundary1 P x S f
        (Sum.inr (qToXSubdivisionBoundaryEdge P q x hxq S (z 0,k))))+
      (∑ k : Fin S.half,doubleCylinderCoboundary1 P x S f
        (Sum.inr (qToXSubdivisionBoundaryEdge P q x hxq S (z 2,k))))=1)
    (h12 : (∑ k : Fin S.half,doubleCylinderCoboundary1 P x S f
        (Sum.inr (qToXSubdivisionBoundaryEdge P q x hxq S (z 1,k))))+
      (∑ k : Fin S.half,doubleCylinderCoboundary1 P x S f
        (Sum.inr (qToXSubdivisionBoundaryEdge P q x hxq S (z 2,k))))=0) :
    ∃ c : BDL26FiniteTannerSquare.Two,∃ k : Fin S.half,
      xFlow P S x f=canonicalBasisWord (F:=BDL26Field) (rayImage P q S (z 0) c k) := by
  have hterm (i : Fin 3) : f (qToXDoubleCylinderEdge P A q x hxq S (Sum.inr (z i)))=0 :=
    shared_bridge_zero P A S x f hw q (leaf i) (Ne.symm (hleaf i))
      hxq (hxleaf i) (z i) (lz i)
      (shared_Z_bridge_image P A S x q (leaf i) hxq (hxleaf i)
        (z i) (lz i) (hlz i).symm)
  have hp02 := rectangle_ray_pair P A S x q hxq f (z 0) (z 2) (hterm 0) (hterm 2)
  have hp12 := rectangle_ray_pair P A S x q hxq f (z 1) (z 2) (hterm 1) (hterm 2)
  apply two_ray_parities_force_actual_cut S (xFlow P S x f) hw
    (fun p : Fin 3 × BDL26FiniteTannerSquare.Two × Fin S.half => rayImage P q S (z p.1) p.2.1 p.2.2)
    (rayImage_injective P q S z hz)
  · exact hp02.symm.trans h02
  · exact hp12.symm.trans h12
end
end OriginalOldXScaleExtension
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace OriginalOldXScaleExtension
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RXDecoderAdapter BDL26DecodingGraph
open scoped Classical BigOperators
noncomputable section
def horizontalStrip (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) : Word BDL26Field (SubdivisionEdge P x S)
  | .inl (e,k) => if e=xStarFaceXQEdge P x f 0 ∧ k.val=0 then 1 else 0
  | .inr (.inl (g,i,_)) => if g=f ∧ i.val=0 then 1 else 0
  | .inr (.inr _) => 0
def verticalStrip (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) : Word BDL26Field (SubdivisionEdge P x S)
  | .inl (e,k) => if e=xStarFaceXQEdge P x f 1 ∧ k.val=0 then 1 else 0
  | .inr (.inl _) => 0
  | .inr (.inr (g,_,j)) => if g=f ∧ j.val=0 then 1 else 0
def copiedStrip (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (copy : BDL26FiniteTannerSquare.Two) (w : Word BDL26Field (SubdivisionEdge P x S)) :
    Word BDL26Field (DoubleCylinderEdge P x S)
  | .inl (d,e) => if d=copy then w e else 0
  | .inr _ => 0
theorem actual_square_coboundary (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (w : Word BDL26Field (DoubleCylinderEdge P x S))
    (copy : BDL26FiniteTannerSquare.Two) (f : XStarFace P x) (i j : Fin S.half) :
    doubleCylinderCoboundary1 P x S w (Sum.inl (copy,f,i,j))=
      (w (Sum.inl (copy,subdivisionHorizontalEdge P x S f i (finCastGrid j)))+
       w (Sum.inl (copy,subdivisionVerticalEdge P x S f (finSuccGrid i) j)))+
      (w (Sum.inl (copy,subdivisionHorizontalEdge P x S f i (finSuccGrid j)))+
       w (Sum.inl (copy,subdivisionVerticalEdge P x S f (finCastGrid i) j))) := by
  rw [doubleCylinderCoboundary1,doubleCylinderBoundary2,
    wordLinearMapTranspose_toLin'_apply]
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [doubleCylinderFaceEdgeMatrix,mul_ite,mul_zero,Finset.sum_const_zero,add_zero]
  have hc :
      (∑ d : BDL26FiniteTannerSquare.Two,∑ e : SubdivisionEdge P x S,
        if d=copy then w (Sum.inl (d,e))*subdivisionFaceEdgeMatrix P x S e (f,i,j) else 0)=
      ∑ e : SubdivisionEdge P x S,
        w (Sum.inl (copy,e))*subdivisionFaceEdgeMatrix P x S e (f,i,j) := by
    rw [Fintype.sum_eq_single copy]
    · simp
    · intro d hd
      simp [hd]
  rw [hc]
  simp only [subdivisionFaceEdgeMatrix,mul_add,Finset.sum_add_distrib,
    mul_ite,mul_one,mul_zero]
  simp
  exact add_assoc _ _ _
theorem horizontalStrip_on_horizontal (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x)
    (hunique : ∀ (g : XStarFace P x) (c : BDL26FiniteTannerSquare.Two),
      xStarFaceXQEdge P x g c=xStarFaceXQEdge P x f 0 → g=f ∧ c=0)
    (g : XStarFace P x) (i : Fin S.half) (j : Fin (S.half+1)) :
    horizontalStrip P x S f (subdivisionHorizontalEdge P x S g i j)=
      if g=f ∧ i.val=0 ∧ j.val < S.half then 1 else 0 := by
  by_cases hj0 : j.val=0
  · have he : xStarFaceXQEdge P x g 0=xStarFaceXQEdge P x f 0 ↔ g=f :=
      ⟨fun h => (hunique g 0 h).1,by intro h;subst g;rfl⟩
    simp [subdivisionHorizontalEdge,hj0,horizontalStrip,he,S.half_pos]
  · by_cases hjm : j.val=S.half
    · simp [subdivisionHorizontalEdge,hj0,hjm,horizontalStrip,
        xStarFaceQZEdge,xStarFaceXQEdge,Nat.ne_of_gt S.half_pos]
    · have hj : j.val < S.half := by have := j.isLt;omega
      simp [subdivisionHorizontalEdge,hj0,hjm,horizontalStrip,hj]
theorem horizontalStrip_on_vertical (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x)
    (hunique : ∀ (g : XStarFace P x) (c : BDL26FiniteTannerSquare.Two),
      xStarFaceXQEdge P x g c=xStarFaceXQEdge P x f 0 → g=f ∧ c=0)
    (g : XStarFace P x) (i : Fin (S.half+1)) (j : Fin S.half) :
    horizontalStrip P x S f (subdivisionVerticalEdge P x S g i j)=0 := by
  by_cases hi0 : i.val=0
  · have he : xStarFaceXQEdge P x g 1≠xStarFaceXQEdge P x f 0 := by
      intro h
      exact (by decide : (1:BDL26FiniteTannerSquare.Two)≠0) (hunique g 1 h).2
    simp [subdivisionVerticalEdge,hi0,horizontalStrip,he]
  · by_cases him : i.val=S.half
    all_goals simp [subdivisionVerticalEdge,hi0,him,horizontalStrip,
      xStarFaceQZEdge,xStarFaceXQEdge,Nat.ne_of_gt S.half_pos]
theorem verticalStrip_on_vertical (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x)
    (hunique : ∀ (g : XStarFace P x) (c : BDL26FiniteTannerSquare.Two),
      xStarFaceXQEdge P x g c=xStarFaceXQEdge P x f 1 → g=f ∧ c=1)
    (g : XStarFace P x) (i : Fin (S.half+1)) (j : Fin S.half) :
    verticalStrip P x S f (subdivisionVerticalEdge P x S g i j)=
      if g=f ∧ j.val=0 ∧ i.val < S.half then 1 else 0 := by
  by_cases hi0 : i.val=0
  · have he : xStarFaceXQEdge P x g 1=xStarFaceXQEdge P x f 1 ↔ g=f :=
      ⟨fun h => (hunique g 1 h).1,by intro h;subst g;rfl⟩
    simp [subdivisionVerticalEdge,hi0,verticalStrip,he,S.half_pos]
  · by_cases him : i.val=S.half
    · simp [subdivisionVerticalEdge,hi0,him,verticalStrip,
        xStarFaceQZEdge,xStarFaceXQEdge,Nat.ne_of_gt S.half_pos]
    · have hi : i.val < S.half := by have := i.isLt;omega
      simp [subdivisionVerticalEdge,hi0,him,verticalStrip,hi]
theorem verticalStrip_on_horizontal (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x)
    (hunique : ∀ (g : XStarFace P x) (c : BDL26FiniteTannerSquare.Two),
      xStarFaceXQEdge P x g c=xStarFaceXQEdge P x f 1 → g=f ∧ c=1)
    (g : XStarFace P x) (i : Fin S.half) (j : Fin (S.half+1)) :
    verticalStrip P x S f (subdivisionHorizontalEdge P x S g i j)=0 := by
  by_cases hj0 : j.val=0
  · have he : xStarFaceXQEdge P x g 0≠xStarFaceXQEdge P x f 1 := by
      intro h
      exact (by decide : (0:BDL26FiniteTannerSquare.Two)≠1) (hunique g 0 h).2
    simp [subdivisionHorizontalEdge,hj0,verticalStrip,he]
  · by_cases hjm : j.val=S.half
    all_goals simp [subdivisionHorizontalEdge,hj0,hjm,verticalStrip,
      xStarFaceQZEdge,xStarFaceXQEdge,Nat.ne_of_gt S.half_pos]
def lastSegment (S : OddScale) : Fin S.half := ⟨S.half-1,by have := S.half_pos;omega⟩
def firstSegment (S : OddScale) : Fin S.half := ⟨0,S.half_pos⟩
theorem horizontalStrip_boundary_zero (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (e : SubdivisionBoundaryEdge P x S) :
    horizontalStrip P x S f e.val=0 := by
  rcases e with ⟨e,he⟩
  rcases e with ⟨a,k⟩ | e
  · have hne : a≠xStarFaceXQEdge P x f 0 := by
      intro h
      subst a
      change false=true at he
      cases he
    simp [horizontalStrip,hne]
  · simp [subdivisionBoundaryEdgeMember] at he
theorem verticalStrip_boundary_zero (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (e : SubdivisionBoundaryEdge P x S) :
    verticalStrip P x S f e.val=0 := by
  rcases e with ⟨e,he⟩
  rcases e with ⟨a,k⟩ | e
  · have hne : a≠xStarFaceXQEdge P x f 1 := by
      intro h
      subst a
      change false=true at he
      cases he
    simp [verticalStrip,hne]
  · simp [subdivisionBoundaryEdgeMember] at he
theorem copiedStrip_rectangle_zero (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (copy : BDL26FiniteTannerSquare.Two)
    (w : Word BDL26Field (SubdivisionEdge P x S))
    (hw : ∀ e : SubdivisionBoundaryEdge P x S,w e.val=0)
    (e : SubdivisionBoundaryEdge P x S) :
    doubleCylinderCoboundary1 P x S (copiedStrip P x S copy w) (Sum.inr e)=0 := by
  rw [original_rectangle_coboundary]
  simp [copiedStrip,hw]
theorem horizontalStrip_copied_square (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x)
    (hunique : ∀ (g : XStarFace P x) (c : BDL26FiniteTannerSquare.Two),
      xStarFaceXQEdge P x g c=xStarFaceXQEdge P x f 0 → g=f ∧ c=0)
    (copy d : BDL26FiniteTannerSquare.Two) (g : XStarFace P x) (i j : Fin S.half) :
    doubleCylinderCoboundary1 P x S (copiedStrip P x S copy (horizontalStrip P x S f))
      (Sum.inl (d,g,i,j))=
      canonicalBasisWord (F:=BDL26Field)
        (Sum.inl (copy,f,firstSegment S,lastSegment S) : DoubleCylinderFace P x S) (Sum.inl (d,g,i,j)) := by
  rw [actual_square_coboundary]
  by_cases hd : d=copy
  · subst d
    simp only [copiedStrip,if_true]
    rw [horizontalStrip_on_horizontal P x S f hunique,
      horizontalStrip_on_vertical P x S f hunique,
      horizontalStrip_on_horizontal P x S f hunique,
      horizontalStrip_on_vertical P x S f hunique]
    have hj : j.val < S.half := j.isLt
    have hji : j.val+1=S.half ↔ j=lastSegment S := by
      simp only [lastSegment,Fin.ext_iff]
      have := j.isLt
      have := S.half_pos
      omega
    have hii : i.val=0 ↔ i=firstSegment S := by simp [firstSegment,Fin.ext_iff]
    by_cases hg : g=f
    · subst g
      by_cases hi : i.val=0
      · by_cases hjlast : j.val+1=S.half
        · have he : j=lastSegment S := hji.mp hjlast
          have ie : i=firstSegment S := hii.mp hi
          subst j
          subst i
          have hl : S.half-1+1=S.half := Nat.sub_add_cancel (by have := S.half_pos;omega)
          simp [finCastGrid,finSuccGrid,firstSegment,lastSegment,basis_value,Prod.mk.injEq,
            S.half_pos,hl]
        · have hjnext : j.val+1 < S.half := by omega
          have hne : j≠lastSegment S := fun he => hjlast (hji.mpr he)
          simp [finCastGrid,finSuccGrid,hj,hjnext,hi,basis_value,Prod.mk.injEq,hne,
            CharTwo.add_self_eq_zero]
      · have hne : i≠firstSegment S := fun he => hi (hii.mpr he)
        simp [finCastGrid,finSuccGrid,hi,basis_value,Prod.mk.injEq,hne]
    · simp [hg,basis_value,Prod.mk.injEq]
  · simp [copiedStrip,hd,basis_value,Prod.mk.injEq]
theorem verticalStrip_copied_square (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x)
    (hunique : ∀ (g : XStarFace P x) (c : BDL26FiniteTannerSquare.Two),
      xStarFaceXQEdge P x g c=xStarFaceXQEdge P x f 1 → g=f ∧ c=1)
    (copy d : BDL26FiniteTannerSquare.Two) (g : XStarFace P x) (i j : Fin S.half) :
    doubleCylinderCoboundary1 P x S (copiedStrip P x S copy (verticalStrip P x S f))
      (Sum.inl (d,g,i,j))=
      canonicalBasisWord (F:=BDL26Field)
        (Sum.inl (copy,f,lastSegment S,firstSegment S) : DoubleCylinderFace P x S) (Sum.inl (d,g,i,j)) := by
  rw [actual_square_coboundary]
  by_cases hd : d=copy
  · subst d
    simp only [copiedStrip,if_true]
    rw [verticalStrip_on_horizontal P x S f hunique,
      verticalStrip_on_vertical P x S f hunique,
      verticalStrip_on_horizontal P x S f hunique,
      verticalStrip_on_vertical P x S f hunique]
    have hi : i.val < S.half := i.isLt
    have hii : i.val+1=S.half ↔ i=lastSegment S := by
      simp only [lastSegment,Fin.ext_iff]
      have := i.isLt
      have := S.half_pos
      omega
    have hji : j.val=0 ↔ j=firstSegment S := by simp [firstSegment,Fin.ext_iff]
    by_cases hg : g=f
    · subst g
      by_cases hj : j.val=0
      · by_cases hilast : i.val+1=S.half
        · have he : i=lastSegment S := hii.mp hilast
          have je : j=firstSegment S := hji.mp hj
          subst i
          subst j
          have hl : S.half-1+1=S.half := Nat.sub_add_cancel (by have := S.half_pos;omega)
          simp [finCastGrid,finSuccGrid,firstSegment,lastSegment,basis_value,Prod.mk.injEq,
            S.half_pos,hl]
        · have hinext : i.val+1 < S.half := by omega
          have hne : i≠lastSegment S := fun he => hilast (hii.mpr he)
          simp [finCastGrid,finSuccGrid,hi,hinext,hj,basis_value,Prod.mk.injEq,hne,
            CharTwo.add_self_eq_zero]
      · have hne : j≠firstSegment S := fun he => hj (hji.mpr he)
        simp [finCastGrid,finSuccGrid,hj,basis_value,Prod.mk.injEq,hne]
    · simp [hg,basis_value,Prod.mk.injEq]
  · simp [copiedStrip,hd,basis_value,Prod.mk.injEq]
theorem horizontalStrip_whole_boundary (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x)
    (hunique : ∀ (g : XStarFace P x) (c : BDL26FiniteTannerSquare.Two),
      xStarFaceXQEdge P x g c=xStarFaceXQEdge P x f 0 → g=f ∧ c=0) (copy : BDL26FiniteTannerSquare.Two) :
    doubleCylinderCoboundary1 P x S (copiedStrip P x S copy (horizontalStrip P x S f))=
      canonicalBasisWord (F:=BDL26Field)
        (Sum.inl (copy,f,firstSegment S,lastSegment S)) := by
  funext face
  rcases face with ⟨d,g,i,j⟩ | e
  · exact horizontalStrip_copied_square P x S f hunique copy d g i j
  · rw [copiedStrip_rectangle_zero P x S copy _ (horizontalStrip_boundary_zero P x S f)]
    simp [basis_value]
theorem verticalStrip_whole_boundary (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x)
    (hunique : ∀ (g : XStarFace P x) (c : BDL26FiniteTannerSquare.Two),
      xStarFaceXQEdge P x g c=xStarFaceXQEdge P x f 1 → g=f ∧ c=1) (copy : BDL26FiniteTannerSquare.Two) :
    doubleCylinderCoboundary1 P x S (copiedStrip P x S copy (verticalStrip P x S f))=
      canonicalBasisWord (F:=BDL26Field)
        (Sum.inl (copy,f,lastSegment S,firstSegment S)) := by
  funext face
  rcases face with ⟨d,g,i,j⟩ | e
  · exact verticalStrip_copied_square P x S f hunique copy d g i j
  · rw [copiedStrip_rectangle_zero P x S copy _ (verticalStrip_boundary_zero P x S f)]
    simp [basis_value]
def scaledSmallFace (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    SubdivisionFace (DirectOldXCounterexample.AP S) (DirectOldXCounterexample.AX S j outer) S :=
  if ActualCriticalStarGeometry.cr S j outer=0 then
    (DirectOldXCounterexample.actualStarFace S j outer,firstSegment S,lastSegment S)
  else (DirectOldXCounterexample.actualStarFace S j outer,lastSegment S,firstSegment S)
def scaledAlpha (S : OddScale) (j : Fin 2) (outer copy : BDL26FiniteTannerSquare.Two) :
    Word BDL26Field (DoubleCylinderEdge (DirectOldXCounterexample.AP S)
      (DirectOldXCounterexample.AX S j outer) S) :=
  if ActualCriticalStarGeometry.cr S j outer=0 then
    copiedStrip _ _ S copy (horizontalStrip _ _ S (DirectOldXCounterexample.actualStarFace S j outer))
  else copiedStrip _ _ S copy (verticalStrip _ _ S (DirectOldXCounterexample.actualStarFace S j outer))
end
end OriginalOldXScaleExtension
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint


