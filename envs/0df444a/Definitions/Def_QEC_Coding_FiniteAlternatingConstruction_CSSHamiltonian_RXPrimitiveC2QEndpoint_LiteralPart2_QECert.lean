-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_LiteralPart2_QECert
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_LiteralPart2_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T10:43:47.037288+00:00
-- url     : https://prove2.me/theorems/740a2214-8368-431e-a32a-ec82cac67046
-- title:
--   RX primitive C2Q endpoint: literal segment 2
-- statement:
--   Definitions and structural lemmas for RXPrimitive C2 QEndpoint, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean

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


set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RXDecoderAdapter BDL26LevelTwoCode BDL26IndexedDecoder
open MultiscaleDecoder.RXCoarseGraining
instance (priority := high) repair3WordHAdd {I : Type*} :
    HAdd (Word BDL26Field I) (Word BDL26Field I) (Word BDL26Field I) :=
  ⟨fun a b i => a i+b i⟩
instance (priority := high) repair6RegionWordHAdd {I : Type*} (Y : Finset I) :
    HAdd (Word BDL26Field (LocalRegionIndex Y))
      (Word BDL26Field (LocalRegionIndex Y))
      (Word BDL26Field (LocalRegionIndex Y)) :=
  ⟨@Add.add (LocalRegionIndex Y → BDL26Field) inferInstance⟩
theorem repair3_scalar_add_self (a : BDL26Field) : a+a=0 :=
  CharTwo.add_self_eq_zero a
theorem repair3_word_add_self {I : Type*} (w : Word BDL26Field I) : w+w=0 := by
  funext i
  exact repair3_scalar_add_self (w i)
universe u4 v4
section Repair4OriginalTotalCongruence
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
variable {depth4 : Nat} {C04 C14 C24 : LevelIndex depth4 → Type u4}
variable [∀ i,Fintype (C04 i)] [∀ i,Fintype (C14 i)] [∀ i,Fintype (C24 i)]
variable [∀ i,DecidableEq (C14 i)] [∀ i,DecidableEq (C24 i)]
variable {D4 : BDL26DecoderData depth4 C04 C14 C24} {i4 : StepIndex depth4}
variable {X4 Q4 Z4 : Type v4} [Fintype X4] [DecidableEq X4]
  [Fintype Q4] [DecidableEq Q4] [Fintype Z4] [DecidableEq Z4]
variable {LX4 : LocalComplexData X4 (C24 i4.succ) (C14 i4.succ)}
  {LQ4 : LocalComplexData Q4 (C24 i4.succ) (C14 i4.succ)}
  {LZ4 : LocalComplexData Z4 (C24 i4.succ) (C14 i4.succ)}
variable {X04 : X4 → Type u4} {Q04 : Q4 → Type u4}
  {Z04 Z14 Z24 : Z4 → Type u4}
variable [∀ x,Fintype (X04 x)] [∀ q,Fintype (Q04 q)]
  [∀ z,Fintype (Z04 z)] [∀ z,Fintype (Z14 z)] [∀ z,Fintype (Z24 z)]
variable (G4 : RXCoarseGrainingData (X0 := X04) (Q0 := Q04)
  (Z0 := Z04) (Z1 := Z14) (Z2 := Z24) D4 i4 LX4 LQ4 LZ4)
end Repair4OriginalTotalCongruence
theorem repair4_basis_weight_one {I : Type} [Fintype I] (p : I) :
    HammingWeight (canonicalBasisWord p : Word BDL26Field I)=1 := by
  classical
  have h : hammingSupport (canonicalBasisWord p : Word BDL26Field I)={p} := by
    ext i
    by_cases hi : i=p <;> simp [hammingSupport,basis_value,hi]
  rw [HammingWeight_eq_card_hammingSupport,h,Finset.card_singleton]
instance repair4BaseStateZeroX : OfNat BDL26DecodingGraph.baseState.presentation.X 0 :=
  inferInstanceAs (OfNat BDL26FiniteAlternatingCore.BaseX 0)
instance repair2BaseZeroX : OfNat baseTannerSquarePresentation.X 0 :=
  inferInstanceAs (OfNat BDL26FiniteAlternatingCore.BaseX 0)
abbrev literalAt (P : TannerSquarePresentation) (S : OddScale) :
    LevelIndex 1 → TannerSquarePresentation :=
  Fin.cases P (fun _ => rxReplacementPresentation P S)
abbrev literalX (P : TannerSquarePresentation) (S : OddScale)
    (i : LevelIndex 1) := (literalAt P S i).X
abbrev literalQ (P : TannerSquarePresentation) (S : OddScale)
    (i : LevelIndex 1) := (literalAt P S i).Q
abbrev literalZ (P : TannerSquarePresentation) (S : OddScale)
    (i : LevelIndex 1) := (literalAt P S i).Z
abbrev literalFamily (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    BDL26CochainFamily 1 (literalX P S) (literalQ P S) (literalZ P S) :=
  presentationFamily P A R S
instance (priority := high) repair6C3TopHAdd (S : OddScale) :
    HAdd ((indexedFamily S 3).Cochain2 (3 : LevelIndex 3))
      ((literalFamily (BDL26DecodingGraph.state S 2).presentation
        (BDL26DecodingGraph.state S 2).admissible
        (BDL26DecodingGraph.state S 2).regular S).Cochain2
          (Fin.succ (0 : StepIndex 1)))
      ((indexedFamily S 3).Cochain2 (3 : LevelIndex 3)) :=
  ⟨fun a b => @Add.add (FamilyZ S 3 (3 : LevelIndex 3) → BDL26Field)
    inferInstance a b⟩
instance (priority := high) repair6C3UpperHAdd (S : OddScale) :
    HAdd (BDL26RXErrorPullback.Upper S 3
        (BDL26LocalizedHistoryErrorDescent.Edge 1 (0 : StepIndex 1)))
      (Word BDL26Field (literalQ (BDL26DecodingGraph.state S 2).presentation S
        (Fin.succ (0 : StepIndex 1))))
      (BDL26RXErrorPullback.Upper S 3
        (BDL26LocalizedHistoryErrorDescent.Edge 1 (0 : StepIndex 1))) :=
  ⟨fun a b => @Add.add
    ((BDL26DecodingGraph.state S 3).presentation.Q → BDL26Field) inferInstance a b⟩
abbrev literalMap (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    BDL26CochainMap (literalFamily P A R S) (0 : StepIndex 1) :=
  presentationMap P A R S
abbrev literalDecoderData (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    BDL26DecoderData 1 (literalX P S) (literalQ P S) (literalZ P S) :=
  presentationDecoderData P A R S
instance (priority := high) repair6LiteralSyndromeHAdd
    (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) :
    HAdd (Word BDL26Field (literalZ P S 1))
      ((literalDecoderData P A R S).family.Cochain2 (Fin.succ (0 : StepIndex 1)))
      (Word BDL26Field (literalZ P S 1)) :=
  ⟨fun a b => @Add.add (literalZ P S 1 → BDL26Field) inferInstance a b⟩
instance (priority := high) repair7TopLiteralCochainHAdd (S : OddScale) :
    HAdd ((indexedFamily S (1+2)).Cochain2 (TopIndex (1+2)))
      ((literalFamily (BDL26DecodingGraph.state S 2).presentation
        (BDL26DecodingGraph.state S 2).admissible
        (BDL26DecodingGraph.state S 2).regular S).Cochain2
          (Fin.succ (0 : StepIndex 1)))
      ((indexedFamily S (1+2)).Cochain2 (TopIndex (1+2))) :=
  ⟨fun a b => @Add.add (FamilyZ S 3 (TopIndex 3) → BDL26Field)
    inferInstance a b⟩
instance (priority := high) repair7TopLiteralWordHAdd (S : OddScale) :
    HAdd ((indexedFamily S (1+2)).Cochain2 (TopIndex (1+2)))
      (Word BDL26Field (literalZ (BDL26DecodingGraph.state S 2).presentation S
        (Fin.succ (0 : StepIndex 1))))
      ((indexedFamily S (1+2)).Cochain2 (TopIndex (1+2))) :=
  ⟨fun a b => @Add.add (FamilyZ S 3 (TopIndex 3) → BDL26Field)
    inferInstance a b⟩
abbrev literalLx (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :=
  presentationLx P A R S
abbrev literalLq (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :=
  presentationLq P A R S
abbrev literalLz (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :=
  presentationLz P A R S
abbrev literalContract (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    RXConstructionContractSlice
      (X0 := fun x => DoubleCylinderVertex P x S)
      (Q0 := fun _ => Fin 0) (Z0 := fun _ => Fin 0)
      (Z1 := fun _ => Fin 0) (Z2 := fun _ => Fin 2)
      (literalDecoderData P A R S) (0 : StepIndex 1)
      (literalLx P A R S) (literalLq P A R S) (literalLz P A R S) :=
  presentationContract P A R S
abbrev literalData (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    RXCoarseGrainingData
      (X0 := fun x => DoubleCylinderVertex P x S)
      (Q0 := fun _ => Fin 0) (Z0 := fun _ => Fin 0)
      (Z1 := fun _ => Fin 0) (Z2 := fun _ => Fin 2)
      (literalDecoderData P A R S) (0 : StepIndex 1)
      (literalLx P A R S) (literalLq P A R S) (literalLz P A R S) :=
  presentationData P A R S
theorem repair5_C3_upper_coboundary1 (S : OddScale) :
    (BDL26IndexedDecoder.indexedFamily S 3).coboundary1 (3 : LevelIndex 3)=
      (literalFamily (BDL26DecodingGraph.state S 2).presentation
        (BDL26DecodingGraph.state S 2).admissible
        (BDL26DecodingGraph.state S 2).regular S).coboundary1
          (Fin.succ (0 : StepIndex 1)) := by
  exact (BDL26IndexedDecoder.indexedFamily_coboundary1 S 3 (3 : LevelIndex 3)).trans
    (presentationFamily_coboundary1 (BDL26DecodingGraph.state S 2).presentation
      (BDL26DecodingGraph.state S 2).admissible
      (BDL26DecodingGraph.state S 2).regular S
      (Fin.succ (0 : StepIndex 1))).symm
abbrev repair2C3Input (S : OddScale) :=
  BDL26HistorySyndromeSensitivity.TopInput S 1
abbrev repair5_literal_to_actual (S : OddScale)
    (sigma : (literalFamily (BDL26DecodingGraph.state S 2).presentation
      (BDL26DecodingGraph.state S 2).admissible
      (BDL26DecodingGraph.state S 2).regular S).Syndrome
        (Fin.succ (0 : StepIndex 1))) : repair2C3Input S := by
  refine ⟨sigma.val,?_⟩
  obtain ⟨w,hw⟩ := sigma.property
  refine ⟨w,?_⟩
  exact (LinearMap.congr_fun (repair5_C3_upper_coboundary1 S) w).trans hw
abbrev repair5_actual_to_literal (S : OddScale) (sigma : repair2C3Input S) :
    (literalFamily (BDL26DecodingGraph.state S 2).presentation
      (BDL26DecodingGraph.state S 2).admissible
      (BDL26DecodingGraph.state S 2).regular S).Syndrome
        (Fin.succ (0 : StepIndex 1)) := by
  refine ⟨sigma.val,?_⟩
  obtain ⟨w,hw⟩ := sigma.property
  refine ⟨w,?_⟩
  exact (LinearMap.congr_fun (repair5_C3_upper_coboundary1 S) w).symm.trans hw
abbrev repair2C3InputOfSyndrome (S : OddScale)
    (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S 1) : repair2C3Input S :=
  BDL26ActualFailureReadout.input S 1 u
abbrev repair2C3PerturbTop (S : OddScale) (sigma : repair2C3Input S)
    (e : Word BDL26Field (literalQ (BDL26DecodingGraph.state S 2).presentation S
      (Fin.succ (0 : StepIndex 1)))) : repair2C3Input S :=
  BDL26HistorySyndromeSensitivity.perturbTop S 1 sigma e
abbrev repair2C3Flip (S : OddScale) (p : BDL26CSSHamiltonian.Physical S 3) :
    Word BDL26Field (literalQ (BDL26DecodingGraph.state S 2).presentation S
      (Fin.succ (0 : StepIndex 1))) :=
  BDL26ActualFailureReadout.flip S 1 p
abbrev repair2C3Correction (S : OddScale) (sigma : repair2C3Input S) :
    Word BDL26Field (literalQ (BDL26DecodingGraph.state S 2).presentation S
      (Fin.succ (0 : StepIndex 1))) :=
  (BDL26HistoryErrorTelescoping.actualOutput S 1 sigma
    (0 : StepIndex 1)).correction
abbrev repair2C3Map2 (S : OddScale) :
    Word BDL26Field (BDL26DecodingGraph.state S 2).presentation.Z →ₗ[BDL26Field]
      Word BDL26Field (literalZ (BDL26DecodingGraph.state S 2).presentation S
        (Fin.succ (0 : StepIndex 1))) :=
  ((indexedDecoderData S 3).selectedMap (2 : StepIndex 3)).map2
theorem repair2_interior_succ_lt (S : OddScale) (i : Fin (S.half-1)) :
    i.val+1<S.half := by
  have hi := i.isLt
  have hm : S.half-1+1=S.half := Nat.sub_add_cancel S.half_pos
  omega
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalOldXQueries
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open BDL26ActualFailureReadout
open scoped Classical BigOperators
section
variable (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
  (R : TannerSquareCellularRegular P) (S : OddScale)
local notation "CF" => BDL26DecoderData.family (literalDecoderData P A R S)
local notation "G" => literalData P A R S
local notation "LX" => (literalLx P A R S :
  @LocalComplexData (TannerSquarePresentation.X P)
    (TannerSquareData.xFintype (TannerSquarePresentation.data P))
    (TannerSquareData.xDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "LQ" => (literalLq P A R S :
  @LocalComplexData (TannerSquarePresentation.Q P)
    (TannerSquareData.qFintype (TannerSquarePresentation.data P))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "U" => (Fin.succ (0 : StepIndex 1))
abbrev LocalQWord (q : P.Q) :=
  Word BDL26Field (LocalRegionIndex ((LQ).correctionRegion q))
def assemble (W : ∀ q, LocalQWord P A R S q) : (CF).Cochain1 U :=
  ∑ q, extendWordLinear ((LQ).correctionRegion q) (W q)
def addError (sigma : (CF).Syndrome U) (e : (CF).Cochain1 U) : (CF).Syndrome U := by
  refine ⟨sigma.val+(CF).coboundary1 U e,?_⟩
  obtain ⟨a,ha⟩ := sigma.property
  exact ⟨a+e,by erw [map_add,ha]⟩
def queryShift (sigma : (CF).Syndrome U)
    (W : ∀ q,LocalQWord P A R S q) : (CF).Cochain1 U :=
  assemble P A R S W+cqCorrectionTotal G sigma.val
def actualTranslation (sigma : (CF).Syndrome U) (e : (CF).Cochain1 U) (q : P.Q) :
    LocalQWord P A R S q :=
  restrictWordLinear ((LQ).correctionRegion q) (cqCorrectionTotal G sigma.val)+
    restrictWordLinear ((LQ).correctionRegion q)
      (cqCorrectionTotal G (addError P A R S sigma e).val)
end
end CriticalOldXQueries
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalOldXQueries
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open BDL26IndexedDecoder BDL26DecodingGraph BDL26ActualFailureReadout
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RXPhysicalCoordinateTrace
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
end CriticalOldXQueries
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalOldXQueries
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open BDL26IndexedDecoder BDL26DecodingGraph BDL26ActualFailureReadout
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RXPhysicalCoordinateTrace
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
section
variable (S : OddScale)
local notation "P" => ConstructionState.presentation (BDL26DecodingGraph.state S 2)
local notation "A" => ConstructionState.admissible (BDL26DecodingGraph.state S 2)
local notation "R" => ConstructionState.regular (BDL26DecodingGraph.state S 2)
local notation "CF" => BDL26DecoderData.family (literalDecoderData P A R S)
local notation "G" => literalData P A R S
local notation "LQ" => (literalLq P A R S :
  @LocalComplexData (TannerSquarePresentation.Q P)
    (TannerSquareData.qFintype (TannerSquarePresentation.data P))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "LX" => (literalLx P A R S :
  @LocalComplexData (TannerSquarePresentation.X P)
    (TannerSquareData.xFintype (TannerSquarePresentation.data P))
    (TannerSquareData.xDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "U" => (Fin.succ (0 : StepIndex 1))
end
end CriticalOldXQueries
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26LevelTwoCode BDL26RXLocalReplacement BDL26TannerLocalRegularity
open scoped Classical BigOperators
def criticalQZ (j : Fin 2) : XStarEdge baseTannerSquarePresentation (0 : BDL26FiniteAlternatingCore.BaseX) :=
  xStarFaceQZEdge baseTannerSquarePresentation 0 (seedFace j) 0
def criticalRadial (S : OddScale) (j : Fin 2) : (BDL26ActualFailureReadout.RawOne S).Q :=
  gammaRadial S j ⟨S.half-1,by have := S.half_pos;omega⟩
def criticalBoundary (S : OddScale) (j : Fin 2) : (BDL26ActualFailureReadout.RawOne S).Q :=
  .inl ⟨(0 : BDL26FiniteAlternatingCore.BaseX),.inl (0,.inl (criticalQZ j,⟨0,S.half_pos⟩))⟩
def criticalVertical (S : OddScale) (j : Fin 2) : (BDL26ActualFailureReadout.RawOne S).Q :=
  .inl ⟨(0 : BDL26FiniteAlternatingCore.BaseX),
    .inr ⟨.inl (seedQVertex j),by change xStarBoundaryVertexMember baseTannerSquarePresentation 0 (seedQVertex j).val=true; fin_cases j <;> decide⟩⟩
theorem critical_grid_not_Q_of_interior (S : OddScale) (j : Fin 2)
    (f : XStarFace baseTannerSquarePresentation (0 : BDL26FiniteAlternatingCore.BaseX))
    (a b : Fin (S.half+1))
    (hi : (0<a.val ∧ a.val<S.half) ∨ (0<b.val ∧ b.val<S.half)) :
    subdivisionGridVertex baseTannerSquarePresentation 0 S f a b≠.inl (seedQVertex j) := by
  intro h
  rcases hi with ⟨ha0,ham⟩ | ⟨hb0,hbm⟩
  · have ha0' : a.val≠0 := by omega
    have ham' : a.val≠S.half := by omega
    simp only [subdivisionGridVertex,dif_neg ha0',dif_neg ham'] at h
    split_ifs at h <;> cases h
  · have hb0' : b.val≠0 := by omega
    have hbm' : b.val≠S.half := by omega
    simp only [subdivisionGridVertex] at h
    split_ifs at h <;> first | omega | cases h
theorem critical_subdivision_incident (S : OddScale) (j : Fin 2)
    (e : SubdivisionEdge baseTannerSquarePresentation (0 : BDL26FiniteAlternatingCore.BaseX) S)
    (h : subdivisionEdgeStart baseTannerSquarePresentation 0 S e=.inl (seedQVertex j) ∨
      subdivisionEdgeEnd baseTannerSquarePresentation 0 S e=.inl (seedQVertex j)) :
    e=.inl (seedRadial j,⟨S.half-1,by have := S.half_pos;omega⟩) ∨
      e=.inl (criticalQZ j,⟨0,S.half_pos⟩) := by
  rcases e with ⟨edge,k⟩ | (⟨f,k,i⟩ | ⟨f,i,k⟩)
  · rcases h with hs | ht
    · change subdivisionSegmentStart _ _ S edge k=.inl (seedQVertex j) at hs
      by_cases hk : k.val=0
      · simp only [subdivisionSegmentStart,dif_pos hk] at hs
        have he : edge=criticalQZ j := by
          rcases edge with ⟨edge,member⟩
          rcases edge with ⟨⟨x,q⟩,hxq⟩ | ⟨⟨q,z⟩,hqz⟩
          · have hv := congrArg Subtype.val (Sum.inl.inj hs)
            cases hv
          · have hq : q=seedQ j := by
              have hv := congrArg Subtype.val (Sum.inl.inj hs)
              exact Vertex.q.inj hv
            subst q
            fin_cases j <;> fin_cases z
            all_goals
              simp [TannerSquarePresentation.qz,baseTannerSquarePresentation,
                baseTannerSquareData,baseBoundary2Matrix] at hqz
            all_goals first | contradiction | rfl
        right
        exact congrArg Sum.inl (Prod.ext he (Fin.ext hk))
      · simp only [subdivisionSegmentStart,dif_neg hk] at hs
        cases hs
    · change subdivisionSegmentEnd _ _ S edge k=.inl (seedQVertex j) at ht
      by_cases hk : k.val+1=S.half
      · simp only [subdivisionSegmentEnd,dif_pos hk] at ht
        have he : edge=seedRadial j := by
          rcases edge with ⟨edge,member⟩
          rcases edge with ⟨⟨x,q⟩,hxq⟩ | ⟨⟨q,z⟩,hqz⟩
          · have hq : q=seedQ j := by
              have hv := congrArg Subtype.val (Sum.inl.inj ht)
              exact Vertex.q.inj hv
            subst q
            fin_cases j <;> fin_cases x
            all_goals
              simp [TannerSquarePresentation.xq,baseTannerSquarePresentation,
                baseTannerSquareData,baseBoundary1Matrix] at hxq
            all_goals first | contradiction | rfl
          · have hv := congrArg Subtype.val (Sum.inl.inj ht)
            cases hv
        left
        have hk' : k=⟨S.half-1,by have := S.half_pos;omega⟩ := by
          apply Fin.ext
          change k.val=S.half-1
          have := S.half_pos
          omega
        exact congrArg Sum.inl (Prod.ext he hk')
      · simp only [subdivisionSegmentEnd,dif_neg hk] at ht
        cases ht
  · rcases h with hs | ht
    · apply False.elim
      apply (critical_grid_not_Q_of_interior S j f
        ⟨k.val,Nat.lt_succ_of_lt k.isLt⟩ ⟨i.val+1,by have hi := repair2_interior_succ_lt S i; omega⟩
        (Or.inr ⟨by change ((0 : Nat) < i.val + 1);omega,by change (i.val + 1 < S.half);exact repair2_interior_succ_lt S i⟩))
      exact hs
    · apply False.elim
      apply (critical_grid_not_Q_of_interior S j f
        ⟨k.val+1,by have := k.isLt;omega⟩ ⟨i.val+1,by have hi := repair2_interior_succ_lt S i; omega⟩
        (Or.inr ⟨by change ((0 : Nat) < i.val + 1);omega,by change (i.val + 1 < S.half);exact repair2_interior_succ_lt S i⟩))
      exact ht
  · rcases h with hs | ht
    · apply False.elim
      apply (critical_grid_not_Q_of_interior S j f
        ⟨i.val+1,by have hi := repair2_interior_succ_lt S i; omega⟩ ⟨k.val,Nat.lt_succ_of_lt k.isLt⟩
        (Or.inl ⟨by change ((0 : Nat) < i.val + 1);omega,by change (i.val + 1 < S.half);exact repair2_interior_succ_lt S i⟩))
      exact hs
    · apply False.elim
      apply (critical_grid_not_Q_of_interior S j f
        ⟨i.val+1,by have hi := repair2_interior_succ_lt S i; omega⟩ ⟨k.val+1,by have := k.isLt;omega⟩
        (Or.inl ⟨by change ((0 : Nat) < i.val + 1);omega,by change (i.val + 1 < S.half);exact repair2_interior_succ_lt S i⟩))
      exact ht
theorem critical_four_neighbours (S : OddScale) (j : Fin 2)
    (r : (BDL26ActualFailureReadout.RawOne S).Q) (hr : (BDL26ActualFailureReadout.RawOne S).xq (seedQNode S j) r=true) :
    r=criticalRadial S j ∨ r=criticalBoundary S j ∨
      r=criticalVertical S j ∨ r=gammaCone S j := by
  change RX1 baseTannerSquarePresentation S at r
  rcases r with ⟨x,e⟩ | ⟨q,v⟩
  · have howner : x=0 := by
      rcases (old_local_incidence S _ x e).mp hr with hs | ht
      · change (x : BDL26FiniteAlternatingCore.BaseX)=0
        exact (congrArg (fun v : (BDL26ActualFailureReadout.RawOne S).X =>
          (v.1 : BDL26FiniteAlternatingCore.BaseX)) hs).symm
      · change (x : BDL26FiniteAlternatingCore.BaseX)=0
        exact (congrArg (fun v : (BDL26ActualFailureReadout.RawOne S).X =>
          (v.1 : BDL26FiniteAlternatingCore.BaseX)) ht).symm
    subst x
    rcases (old_local_incidence S _ 0 e).mp hr with hs | ht
    · have hv := eq_of_heq (Sigma.mk.inj hs).2
      rcases e with ⟨copy,edge⟩ | vertex
      · have hc : copy=0 := (congrArg Prod.fst hv).symm
        subst copy
        have h : subdivisionEdgeStart baseTannerSquarePresentation 0 S edge=
            .inl (seedQVertex j) ∨
            subdivisionEdgeEnd baseTannerSquarePresentation 0 S edge=
              .inl (seedQVertex j) := Or.inl (congrArg Prod.snd hv).symm
        rcases critical_subdivision_incident S j edge h with he | he
        · exact Or.inl (by erw [he];rfl)
        · exact Or.inr (Or.inl (by erw [he];rfl))
      · have hvertex : vertex=⟨.inl (seedQVertex j),by change xStarBoundaryVertexMember baseTannerSquarePresentation 0 (seedQVertex j).val=true; fin_cases j <;> decide⟩ := by
          apply Subtype.ext
          exact (congrArg Prod.snd hv).symm
        rw [hvertex]
        exact Or.inr (Or.inr (Or.inl rfl))
    · have hv := eq_of_heq (Sigma.mk.inj ht).2
      rcases e with ⟨copy,edge⟩ | vertex
      · have hc : copy=0 := (congrArg Prod.fst hv).symm
        subst copy
        have h : subdivisionEdgeStart baseTannerSquarePresentation 0 S edge=
            .inl (seedQVertex j) ∨
            subdivisionEdgeEnd baseTannerSquarePresentation 0 S edge=
              .inl (seedQVertex j) := Or.inr (congrArg Prod.snd hv).symm
        rcases critical_subdivision_incident S j edge h with he | he
        · exact Or.inl (by erw [he];rfl)
        · exact Or.inr (Or.inl (by erw [he];rfl))
      · have hc := congrArg Prod.fst hv
        change (0 : BDL26FiniteTannerSquare.Two)=1 at hc
        exact False.elim (by cases hc)
  · exact Or.inr (Or.inr (Or.inr (seedQNode_shifted_neighbour S j q v hr)))
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalOldXQueries
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open BDL26DecodingGraph BDL26IndexedDecoder
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
def criticalTerminal (S : OddScale) (j : Fin 2)
    (copy : BDL26FiniteTannerSquare.Two) (r : (BDL26ActualFailureReadout.RawOne S).Q)
    (hr : (BDL26ActualFailureReadout.RawOne S).xq (seedQNode S j) r=true) : (BDL26DecodingGraph.state S 2).presentation.Q :=
  .inr ⟨r,(copy,.inl (.inr ⟨seedQNode S j,hr⟩))⟩
end CriticalOldXQueries
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RZLocalReplacement
open BDL26TannerLocalRegularity BDL26DecodingGraph BDL26LevelTwoCode
open scoped Classical BigOperators
noncomputable def shiftedQZNeighbourEquiv (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q)
    (v : QDoubleCylinderVertex (transposePresentation P) q S) :
    QStarEdge P q ≃ {z : RZZ P S // rzQZIncidence P A S (.inr ⟨q,v⟩) z=true} where
  toFun z := ⟨⟨z.val,qToZDoubleCylinderVertex P A q z.val z.property S v⟩,by
    change decide (∃ h : P.qz q z.val=true,
      qToZDoubleCylinderVertex P A q z.val h S v=
        qToZDoubleCylinderVertex P A q z.val z.property S v)=true
    exact decide_eq_true ⟨z.property,rfl⟩⟩
  invFun z := ⟨z.val.1,by
    have hz := z.property
    change decide (∃ h : P.qz q z.val.1=true,
      qToZDoubleCylinderVertex P A q z.val.1 h S v=z.val.2)=true at hz
    exact Classical.choose (of_decide_eq_true hz)⟩
  left_inv z := Subtype.ext rfl
  right_inv z := by
    rcases z with ⟨⟨z,t⟩,hz⟩
    change decide (∃ h : P.qz q z=true,
      qToZDoubleCylinderVertex P A q z h S v=t)=true at hz
    apply Subtype.ext
    exact Sigma.ext rfl (heq_of_eq (Classical.choose_spec (of_decide_eq_true hz)))
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RZLocalReplacement
open BDL26TannerLocalRegularity BDL26DecodingGraph BDL26LevelTwoCode
open scoped Classical BigOperators
theorem criticalRadial_incident (S : OddScale) (j : Fin 2) :
    (BDL26ActualFailureReadout.RawOne S).xq (seedQNode S j) (criticalRadial S j)=true := by
  let e : DoubleCylinderEdge baseTannerSquarePresentation (0 : BDL26FiniteAlternatingCore.BaseX) S :=
    .inl (0,.inl (seedRadial j,⟨S.half-1,by have := S.half_pos;omega⟩))
  apply (old_local_incidence S (seedQNode S j) 0 e).mpr
  right
  change seedQNode S j=⟨0,(0,subdivisionSegmentEnd baseTannerSquarePresentation 0 S
    (seedRadial j) ⟨S.half-1,by have := S.half_pos;omega⟩)⟩
  have hk : S.half-1+1=S.half := by have := S.half_pos;omega
  erw [subdivisionSegmentEnd,dif_pos hk,seedRadial_end]
  rfl
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXLocalReplacement
open BDL26TannerLocalRegularity BDL26DecodingGraph BDL26LevelTwoCode
open scoped Classical BigOperators
def criticalBoundaryPath (S : OddScale) (j : Fin 2) :
    SubdivisionBoundaryEdge baseTannerSquarePresentation (0 : BDL26FiniteAlternatingCore.BaseX) S :=
  ⟨.inl (criticalQZ j,⟨0,S.half_pos⟩),by change xStarBoundaryEdgeMember baseTannerSquarePresentation 0 (criticalQZ j).val=true; fin_cases j <;> decide⟩
def criticalVerticalVertex (S : OddScale) (j : Fin 2) :
    SubdivisionBoundaryVertex baseTannerSquarePresentation (0 : BDL26FiniteAlternatingCore.BaseX) S :=
  ⟨.inl (seedQVertex j),by change xStarBoundaryVertexMember baseTannerSquarePresentation 0 (seedQVertex j).val=true; fin_cases j <;> decide⟩
theorem criticalBoundaryPath_start (S : OddScale) (j : Fin 2) :
    subdivisionBoundaryEdgeStart baseTannerSquarePresentation 0 S
      (criticalBoundaryPath S j)=criticalVerticalVertex S j := by
  apply Subtype.ext
  change subdivisionSegmentStart baseTannerSquarePresentation 0 S
    (criticalQZ j) ⟨0,S.half_pos⟩=.inl (seedQVertex j)
  erw [subdivisionSegmentStart,dif_pos rfl]
  fin_cases j <;> rfl
theorem criticalVertical_rectangle_unique (S : OddScale) (j : Fin 2)
    (b : SubdivisionBoundaryEdge baseTannerSquarePresentation (0 : BDL26FiniteAlternatingCore.BaseX) S)
    (hb : criticalVerticalVertex S j=subdivisionBoundaryEdgeStart _ _ S b ∨
      criticalVerticalVertex S j=subdivisionBoundaryEdgeEnd _ _ S b) :
    b=criticalBoundaryPath S j := by
  have hv : subdivisionEdgeStart baseTannerSquarePresentation 0 S b.val=
      .inl (seedQVertex j) ∨
      subdivisionEdgeEnd baseTannerSquarePresentation 0 S b.val=.inl (seedQVertex j) := by
    rcases hb with hs | ht
    · left
      have hs' := congrArg Subtype.val hs
      have h := hs'.symm
      change (subdivisionBoundaryEdgeStart baseTannerSquarePresentation 0 S b).val=
        (criticalVerticalVertex S j).val at h
      exact (subdivisionBoundaryEdgeStart_value
        baseTannerSquarePresentation (0 : BDL26FiniteAlternatingCore.BaseX) S b).symm.trans h
    · right
      have ht' := congrArg Subtype.val ht
      have h := ht'.symm
      change (subdivisionBoundaryEdgeEnd baseTannerSquarePresentation 0 S b).val=
        (criticalVerticalVertex S j).val at h
      exact (subdivisionBoundaryEdgeEnd_value
        baseTannerSquarePresentation (0 : BDL26FiniteAlternatingCore.BaseX) S b).symm.trans h
  rcases critical_subdivision_incident S j b.val hv with hR | hB
  · have hm := b.property
    erw [hR] at hm
    change false=true at hm
    cases hm
  · exact Subtype.ext hB
theorem repair14_vertical_rectangle_zero (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (v : SubdivisionBoundaryVertex P x S)
    (b : SubdivisionBoundaryEdge P x S)
    (hs : v≠subdivisionBoundaryEdgeStart P x S b)
    (ht : v≠subdivisionBoundaryEdgeEnd P x S b) :
    doubleCylinderFaceEdgeMatrix P x S (Sum.inr v) (Sum.inr b)=0 := by
  classical
  change ((if v=subdivisionBoundaryEdgeStart P x S b then (1 : BDL26Field) else 0)+
    (if v=subdivisionBoundaryEdgeEnd P x S b then 1 else 0))=0
  rw [if_neg hs,if_neg ht,zero_add]
theorem criticalVertical_localMatrix (S : OddScale) (j : Fin 2)
    (f : DoubleCylinderFace baseTannerSquarePresentation (0 : BDL26FiniteAlternatingCore.BaseX) S) :
    doubleCylinderFaceEdgeMatrix baseTannerSquarePresentation 0 S
      (.inr (criticalVerticalVertex S j)) f=
        if f=.inr (criticalBoundaryPath S j) then 1 else 0 := by
  classical
  rcases f with ⟨copy,f⟩ | b
  · simp [doubleCylinderFaceEdgeMatrix]
  · by_cases hb : b=criticalBoundaryPath S j
    · subst b
      have hm : doubleCylinderFaceEdgeMatrix baseTannerSquarePresentation 0 S
          (.inr (criticalVerticalVertex S j)) (.inr (criticalBoundaryPath S j))=1 := by
        rw [← criticalBoundaryPath_start S j]
        exact doubleCylinder_rectangle_vertical_start baseTannerSquarePresentation 0 S
          (criticalBoundaryPath S j) (subdivisionBoundaryEdgeStart_ne_end _ _ _ _)
      exact hm.trans (if_pos rfl).symm
    · have hs : criticalVerticalVertex S j≠subdivisionBoundaryEdgeStart _ _ S b :=
        fun h => hb (criticalVertical_rectangle_unique S j b (Or.inl h))
      have ht : criticalVerticalVertex S j≠subdivisionBoundaryEdgeEnd _ _ S b :=
        fun h => hb (criticalVertical_rectangle_unique S j b (Or.inr h))
      have hf : (Sum.inr b : DoubleCylinderFace baseTannerSquarePresentation 0 S)≠
          Sum.inr (criticalBoundaryPath S j) := fun h => hb (Sum.inr.inj h)
      exact (repair14_vertical_rectangle_zero baseTannerSquarePresentation 0 S
        (criticalVerticalVertex S j) b hs ht).trans (if_neg hf).symm
theorem criticalVertical_qEdge_zero (S : OddScale) (j : Fin 2)
    (q : BDL26FiniteAlternatingCore.BaseQubit) (e : QDoubleCylinderEdge baseTannerSquarePresentation q S) :
    qDoubleCylinderEdgeXIncidence baseTannerSquarePresentation q 0 S
      (.inr (criticalVerticalVertex S j)) e=0 := by
  unfold qDoubleCylinderEdgeXIncidence
  by_cases hxq : baseTannerSquarePresentation.xq (0 : BDL26FiniteAlternatingCore.BaseX) q=true
  · erw [dif_pos hxq]
    have hn : (.inr (criticalVerticalVertex S j) : DoubleCylinderEdge
        baseTannerSquarePresentation (0 : BDL26FiniteAlternatingCore.BaseX) S)≠
        qToXDoubleCylinderEdgeRaw baseTannerSquarePresentation q 0 hxq S e := by
      rcases e with ⟨copy,z,k⟩ | z
      · intro he
        cases he
      · intro he
        have hv := congrArg Subtype.val (Sum.inr.inj he)
        change (Sum.inl (seedQVertex j) : SubdivisionVertex baseTannerSquarePresentation 0 S)=
          Sum.inl ⟨Vertex.z z.val,_⟩ at hv
        have ht := congrArg Subtype.val (Sum.inl.inj hv)
        cases ht
    erw [if_neg hn]
  · erw [dif_neg hxq]
def criticalVerticalCheck (S : OddScale) (j : Fin 2) : (BDL26ActualFailureReadout.RawOne S).Z :=
  .inl (.inl ⟨(0 : BDL26FiniteAlternatingCore.BaseX),.inr (criticalBoundaryPath S j)⟩)
theorem criticalVertical_matrix (S : OddScale) (j : Fin 2)
    (z : (BDL26ActualFailureReadout.RawOne S).Z) :
    rxBoundary2Matrix baseTannerSquarePresentation S (criticalVertical S j) z=
      if z=criticalVerticalCheck S j then 1 else 0 := by
  have h := rx_local_column_indicator baseTannerSquarePresentation S
    (0 : BDL26FiniteAlternatingCore.BaseX) (.inr (criticalVerticalVertex S j))
    (.inr (criticalBoundaryPath S j)) (criticalVertical_localMatrix S j)
    (criticalVertical_qEdge_zero S j) z
  convert h using 1 <;> congr 1
theorem criticalVertical_degree_one (S : OddScale) (j : Fin 2) :
    (BDL26ActualFailureReadout.RawOne S).qz (criticalVertical S j) (criticalVerticalCheck S j)=true ∧
      ∀ z : (BDL26ActualFailureReadout.RawOne S).Z,(BDL26ActualFailureReadout.RawOne S).qz (criticalVertical S j) z=true →
        z=criticalVerticalCheck S j := by
  constructor
  · have ht := raw_boundary2_view S (criticalVertical S j) (criticalVerticalCheck S j)
    erw [criticalVertical_matrix,if_pos rfl] at ht
    by_contra hn
    erw [if_neg hn] at ht
    exact one_ne_zero ht
  · intro z hz
    have ht := raw_boundary2_view S (criticalVertical S j) z
    erw [criticalVertical_matrix,if_pos hz] at ht
    by_contra hn
    erw [if_neg hn] at ht
    exact one_ne_zero ht.symm
theorem criticalVertical_incident (S : OddScale) (j : Fin 2) :
    (BDL26ActualFailureReadout.RawOne S).xq (seedQNode S j) (criticalVertical S j)=true := by
  apply (old_local_incidence S (seedQNode S j) 0
    (.inr (criticalVerticalVertex S j))).mpr
  left
  rfl
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXLocalReplacement
open BDL26TannerLocalRegularity BDL26DecodingGraph BDL26LevelTwoCode
open BDL26ActualFailureReadout
open scoped Classical BigOperators
theorem criticalBoundary_incident (S : OddScale) (j : Fin 2) :
    (BDL26ActualFailureReadout.RawOne S).xq (seedQNode S j) (criticalBoundary S j)=true := by
  apply (old_local_incidence S (seedQNode S j) 0
    (.inl (0,(criticalBoundaryPath S j).val))).mpr
  left
  have hs := congrArg Subtype.val (criticalBoundaryPath_start S j)
  change seedQNode S j=⟨0,(0,subdivisionEdgeStart baseTannerSquarePresentation 0 S
    (criticalBoundaryPath S j).val)⟩
  erw [subdivisionBoundaryEdgeStart_value] at hs
  exact congrArg (fun v => (⟨(0 : BDL26FiniteAlternatingCore.BaseX),((0 : BDL26FiniteTannerSquare.Two),v)⟩ :
    (BDL26ActualFailureReadout.RawOne S).X)) hs.symm
theorem criticalRadial_ne_boundary (S : OddScale) (j : Fin 2) :
    criticalRadial S j≠criticalBoundary S j := by
  intro h
  have h' := congrArg (fun r : (BDL26ActualFailureReadout.RawOne S).Q =>
    match r with
    | .inl v => match v.2 with
        | .inl e => match e.2 with
            | .inl a => match a.1.val with | .inl _ => true | .inr _ => false
            | _ => false
        | _ => false
    | _ => false) h
  dsimp only [criticalRadial,criticalBoundary,gammaRadial,seedRadial,criticalQZ] at h'
  change true=false at h'
  cases h'
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalOldXQueries
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open BDL26DecodingGraph BDL26IndexedDecoder BDL26ActualFailureReadout
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RXPhysicalCoordinateTrace
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
section
variable (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
  (R : TannerSquareCellularRegular P) (S : OddScale)
local notation "CF" => BDL26DecoderData.family (literalDecoderData P A R S)
local notation "G" => literalData P A R S
local notation "LX" => (literalLx P A R S :
  @LocalComplexData (TannerSquarePresentation.X P)
    (TannerSquareData.xFintype (TannerSquarePresentation.data P))
    (TannerSquareData.xDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "LQ" => (literalLq P A R S :
  @LocalComplexData (TannerSquarePresentation.Q P)
    (TannerSquareData.qFintype (TannerSquarePresentation.data P))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "U" => (Fin.succ (0 : StepIndex 1))
end
section
variable (S : OddScale)
local notation "P" => ConstructionState.presentation (BDL26DecodingGraph.state S 2)
local notation "A" => ConstructionState.admissible (BDL26DecodingGraph.state S 2)
local notation "R" => ConstructionState.regular (BDL26DecodingGraph.state S 2)
local notation "CF" => BDL26DecoderData.family (literalDecoderData P A R S)
local notation "G" => literalData P A R S
local notation "LX" => (literalLx P A R S :
  @LocalComplexData (TannerSquarePresentation.X P)
    (TannerSquareData.xFintype (TannerSquarePresentation.data P))
    (TannerSquareData.xDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "LQ" => (literalLq P A R S :
  @LocalComplexData (TannerSquarePresentation.Q P)
    (TannerSquareData.qFintype (TannerSquarePresentation.data P))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "U" => (Fin.succ (0 : StepIndex 1))
end
end CriticalOldXQueries
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalOldXQueries
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open BDL26DecodingGraph BDL26IndexedDecoder BDL26ActualFailureReadout
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
section
variable (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
  (R : TannerSquareCellularRegular P) (S : OddScale)
local notation "G" => literalData P A R S
local notation "LQ" => (literalLq P A R S :
  @LocalComplexData (TannerSquarePresentation.Q P)
    (TannerSquareData.qFintype (TannerSquarePresentation.data P))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
end
section
variable (S : OddScale)
local notation "P" => ConstructionState.presentation (BDL26DecodingGraph.state S 2)
local notation "A" => ConstructionState.admissible (BDL26DecodingGraph.state S 2)
local notation "R" => ConstructionState.regular (BDL26DecodingGraph.state S 2)
local notation "CF" => BDL26DecoderData.family (literalDecoderData P A R S)
local notation "G" => literalData P A R S
local notation "LX" => (literalLx P A R S :
  @LocalComplexData (TannerSquarePresentation.X P)
    (TannerSquareData.xFintype (TannerSquarePresentation.data P))
    (TannerSquareData.xDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "LQ" => (literalLq P A R S :
  @LocalComplexData (TannerSquarePresentation.Q P)
    (TannerSquareData.qFintype (TannerSquarePresentation.data P))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "U" => (Fin.succ (0 : StepIndex 1))
end
end CriticalOldXQueries
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalDegreeOneBudget
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26RXLocalReplacement BDL26TannerLocalRegularity BDL26LevelTwoCode
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open BDL26ActualFailureReadout
open BDL26DecodingGraph
open scoped Classical BigOperators
def bothCones (P : TannerSquarePresentation) (q : P.Q) (S : OddScale) :
    Word BDL26Field (QDoubleCylinderVertex P q S) := fun v => match v.2 with
  | .inl (.inl _) => 1
  | _ => 0
end CriticalDegreeOneBudget
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalOriginalChoice
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26RXLocalReplacement BDL26TannerLocalRegularity BDL26LevelTwoCode
open BDL26ActualFailureReadout
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable def originalChoice (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (q : P.Q) (w : Word BDL26Field (QDoubleCylinderVertex P q S)) :
    Word BDL26Field (QDoubleCylinderVertex P q S) :=
  let C := literalContract P A R S
  let E := wordEquiv (qCorrectionEquiv P S q)
  E.symm (Classical.choose (C.local_boundary_weight_budgets.cq q
    (C.rx_local_complexes.cqDelta1 q (E w)) ⟨E w,rfl⟩))
def coneWord (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (copy : BDL26FiniteTannerSquare.Two) : Word BDL26Field (QDoubleCylinderVertex P q S) :=
  canonicalBasisWord (copy,.inl (.inl ()))
end CriticalOriginalChoice
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalOriginalChoice
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26RXLocalReplacement BDL26TannerLocalRegularity BDL26LevelTwoCode
open BDL26ActualFailureReadout
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
end CriticalOriginalChoice
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalOriginalChoice
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26RXLocalReplacement BDL26TannerLocalRegularity BDL26LevelTwoCode
open BDL26ActualFailureReadout BDL26IndexedDecoder
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open BDL26DecodingGraph
open scoped Classical BigOperators
section
variable (S : OddScale)
local notation "P" => ConstructionState.presentation (BDL26DecodingGraph.state S 2)
local notation "A" => ConstructionState.admissible (BDL26DecodingGraph.state S 2)
local notation "R" => ConstructionState.regular (BDL26DecodingGraph.state S 2)
local notation "CF" => BDL26DecoderData.family (literalDecoderData P A R S)
local notation "G" => literalData P A R S
local notation "LQ" => (literalLq P A R S :
  @LocalComplexData (TannerSquarePresentation.Q P)
    (TannerSquareData.qFintype (TannerSquarePresentation.data P))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "U" => (Fin.succ (0 : StepIndex 1))
end
end CriticalOriginalChoice
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalOriginalChoice
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26RXLocalReplacement BDL26TannerLocalRegularity BDL26LevelTwoCode
open BDL26ActualFailureReadout
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
def terminalWord (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (copy : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q) :
    Word BDL26Field (QDoubleCylinderVertex P q S) := canonicalBasisWord (copy,.inl (.inr z))
end CriticalOriginalChoice
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalOriginalChoice
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26RXLocalReplacement BDL26TannerLocalRegularity BDL26LevelTwoCode
open BDL26ActualFailureReadout
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open BDL26DecodingGraph
open scoped Classical BigOperators
def otherCopy (c : BDL26FiniteTannerSquare.Two) :
    BDL26FiniteTannerSquare.Two := if c=0 then 1 else 0
def pairShift (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (ca cb : BDL26FiniteTannerSquare.Two) (a b : QStarEdge P q) :
    Word BDL26Field (QDoubleCylinderVertex P q S) :=
  terminalWord P q S ca a+terminalWord P q S cb b
def sharpQuery (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (ca cb : BDL26FiniteTannerSquare.Two) (a b c : QStarEdge P q) :
    Word BDL26Field (QDoubleCylinderVertex P q S) :=
  if ca=cb then
    coneWord P q S (otherCopy ca)+terminalWord P q S (otherCopy ca) a+
      terminalWord P q S (otherCopy ca) b
  else coneWord P q S cb+terminalWord P q S cb a+terminalWord P q S cb c
def firstArm (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (copy : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q) :
    QDoubleCylinderEdge P q S := .inl (copy,z,⟨0,S.half_pos⟩)
end CriticalOriginalChoice
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalPhysicalCx
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open BDL26ActualFailureReadout BDL26DecodingGraph
open scoped Classical BigOperators
section
variable (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
  (R : TannerSquareCellularRegular P) (S : OddScale)
local notation "CF" => BDL26DecoderData.family (literalDecoderData P A R S)
local notation "G" => literalData P A R S
local notation "LX" => (literalLx P A R S :
  @LocalComplexData (TannerSquarePresentation.X P)
    (TannerSquareData.xFintype (TannerSquarePresentation.data P))
    (TannerSquareData.xDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "LQ" => (literalLq P A R S :
  @LocalComplexData (TannerSquarePresentation.Q P)
    (TannerSquareData.qFintype (TannerSquarePresentation.data P))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "U" => (Fin.succ (0 : StepIndex 1))
end
end CriticalPhysicalCx
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalPhysicalCx
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open BDL26ActualFailureReadout BDL26DecodingGraph
open scoped Classical BigOperators
end CriticalPhysicalCx
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalPhysicalCx
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open BDL26DecodingGraph BDL26IndexedDecoder BDL26ActualFailureReadout
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RXPhysicalCoordinateTrace
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
section
variable (S : OddScale)
local notation "P" => ConstructionState.presentation (BDL26DecodingGraph.state S 2)
local notation "A" => ConstructionState.admissible (BDL26DecodingGraph.state S 2)
local notation "R" => ConstructionState.regular (BDL26DecodingGraph.state S 2)
local notation "CF" => BDL26DecoderData.family (literalDecoderData P A R S)
local notation "G" => literalData P A R S
local notation "LX" => (literalLx P A R S :
  @LocalComplexData (TannerSquarePresentation.X P)
    (TannerSquareData.xFintype (TannerSquarePresentation.data P))
    (TannerSquareData.xDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "LQ" => (literalLq P A R S :
  @LocalComplexData (TannerSquarePresentation.Q P)
    (TannerSquareData.qFintype (TannerSquarePresentation.data P))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "U" => (Fin.succ (0 : StepIndex 1))
end
end CriticalPhysicalCx
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace ActualCriticalStarGeometry
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RZLocalReplacement BDL26RXLocalReplacement BDL26ActualFailureReadout
open scoped Classical
noncomputable section
def opposite (c : BDL26FiniteTannerSquare.Two) : BDL26FiniteTannerSquare.Two := if c=0 then 1 else 0
theorem opposite_ne (c : BDL26FiniteTannerSquare.Two) : opposite c ≠ c := by
  exact (by decide : ∀ c : Fin 2, (if c=0 then 1 else 0) ≠ c) c
theorem shared_other (P : TannerSquarePresentation) (x : P.X) (z : P.Z)
    (q : P.Q) (hx : P.xq x q=true) (hz : P.qz q z=true) :
    ∃ r : P.Q, r≠q ∧ P.xq x r=true ∧ P.qz r z=true := by
  let a : SharedQ P.data x z := ⟨q,by simpa using And.intro hx hz⟩
  let fc := (P.faceCornerEquiv x z).symm a
  have hq : P.faceQ fc.1.val fc.2=q :=
    congrArg Subtype.val ((P.faceCornerEquiv x z).apply_symm_apply a)
  refine ⟨P.faceQ fc.1.val (opposite fc.2),?_,?_,?_⟩
  · intro he
    have hc : opposite fc.2=fc.2 :=
      P.faceQ_injective fc.1.val (he.trans hq.symm)
    exact opposite_ne fc.2 hc
  · simpa only [fc.1.property.1] using P.data.faceQ_xq fc.1.val (opposite fc.2)
  · simpa only [fc.1.property.2] using P.data.faceQ_qz fc.1.val (opposite fc.2)
theorem oldX_neighbour_terminal (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (x : P.X) (copy : BDL26FiniteTannerSquare.Two)
    (q : RZQ P S) (hq : rzXQIncidence P A S (.inr (x,copy)) q=true) :
    ∃ r : P.Q, ∃ hr : P.xq x r=true,
      q=.inr ⟨r,(copy,.inl (.inr ⟨x,hr⟩))⟩ := by
  classical
  rcases q with ⟨z,e⟩ | ⟨r,v⟩
  · change false=true at hq
    cases hq
  · change decide (∃ f : P.Face, ∃ c : BDL26FiniteTannerSquare.Two,
      P.faceX f=x ∧ oldXFaceQ P S c (f,copy)=.inr ⟨r,v⟩)=true at hq
    obtain ⟨f,c,hx,he⟩ := of_decide_eq_true hq
    have hr : P.xq x (P.faceQ f c)=true := by
      simpa only [hx] using P.data.faceQ_xq f c
    refine ⟨P.faceQ f c,hr,?_⟩
    simpa only [oldXFaceQ,hx] using he.symm
abbrev P (S : OddScale) := (state S 2).presentation
noncomputable abbrev PA (S : OddScale) := (state S 2).admissible
def x (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) : (P S).X :=
  .inr (seedQNode S j,copy)
def r (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) : (P S).Q :=
  CriticalOldXQueries.criticalTerminal S j copy (criticalRadial S j)
    (criticalRadial_incident S j)
def b (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) : (P S).Q :=
  CriticalOldXQueries.criticalTerminal S j copy (criticalBoundary S j)
    (criticalBoundary_incident S j)
def v (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) : (P S).Q :=
  CriticalOldXQueries.criticalTerminal S j copy (criticalVertical S j)
    (criticalVertical_incident S j)
def g (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) : (P S).Q :=
  CriticalOldXQueries.criticalTerminal S j copy (gammaCone S j)
    (seedQNode_incident S j)
theorem full_four_cover (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two)
    (q : (P S).Q) (hq : (P S).xq (x S j copy) q=true) :
    q=r S j copy ∨ q=b S j copy ∨ q=v S j copy ∨ q=g S j copy := by
  have hraw : rzXQIncidence (RawOne S) (rxState S baseState).admissible.toTannerSquareAdmissible S
      (.inr (seedQNode S j,copy)) q=true := hq
  obtain ⟨a,ha,rfl⟩ := oldX_neighbour_terminal (RawOne S)
    (rxState S baseState).admissible.toTannerSquareAdmissible S (seedQNode S j) copy q hraw
  rcases critical_four_neighbours S j a ha with h | h | h | h
  · subst a; exact Or.inl rfl
  · subst a; exact Or.inr (Or.inl rfl)
  · subst a; exact Or.inr (Or.inr (Or.inl rfl))
  · subst a; exact Or.inr (Or.inr (Or.inr rfl))
theorem terminal_incident (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two)
    (a : (RawOne S).Q) (ha : (RawOne S).xq (seedQNode S j) a=true) :
    (P S).xq (x S j copy)
      (CriticalOldXQueries.criticalTerminal S j copy a ha)=true := by
  let shared : SharedQ (RawOne S).data (seedQNode S j)
      ((rxState S baseState).admissible.qzRoot a).val :=
    ⟨a,by
      have hz := ((rxState S baseState).admissible.qzRoot a).property
      simpa using And.intro ha hz⟩
  let fc := ((RawOne S).faceCornerEquiv _ _).symm shared
  have he : (RawOne S).faceQ fc.1.val fc.2=a :=
    congrArg Subtype.val (((RawOne S).faceCornerEquiv _ _).apply_symm_apply shared)
  change decide (∃ f : (RawOne S).Face, ∃ c : BDL26FiniteTannerSquare.Two,
    (RawOne S).faceX f=seedQNode S j ∧
      oldXFaceQ (RawOne S) S c (f,copy)=
        CriticalOldXQueries.criticalTerminal S j copy a ha)=true
  apply decide_eq_true
  refine ⟨fc.1.val,fc.2,fc.1.property.1,?_⟩
  simp only [oldXFaceQ,CriticalOldXQueries.criticalTerminal,fc.1.property.1]
  apply congrArg Sum.inr
  refine Sigma.ext he ?_
  have ht (a a' : (RawOne S).Q) (haa' : a=a')
      (h0 : (RawOne S).xq (seedQNode S j) a=true)
      (h1 : (RawOne S).xq (seedQNode S j) a'=true) :
      HEq ((copy,.inl (.inr ⟨seedQNode S j,h0⟩)) :
        QDoubleCylinderVertex (transposePresentation (RawOne S)) a S)
        ((copy,.inl (.inr ⟨seedQNode S j,h1⟩)) :
          QDoubleCylinderVertex (transposePresentation (RawOne S)) a' S) := by
    cases haa'
    rfl
  exact ht _ _ he _ _
def shiftedZ (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two)
    (a : (RawOne S).Q) (ha : (RawOne S).xq (seedQNode S j) a=true)
    (z : (RawOne S).Z) (hz : (RawOne S).qz a z=true) : (P S).Z :=
  ((shiftedQZNeighbourEquiv (RawOne S) (rxState S baseState).admissible.toTannerSquareAdmissible S a
    (copy,.inl (.inr ⟨seedQNode S j,ha⟩))) ⟨z,hz⟩).val
theorem shiftedZ_incident (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two)
    (a : (RawOne S).Q) (ha : (RawOne S).xq (seedQNode S j) a=true)
    (z : (RawOne S).Z) (hz : (RawOne S).qz a z=true) :
    (P S).qz (CriticalOldXQueries.criticalTerminal S j copy a ha)
      (shiftedZ S j copy a ha z hz)=true :=
  ((shiftedQZNeighbourEquiv (RawOne S) (rxState S baseState).admissible.toTannerSquareAdmissible S a
    (copy,.inl (.inr ⟨seedQNode S j,ha⟩))) ⟨z,hz⟩).property
theorem shiftedZ_unique (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two)
    (a : (RawOne S).Q) (ha : (RawOne S).xq (seedQNode S j) a=true)
    (z : (RawOne S).Z) (hz : (RawOne S).qz a z=true)
    (hu : ∀ z', (RawOne S).qz a z'=true → z'=z)
    (t : (P S).Z)
    (ht : (P S).qz (CriticalOldXQueries.criticalTerminal S j copy a ha) t=true) :
    t=shiftedZ S j copy a ha z hz := by
  let E := shiftedQZNeighbourEquiv (RawOne S) (rxState S baseState).admissible.toTannerSquareAdmissible S a
    (copy,.inl (.inr ⟨seedQNode S j,ha⟩))
  let s := E.symm ⟨t,ht⟩
  have hs : s=⟨z,hz⟩ := Subtype.ext (hu s.val s.property)
  have he := congrArg Subtype.val (E.apply_symm_apply ⟨t,ht⟩)
  have hEs : E s=E ⟨z,hz⟩ := congrArg E hs
  have hv := congrArg Subtype.val hEs
  exact he.symm.trans hv
def zr (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) : (P S).Z :=
  shiftedZ S j copy (criticalRadial S j) (criticalRadial_incident S j)
    (seedRadialCheck S j ⟨S.half-1,by have := S.half_pos;omega⟩)
    (seedRadial_degree_one S j _).1
def zv (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) : (P S).Z :=
  shiftedZ S j copy (criticalVertical S j) (criticalVertical_incident S j)
    (criticalVerticalCheck S j) (criticalVertical_degree_one S j).1
def zg (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) : (P S).Z :=
  shiftedZ S j copy (gammaCone S j) (seedQNode_incident S j)
    (seedConeCheck S j) (seedCone_degree_one S j).1
theorem leaf_unique (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) :
    ((P S).qz (r S j copy) (zr S j copy)=true ∧
      ∀ z, (P S).qz (r S j copy) z=true → z=zr S j copy) ∧
    ((P S).qz (v S j copy) (zv S j copy)=true ∧
      ∀ z, (P S).qz (v S j copy) z=true → z=zv S j copy) ∧
    ((P S).qz (g S j copy) (zg S j copy)=true ∧
      ∀ z, (P S).qz (g S j copy) z=true → z=zg S j copy) := by
  exact ⟨⟨shiftedZ_incident S j copy _ _ _ _,
    shiftedZ_unique S j copy _ _ _ _ (seedRadial_degree_one S j _).2⟩,
    ⟨shiftedZ_incident S j copy _ _ _ _,
      shiftedZ_unique S j copy _ _ _ _ (criticalVertical_degree_one S j).2⟩,
    ⟨shiftedZ_incident S j copy _ _ _ _,
      shiftedZ_unique S j copy _ _ _ _ (seedCone_degree_one S j).2⟩⟩
theorem checks_distinct (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) :
    zr S j copy≠zv S j copy ∧ zr S j copy≠zg S j copy ∧
      zv S j copy≠zg S j copy := by
  constructor
  · intro h
    have hs := congrArg (fun z : (P S).Z => z.1) h
    change seedRadialCheck S j _=criticalVerticalCheck S j at hs
    cases hs
  constructor
  · intro h
    have hs := congrArg (fun z : (P S).Z => z.1) h
    change seedRadialCheck S j _=seedConeCheck S j at hs
    cases hs
  · intro h
    have hs := congrArg (fun z : (P S).Z => z.1) h
    change criticalVerticalCheck S j=seedConeCheck S j at hs
    cases hs
theorem ports_distinct (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) :
    r S j copy≠b S j copy ∧ r S j copy≠v S j copy ∧
    r S j copy≠g S j copy ∧ b S j copy≠v S j copy ∧
    b S j copy≠g S j copy ∧ v S j copy≠g S j copy := by
  have take (a a' : (RawOne S).Q)
      (ha : (RawOne S).xq (seedQNode S j) a=true)
      (ha' : (RawOne S).xq (seedQNode S j) a'=true)
      (he : CriticalOldXQueries.criticalTerminal S j copy a ha=
        CriticalOldXQueries.criticalTerminal S j copy a' ha') : a=a' := by
    exact congrArg (fun q : (P S).Q => match q with
      | .inl _ => a
      | .inr q => q.1) he
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro h; exact criticalRadial_ne_boundary S j (take _ _ _ _ h)
  · intro h; have h' := take _ _ _ _ h
    dsimp only [criticalRadial,gammaRadial,criticalVertical] at h'; cases h'
  · intro h; have h' := take _ _ _ _ h
    dsimp only [criticalRadial,gammaRadial,gammaCone] at h'; cases h'
  · intro h; have h' := take _ _ _ _ h
    dsimp only [criticalBoundary,criticalVertical] at h'; cases h'
  · intro h; have h' := take _ _ _ _ h
    dsimp only [criticalBoundary,gammaCone] at h'; cases h'
  · intro h; have h' := take _ _ _ _ h
    dsimp only [criticalVertical,gammaCone] at h'; cases h'
theorem hub_neighbours (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two)
    (z : (P S).Z) :
    (P S).qz (b S j copy) z=true ↔
      z=zr S j copy ∨ z=zv S j copy ∨ z=zg S j copy := by
  have hr := leaf_unique S j copy
  have hd := ports_distinct S j copy
  have hz := checks_distinct S j copy
  have hx (a : (RawOne S).Q) (ha : (RawOne S).xq (seedQNode S j) a=true) :=
    terminal_incident S j copy a ha
  have hxR : (P S).xq (x S j copy) (r S j copy)=true := hx _ _
  have hxB : (P S).xq (x S j copy) (b S j copy)=true := hx _ _
  have hxV : (P S).xq (x S j copy) (v S j copy)=true := hx _ _
  have hxG : (P S).xq (x S j copy) (g S j copy)=true := hx _ _
  constructor
  · intro hb
    obtain ⟨q,hne,hqx,hqz⟩ := shared_other (P S) (x S j copy) z (b S j copy) hxB hb
    rcases full_four_cover S j copy q hqx with he | he | he | he
    · exact Or.inl (hr.1.2 z (he ▸ hqz))
    · exact False.elim (hne he)
    · exact Or.inr (Or.inl (hr.2.1.2 z (he ▸ hqz)))
    · exact Or.inr (Or.inr (hr.2.2.2 z (he ▸ hqz)))
  · intro hz'
    have pairR : (P S).qz (b S j copy) (zr S j copy)=true := by
      obtain ⟨q,hne,hqx,hqz⟩ := shared_other (P S) (x S j copy) _ (r S j copy) hxR hr.1.1
      rcases full_four_cover S j copy q hqx with he | he | he | he
      · exact False.elim (hne he)
      · exact he ▸ hqz
      · exact False.elim (hz.1 (hr.2.1.2 _ (he ▸ hqz)))
      · exact False.elim (hz.2.1 (hr.2.2.2 _ (he ▸ hqz)))
    have pairV : (P S).qz (b S j copy) (zv S j copy)=true := by
      obtain ⟨q,hne,hqx,hqz⟩ := shared_other (P S) (x S j copy) _ (v S j copy) hxV hr.2.1.1
      rcases full_four_cover S j copy q hqx with he | he | he | he
      · exact False.elim (hz.1 (hr.1.2 _ (he ▸ hqz)).symm)
      · exact he ▸ hqz
      · exact False.elim (hne he)
      · exact False.elim (hz.2.2 (hr.2.2.2 _ (he ▸ hqz)))
    have pairG : (P S).qz (b S j copy) (zg S j copy)=true := by
      obtain ⟨q,hne,hqx,hqz⟩ := shared_other (P S) (x S j copy) _ (g S j copy) hxG hr.2.2.1
      rcases full_four_cover S j copy q hqx with he | he | he | he
      · exact False.elim (hz.2.1 (hr.1.2 _ (he ▸ hqz)).symm)
      · exact he ▸ hqz
      · exact False.elim (hz.2.2 (hr.2.1.2 _ (he ▸ hqz)).symm)
      · exact False.elim (hne he)
    rcases hz' with rfl | rfl | rfl
    · exact pairR
    · exact pairV
    · exact pairG
def faceFromShared (P : TannerSquarePresentation) (x : P.X) (z : P.Z)
    (q : P.Q) (hx : P.xq x q=true) (hz : P.qz q z=true) : P.Face :=
  (((P.faceCornerEquiv x z).symm ⟨q,by simpa using And.intro hx hz⟩).1).val
theorem faceFromShared_X (P : TannerSquarePresentation) (x : P.X) (z : P.Z)
    (q : P.Q) (hx : P.xq x q=true) (hz : P.qz q z=true) :
    P.faceX (faceFromShared P x z q hx hz)=x :=
  (((P.faceCornerEquiv x z).symm ⟨q,by simpa using And.intro hx hz⟩).1).property.1
theorem faceFromShared_Z (P : TannerSquarePresentation) (x : P.X) (z : P.Z)
    (q : P.Q) (hx : P.xq x q=true) (hz : P.qz q z=true) :
    P.faceZ (faceFromShared P x z q hx hz)=z :=
  (((P.faceCornerEquiv x z).symm ⟨q,by simpa using And.intro hx hz⟩).1).property.2
def fr (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) : (P S).Face :=
  faceFromShared (P S) (x S j copy) (zr S j copy) (r S j copy)
    (terminal_incident S j copy _ _) (leaf_unique S j copy).1.1
def fv (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) : (P S).Face :=
  faceFromShared (P S) (x S j copy) (zv S j copy) (v S j copy)
    (terminal_incident S j copy _ _) (leaf_unique S j copy).2.1.1
def fg (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) : (P S).Face :=
  faceFromShared (P S) (x S j copy) (zg S j copy) (g S j copy)
    (terminal_incident S j copy _ _) (leaf_unique S j copy).2.2.1
def cr (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) : BDL26FiniteTannerSquare.Two :=
  (((P S).faceCornerEquiv (x S j copy) (zr S j copy)).symm
    ⟨r S j copy,by
      change ((P S).xq (x S j copy) (r S j copy) &&
         (P S).qz (r S j copy) (zr S j copy))=true
      have hx : (P S).xq (x S j copy) (r S j copy)=true :=
        terminal_incident S j copy _ _
      have hz : (P S).qz (r S j copy) (zr S j copy)=true :=
        (leaf_unique S j copy).1.1
      rw [hx,hz]
      rfl⟩).2
theorem fr_leaf_corner (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) :
    (P S).faceQ (fr S j copy) (cr S j copy)=r S j copy := by
  exact congrArg Subtype.val
    (((P S).faceCornerEquiv (x S j copy) (zr S j copy)).apply_symm_apply
      ⟨r S j copy,by
        change ((P S).xq (x S j copy) (r S j copy) &&
           (P S).qz (r S j copy) (zr S j copy))=true
        have hx : (P S).xq (x S j copy) (r S j copy)=true :=
          terminal_incident S j copy _ _
        have hz : (P S).qz (r S j copy) (zr S j copy)=true :=
          (leaf_unique S j copy).1.1
        rw [hx,hz]
        rfl⟩)
theorem fr_hub_corner (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) :
    (P S).faceQ (fr S j copy) (opposite (cr S j copy))=b S j copy := by
  let q := (P S).faceQ (fr S j copy) (opposite (cr S j copy))
  have hfx : (P S).faceX (fr S j copy)=x S j copy :=
    faceFromShared_X (P S) (x S j copy) (zr S j copy) (r S j copy)
      (terminal_incident S j copy _ _) (leaf_unique S j copy).1.1
  have hfz : (P S).faceZ (fr S j copy)=zr S j copy :=
    faceFromShared_Z (P S) (x S j copy) (zr S j copy) (r S j copy)
      (terminal_incident S j copy _ _) (leaf_unique S j copy).1.1
  have hx : (P S).xq (x S j copy) q=true :=
    (congrArg (fun xx : (P S).X => (P S).xq xx q) hfx).symm.trans
      ((P S).data.faceQ_xq (fr S j copy) (opposite (cr S j copy)))
  have hz : (P S).qz q (zr S j copy)=true :=
    (congrArg (fun zz : (P S).Z => (P S).qz q zz) hfz).symm.trans
      ((P S).data.faceQ_qz (fr S j copy) (opposite (cr S j copy)))
  have hne : q≠r S j copy := by
    intro he
    apply opposite_ne (cr S j copy)
    exact (P S).faceQ_injective (fr S j copy)
      (he.trans (fr_leaf_corner S j copy).symm)
  have hr := leaf_unique S j copy
  have hd := checks_distinct S j copy
  rcases full_four_cover S j copy q hx with he | he | he | he
  · exact False.elim (hne he)
  · exact he
  · exact False.elim (hd.1 (hr.2.1.2 _ (he ▸ hz)))
  · exact False.elim (hd.2.1 (hr.2.2.2 _ (he ▸ hz)))
end
end ActualCriticalStarGeometry
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace ActualCriticalStarGeometry
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26FiniteAlternatingCore
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoDistance BDL26LevelTwoCode
open BDL26ActualFailureReadout BDL26DecodingGraph BDL26TannerLocalRegularity
open scoped Classical BigOperators
noncomputable section
def oldPair (S : OddScale) (j : Fin 2) : Word F (RawOne S).Q :=
  canonicalBasisWord (criticalRadial S j)+canonicalBasisWord (criticalBoundary S j)
def pairWord (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) : Word F (RawTwo S).Q :=
  (canonicalBasisWord (r S j copy) : Word F (RawTwo S).Q)+
    (canonicalBasisWord (b S j copy) : Word F (RawTwo S).Q)
def radialEdge (S : OddScale) (j : Fin 2) (i : Fin S.half) :
    DoubleCylinderEdge baseTannerSquarePresentation (0 : BaseX) S :=
  .inl (0,.inl (seedRadial j,i))
def boundaryEdge (S : OddScale) (j : Fin 2) :
    DoubleCylinderEdge baseTannerSquarePresentation (0 : BaseX) S :=
  .inl (0,.inl (criticalQZ j,⟨0,S.half_pos⟩))
end
end ActualCriticalStarGeometry
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace OriginalOneStepPhiBridge
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26LocalizedHistoryErrorDescent
open BDL26ActualFailureReadout BDL26TransposedStoppedDecoder BDL26CSSHamiltonian
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open scoped Classical BigOperators
noncomputable section
theorem original_flip_supported (S : OddScale) (n : Nat)
    (q : Physical S (n+2)) :
    hammingSupport (flip S n q) ⊆
      BDL26LocalizedHistoryErrorDescent.star S n (TopIndex n)
        (elementaryCenter S n q) := by
  rw [flip_eq_basis]
  exact elementary_support S n q
end
end OriginalOneStepPhiBridge
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint


