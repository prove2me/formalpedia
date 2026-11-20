-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T12:27:32.719165+00:00
-- url     : https://prove2.me/theorems/cf8c4d2c-5112-412a-8bb0-33af08f63f7d
-- title:
--   RXPrimitive C2 QEndpoint
-- statement:
--   Definitions and structural lemmas for RXPrimitive C2 QEndpoint, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_LiteralPart4_QECert
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
namespace OriginalOldXScaleExtension
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RXDecoderAdapter BDL26DecodingGraph
open scoped Classical BigOperators
noncomputable section
theorem two_opposite_of_ne (c d : BDL26FiniteTannerSquare.Two) (h : c≠d) :
    c=ActualCriticalStarGeometry.opposite d := by
  fin_cases c <;> fin_cases d
  all_goals simp [ActualCriticalStarGeometry.opposite] at *
theorem actual_radial_corner_unique (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two)
    (g : XStarFace (DirectOldXCounterexample.AP S) (DirectOldXCounterexample.AX S j outer))
    (c : BDL26FiniteTannerSquare.Two)
    (he : xStarFaceXQEdge (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer) g c=
      DirectOldXCounterexample.actualRadialStarEdge S j outer) :
    g=DirectOldXCounterexample.actualStarFace S j outer ∧
      c=ActualCriticalStarGeometry.cr S j outer := by
  have hQ : (DirectOldXCounterexample.AP S).faceQ g.val c=
      DirectOldXCounterexample.AL S j outer 0 := by
    have h := congrArg (fun e : XStarEdge (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer) =>
      match e.val with | .inl a => a.val.2 | .inr a => a.val.1) he
    simpa [xStarFaceXQEdge,faceXQEdge,
      DirectOldXCounterexample.actualRadialStarEdge_value] using h
  have hg : g=DirectOldXCounterexample.actualStarFace S j outer := by
    apply (DirectOldXCounterexample.actual_radial_incident_face S j outer g).mp
    rcases two_eq_zero_or_one c with hc | hc
    · exact Or.inl (by simpa [hc] using hQ.symm)
    · exact Or.inr (by simpa [hc] using hQ.symm)
  refine ⟨hg,?_⟩
  subst g
  by_contra hc
  have ho := two_opposite_of_ne c (ActualCriticalStarGeometry.cr S j outer) hc
  have hhub : (DirectOldXCounterexample.AP S).faceQ
      (DirectOldXCounterexample.actualStarFace S j outer).val c=
        DirectOldXCounterexample.AH S j outer := by
    simpa [DirectOldXCounterexample.actualStarFace,ho] using
      ActualCriticalStarGeometry.fr_hub_corner S j outer
  exact DirectOldXCounterexample.AL_ne_hub S j outer 0 (hQ.symm.trans hhub)
theorem scaledAlpha_actual_boundary (S : OddScale) (j : Fin 2) (outer copy : BDL26FiniteTannerSquare.Two) :
    doubleCylinderCoboundary1 (DirectOldXCounterexample.AP S)
      (DirectOldXCounterexample.AX S j outer) S (scaledAlpha S j outer copy)=
      canonicalBasisWord (F:=BDL26Field) (Sum.inl (copy,scaledSmallFace S j outer)) := by
  by_cases hc : ActualCriticalStarGeometry.cr S j outer=0
  · have hu : ∀ (g : XStarFace (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer)) (c : BDL26FiniteTannerSquare.Two),
        xStarFaceXQEdge _ _ g c=xStarFaceXQEdge _ _
          (DirectOldXCounterexample.actualStarFace S j outer) 0 →
        g=DirectOldXCounterexample.actualStarFace S j outer ∧ c=0 := by
      intro g c he
      have hr : xStarFaceXQEdge _ _ g c=DirectOldXCounterexample.actualRadialStarEdge S j outer := by
        simpa [DirectOldXCounterexample.actualRadialStarEdge,hc] using he
      simpa [hc] using actual_radial_corner_unique S j outer g c hr
    simpa [scaledAlpha,scaledSmallFace,hc] using
      horizontalStrip_whole_boundary (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer) S
        (DirectOldXCounterexample.actualStarFace S j outer) hu copy
  · have hc1 : ActualCriticalStarGeometry.cr S j outer=1 :=
      (two_eq_zero_or_one _).resolve_left hc
    have hu : ∀ (g : XStarFace (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer)) (c : BDL26FiniteTannerSquare.Two),
        xStarFaceXQEdge _ _ g c=xStarFaceXQEdge _ _
          (DirectOldXCounterexample.actualStarFace S j outer) 1 →
        g=DirectOldXCounterexample.actualStarFace S j outer ∧ c=1 := by
      intro g c he
      have hr : xStarFaceXQEdge _ _ g c=DirectOldXCounterexample.actualRadialStarEdge S j outer := by
        simpa [DirectOldXCounterexample.actualRadialStarEdge,hc1] using he
      simpa [hc1] using actual_radial_corner_unique S j outer g c hr
    simpa [scaledAlpha,scaledSmallFace,hc] using
      verticalStrip_whole_boundary (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer) S
        (DirectOldXCounterexample.actualStarFace S j outer) hu copy
theorem actual_hub_corner_unique (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two)
    (g : XStarFace (DirectOldXCounterexample.AP S) (DirectOldXCounterexample.AX S j outer))
    (c : BDL26FiniteTannerSquare.Two)
    (he : xStarFaceQZEdge (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer) g c=
      DirectOldXCounterexample.actualHubStarEdge S j outer) :
    g=DirectOldXCounterexample.actualStarFace S j outer ∧
      c=ActualCriticalStarGeometry.opposite (ActualCriticalStarGeometry.cr S j outer) := by
  have hQ : (DirectOldXCounterexample.AP S).faceQ g.val c=
      DirectOldXCounterexample.AH S j outer := by
    have h := congrArg (fun e : XStarEdge (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer) =>
      match e.val with | .inl a => a.val.2 | .inr a => a.val.1) he
    simpa [xStarFaceQZEdge,faceQZEdge,DirectOldXCounterexample.actualHubStarEdge,
      qToXBoundaryEdge,xStarBoundaryEdgeToStar,DirectOldXCounterexample.AHZ] using h
  have hZ : (DirectOldXCounterexample.AP S).faceZ g.val=
      DirectOldXCounterexample.AZ S j outer 0 := by
    have h := congrArg (fun e : XStarEdge (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer) =>
      match e.val with | .inl _ => none | .inr a => some a.val.2) he
    simpa [xStarFaceQZEdge,faceQZEdge,DirectOldXCounterexample.actualHubStarEdge,
      qToXBoundaryEdge,xStarBoundaryEdgeToStar,DirectOldXCounterexample.AHZ] using h
  have hg : g=DirectOldXCounterexample.actualStarFace S j outer := by
    apply Subtype.ext
    apply (DirectOldXCounterexample.AR S).faceXZ_injective
    apply Prod.ext
    · exact (show (DirectOldXCounterexample.AP S).faceX g.val=
        DirectOldXCounterexample.AX S j outer from by
          simpa [xStarFaceMember] using g.property).trans
        (show (DirectOldXCounterexample.AP S).faceX
          (DirectOldXCounterexample.actualStarFace S j outer).val=
            DirectOldXCounterexample.AX S j outer from by
          simpa [xStarFaceMember] using (DirectOldXCounterexample.actualStarFace S j outer).property).symm
    · exact hZ.trans (ActualCriticalStarGeometry.faceFromShared_Z
        (DirectOldXCounterexample.AP S) (DirectOldXCounterexample.AX S j outer)
        (DirectOldXCounterexample.AZ S j outer 0) (DirectOldXCounterexample.AL S j outer 0)
        (DirectOldXCounterexample.AL_incident S j outer 0)
        (DirectOldXCounterexample.AL_check S j outer 0)).symm
  refine ⟨hg,?_⟩
  apply two_opposite_of_ne
  intro hc
  subst g
  have hleaf : (DirectOldXCounterexample.AP S).faceQ
      (DirectOldXCounterexample.actualStarFace S j outer).val c=
        DirectOldXCounterexample.AL S j outer 0 := by
    have hr : DirectOldXCounterexample.AL S j outer 0=ActualCriticalStarGeometry.r S j outer := by
      simp [DirectOldXCounterexample.AL]
    simpa [DirectOldXCounterexample.actualStarFace,hc,hr] using
      ActualCriticalStarGeometry.fr_leaf_corner S j outer
  exact DirectOldXCounterexample.AL_ne_hub S j outer 0 (hleaf.symm.trans hQ)
theorem hub_horizontal_matrix (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x)
    (hu : ∀ (g : XStarFace P x) (c : BDL26FiniteTannerSquare.Two),
      xStarFaceQZEdge P x g c=xStarFaceQZEdge P x f 1 → g=f ∧ c=1)
    (g : XStarFace P x) (i j : Fin S.half) :
    subdivisionFaceEdgeMatrix P x S
      (Sum.inl (xStarFaceQZEdge P x f 1,firstSegment S)) (g,i,j)=
      if g=f ∧ i=firstSegment S ∧ j=lastSegment S then 1 else 0 := by
  let e : SubdivisionEdge P x S := Sum.inl (xStarFaceQZEdge P x f 1,firstSegment S)
  have heq (g : XStarFace P x) (c : BDL26FiniteTannerSquare.Two) :
      xStarFaceQZEdge P x f 1=xStarFaceQZEdge P x g c ↔ g=f ∧ c=1 :=
    ⟨fun h => hu g c h.symm,by rintro ⟨rfl,rfl⟩;rfl⟩
  have hne (g : XStarFace P x) (c : BDL26FiniteTannerSquare.Two) :
      xStarFaceQZEdge P x f 1≠xStarFaceXQEdge P x g c := by
    intro h
    have hh := congrArg Subtype.val h
    cases hh
  have hi0 : i.val+1≠0 := by omega
  have hj0 : j.val+1≠0 := by omega
  have hil : i.val≠S.half := Nat.ne_of_lt i.isLt
  have hjl : j.val≠S.half := Nat.ne_of_lt j.isLt
  have hlast : j.val+1=S.half ↔ j=lastSegment S := by
    simp only [lastSegment,Fin.ext_iff]
    have := S.half_pos
    have := j.isLt
    omega
  have hHlo : e≠subdivisionHorizontalEdge P x S g i (finCastGrid j) := by
    by_cases hz : j.val=0
    all_goals simp [e,subdivisionHorizontalEdge,finCastGrid,hz,hjl,hne,Prod.mk.injEq]
  have hVlo : e≠subdivisionVerticalEdge P x S g (finCastGrid i) j := by
    by_cases hz : i.val=0
    all_goals simp [e,subdivisionVerticalEdge,finCastGrid,hz,hil,hne,Prod.mk.injEq]
  have hVhi : e≠subdivisionVerticalEdge P x S g (finSuccGrid i) j := by
    have hn : xStarFaceQZEdge P x f 1≠xStarFaceQZEdge P x g 0 := by
      intro h
      exact (by decide : (0 : BDL26FiniteTannerSquare.Two)≠1) (hu g 0 h.symm).2
    by_cases hm : i.val+1=S.half
    all_goals
      have hhalf : S.half≠0 := Nat.ne_of_gt S.half_pos
      simp [e,subdivisionVerticalEdge,finSuccGrid,hi0,hm,hn,hhalf,Prod.mk.injEq]
  have hHhi : e=subdivisionHorizontalEdge P x S g i (finSuccGrid j) ↔
      g=f ∧ i=firstSegment S ∧ j=lastSegment S := by
    by_cases hm : j.val+1=S.half
    · dsimp only [e,subdivisionHorizontalEdge,finSuccGrid]
      rw [dif_neg hj0,dif_pos hm]
      simp only [Sum.inl.injEq,Prod.mk.injEq]
      constructor
      · rintro ⟨he,hi⟩
        exact ⟨((heq g 1).mp he).1,hi.symm,hlast.mp hm⟩
      · rintro ⟨hg,hi,hj⟩
        subst g
        subst i
        exact ⟨rfl,rfl⟩
    · have hn : j≠lastSegment S := fun h => hm (hlast.mpr h)
      simp [e,subdivisionHorizontalEdge,finSuccGrid,hj0,hm,hn]
  change (((if e=subdivisionHorizontalEdge P x S g i (finCastGrid j) then (1 : BDL26Field) else 0)+
    (if e=subdivisionVerticalEdge P x S g (finSuccGrid i) j then 1 else 0))+
    (if e=subdivisionHorizontalEdge P x S g i (finSuccGrid j) then 1 else 0))+
    (if e=subdivisionVerticalEdge P x S g (finCastGrid i) j then 1 else 0)=_
  simp only [if_neg hHlo,if_neg hVhi,if_neg hVlo,zero_add,add_zero]
  exact indicator_iff _ _ hHhi
theorem hub_vertical_matrix (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x)
    (hu : ∀ (g : XStarFace P x) (c : BDL26FiniteTannerSquare.Two),
      xStarFaceQZEdge P x g c=xStarFaceQZEdge P x f 0 → g=f ∧ c=0)
    (g : XStarFace P x) (i j : Fin S.half) :
    subdivisionFaceEdgeMatrix P x S
      (Sum.inl (xStarFaceQZEdge P x f 0,firstSegment S)) (g,i,j)=
      if g=f ∧ i=lastSegment S ∧ j=firstSegment S then 1 else 0 := by
  let e : SubdivisionEdge P x S := Sum.inl (xStarFaceQZEdge P x f 0,firstSegment S)
  have heq (g : XStarFace P x) (c : BDL26FiniteTannerSquare.Two) :
      xStarFaceQZEdge P x f 0=xStarFaceQZEdge P x g c ↔ g=f ∧ c=0 :=
    ⟨fun h => hu g c h.symm,by rintro ⟨rfl,rfl⟩;rfl⟩
  have hne (g : XStarFace P x) (c : BDL26FiniteTannerSquare.Two) :
      xStarFaceQZEdge P x f 0≠xStarFaceXQEdge P x g c := by
    intro h
    have hh := congrArg Subtype.val h
    cases hh
  have hi0 : i.val+1≠0 := by omega
  have hj0 : j.val+1≠0 := by omega
  have hil : i.val≠S.half := Nat.ne_of_lt i.isLt
  have hjl : j.val≠S.half := Nat.ne_of_lt j.isLt
  have hlast : i.val+1=S.half ↔ i=lastSegment S := by
    simp only [lastSegment,Fin.ext_iff]
    have := S.half_pos
    have := i.isLt
    omega
  have hHlo : e≠subdivisionHorizontalEdge P x S g i (finCastGrid j) := by
    by_cases hz : j.val=0
    all_goals simp [e,subdivisionHorizontalEdge,finCastGrid,hz,hjl,hne,Prod.mk.injEq]
  have hVlo : e≠subdivisionVerticalEdge P x S g (finCastGrid i) j := by
    by_cases hz : i.val=0
    all_goals simp [e,subdivisionVerticalEdge,finCastGrid,hz,hil,hne,Prod.mk.injEq]
  have hHhi : e≠subdivisionHorizontalEdge P x S g i (finSuccGrid j) := by
    have hn : xStarFaceQZEdge P x f 0≠xStarFaceQZEdge P x g 1 := by
      intro h
      exact (by decide : (1 : BDL26FiniteTannerSquare.Two)≠0) (hu g 1 h.symm).2
    by_cases hm : j.val+1=S.half
    all_goals
      have hhalf : S.half≠0 := Nat.ne_of_gt S.half_pos
      simp [e,subdivisionHorizontalEdge,finSuccGrid,hj0,hm,hn,hhalf,Prod.mk.injEq]
  have hVhi : e=subdivisionVerticalEdge P x S g (finSuccGrid i) j ↔
      g=f ∧ i=lastSegment S ∧ j=firstSegment S := by
    by_cases hm : i.val+1=S.half
    · dsimp only [e,subdivisionVerticalEdge,finSuccGrid]
      rw [dif_neg hi0,dif_pos hm]
      simp only [Sum.inl.injEq,Prod.mk.injEq]
      constructor
      · rintro ⟨he,hj⟩
        exact ⟨((heq g 0).mp he).1,hlast.mp hm,hj.symm⟩
      · rintro ⟨hg,hi,hj⟩
        subst g
        subst j
        exact ⟨rfl,rfl⟩
    · have hn : i≠lastSegment S := fun h => hm (hlast.mpr h)
      simp [e,subdivisionVerticalEdge,finSuccGrid,hi0,hm,hn]
  change (((if e=subdivisionHorizontalEdge P x S g i (finCastGrid j) then (1 : BDL26Field) else 0)+
    (if e=subdivisionVerticalEdge P x S g (finSuccGrid i) j then 1 else 0))+
    (if e=subdivisionHorizontalEdge P x S g i (finSuccGrid j) then 1 else 0))+
    (if e=subdivisionVerticalEdge P x S g (finCastGrid i) j then 1 else 0)=_
  simp only [if_neg hHlo,if_neg hHhi,if_neg hVlo,zero_add,add_zero]
  exact indicator_iff _ _ hVhi
theorem actual_hub_side (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    DirectOldXCounterexample.actualHubStarEdge S j outer=
      xStarFaceQZEdge (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer)
        (DirectOldXCounterexample.actualStarFace S j outer)
        (ActualCriticalStarGeometry.opposite (ActualCriticalStarGeometry.cr S j outer)) := by
  apply Subtype.ext
  apply congrArg Sum.inr
  apply Subtype.ext
  apply Prod.ext
  · exact (ActualCriticalStarGeometry.fr_hub_corner S j outer).symm
  · exact (ActualCriticalStarGeometry.faceFromShared_Z
      (DirectOldXCounterexample.AP S) (DirectOldXCounterexample.AX S j outer)
      (DirectOldXCounterexample.AZ S j outer 0) (DirectOldXCounterexample.AL S j outer 0)
      (DirectOldXCounterexample.AL_incident S j outer 0)
      (DirectOldXCounterexample.AL_check S j outer 0)).symm
theorem actual_error_small_column (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two)
    (g : XStarFace (DirectOldXCounterexample.AP S) (DirectOldXCounterexample.AX S j outer))
    (i k : Fin S.half) :
    subdivisionFaceEdgeMatrix (DirectOldXCounterexample.AP S)
      (DirectOldXCounterexample.AX S j outer) S
      (Sum.inl (DirectOldXCounterexample.actualHubStarEdge S j outer,firstSegment S)) (g,i,k)=
      if (g,i,k)=scaledSmallFace S j outer then 1 else 0 := by
  by_cases hc : ActualCriticalStarGeometry.cr S j outer=0
  · have hs : ActualCriticalStarGeometry.opposite (ActualCriticalStarGeometry.cr S j outer)=1 := by
      simp [hc,ActualCriticalStarGeometry.opposite]
    have hu : ∀ (g : XStarFace (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer)) (c : BDL26FiniteTannerSquare.Two),
      xStarFaceQZEdge _ _ g c=xStarFaceQZEdge _ _
        (DirectOldXCounterexample.actualStarFace S j outer) 1 →
        g=DirectOldXCounterexample.actualStarFace S j outer ∧ c=1 := by
      intro g c he
      have he' : xStarFaceQZEdge _ _ g c=DirectOldXCounterexample.actualHubStarEdge S j outer :=
        he.trans (by rw [actual_hub_side,hs])
      simpa [hs] using actual_hub_corner_unique S j outer g c he'
    rw [actual_hub_side,hs,hub_horizontal_matrix _ _ S _ hu]
    simp [scaledSmallFace,hc,Prod.mk.injEq]
  · have hc1 : ActualCriticalStarGeometry.cr S j outer=1 := (two_eq_zero_or_one _).resolve_left hc
    have hs : ActualCriticalStarGeometry.opposite (ActualCriticalStarGeometry.cr S j outer)=0 := by
      simp [hc1,ActualCriticalStarGeometry.opposite]
    have hu : ∀ (g : XStarFace (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer)) (c : BDL26FiniteTannerSquare.Two),
      xStarFaceQZEdge _ _ g c=xStarFaceQZEdge _ _
        (DirectOldXCounterexample.actualStarFace S j outer) 0 →
        g=DirectOldXCounterexample.actualStarFace S j outer ∧ c=0 := by
      intro g c he
      have he' : xStarFaceQZEdge _ _ g c=DirectOldXCounterexample.actualHubStarEdge S j outer :=
        he.trans (by rw [actual_hub_side,hs])
      simpa [hs] using actual_hub_corner_unique S j outer g c he'
    rw [actual_hub_side,hs,hub_vertical_matrix _ _ S _ hu]
    simp [scaledSmallFace,hc,Prod.mk.injEq]
theorem actual_single_error_whole_boundary (S : OddScale) (j : Fin 2)
    (outer copy : BDL26FiniteTannerSquare.Two) :
    doubleCylinderCoboundary1 (DirectOldXCounterexample.AP S)
      (DirectOldXCounterexample.AX S j outer) S
      (canonicalBasisWord (F:=BDL26Field) (DirectOldXCounterexample.actualErrorEdge S j outer copy))=
      canonicalBasisWord (F:=BDL26Field) (Sum.inl (copy,scaledSmallFace S j outer))+
      canonicalBasisWord (F:=BDL26Field) (Sum.inr (DirectOldXCounterexample.actualHubD S j outer)) := by
  funext face
  rw [QEC.Coding.BDL26RXPrimitiveC2QEndpoint.doubleCylinder_basis_column]
  rcases face with ⟨d,g,i,k⟩ | rect
  · change (if copy=d then subdivisionFaceEdgeMatrix (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer) S
        (Sum.inl (DirectOldXCounterexample.actualHubStarEdge S j outer,firstSegment S)) (g,i,k) else 0)=_
    rw [actual_error_small_column]
    simp only [Pi.add_apply,basis_value,Sum.inl.injEq,Sum.inl_ne_inr,if_false,add_zero]
    by_cases hd : copy=d
    · subst d
      simp only [Prod.mk.injEq,true_and,if_pos rfl,if_true]
    · have hd' : d≠copy := Ne.symm hd
      simp only [if_neg hd,Prod.mk.injEq,hd',false_and,if_false]
  · change (if (DirectOldXCounterexample.actualHubD S j outer).val=rect.val then (1:BDL26Field) else 0)=_
    have he : (Sum.inr rect : DoubleCylinderFace (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer) S)=
        Sum.inr (DirectOldXCounterexample.actualHubD S j outer) ↔
        (DirectOldXCounterexample.actualHubD S j outer).val=rect.val := by
      constructor
      · intro h
        exact (congrArg Subtype.val (Sum.inr.inj h)).symm
      · intro h
        exact congrArg Sum.inr (Subtype.ext h.symm)
    simp [basis_value,he]
theorem scaled_fixed_D_query (S : OddScale) (j : Fin 2) (outer copy : BDL26FiniteTannerSquare.Two) :
    doubleCylinderCoboundary1 (DirectOldXCounterexample.AP S)
      (DirectOldXCounterexample.AX S j outer) S
      (scaledAlpha S j outer copy+
        canonicalBasisWord (F:=BDL26Field) (DirectOldXCounterexample.actualErrorEdge S j outer copy))=
      canonicalBasisWord (F:=BDL26Field) (Sum.inr (DirectOldXCounterexample.actualHubD S j outer)) := by
  rw [map_add,scaledAlpha_actual_boundary,actual_single_error_whole_boundary]
  have hs := repair3_word_add_self
    (canonicalBasisWord (F:=BDL26Field) (Sum.inl (copy,scaledSmallFace S j outer)) :
      Word BDL26Field (DoubleCylinderFace (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer) S))
  rw [← add_assoc,hs,zero_add]
end
end OriginalOldXScaleExtension
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace OriginalOldXScaleExtension
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RXDecoderAdapter BDL26DecodingGraph
open MultiscaleDecoder.RXCoarseGraining
open scoped Classical BigOperators
noncomputable section
def scaledFixedDInput (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    DirectOldXCounterexample.ASyndrome S :=
  DirectOldXCounterexample.pureXInput (DirectOldXCounterexample.AP S)
    (DirectOldXCounterexample.AA S) (DirectOldXCounterexample.AR S) S
    (DirectOldXCounterexample.AX S j outer)
    (scaledAlpha S j outer 0+canonicalBasisWord (F:=BDL26Field)
      (DirectOldXCounterexample.actualErrorEdge S j outer 0))
theorem scaledFixedDInput_raw_query (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    (wordEquiv (xSyndromeEquiv (DirectOldXCounterexample.AP S) S
      (DirectOldXCounterexample.AX S j outer))).symm
      (restrictWordLinear ((literalLx (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AA S) (DirectOldXCounterexample.AR S) S).syndromeRegion
        (DirectOldXCounterexample.AX S j outer)) (scaledFixedDInput S j outer).val)=
      canonicalBasisWord (F:=BDL26Field) (Sum.inr (DirectOldXCounterexample.actualHubD S j outer)) :=
  (DirectOldXCounterexample.pureXInput_raw_query (DirectOldXCounterexample.AP S)
    (DirectOldXCounterexample.AA S) (DirectOldXCounterexample.AR S) S
    (DirectOldXCounterexample.AX S j outer) _).trans (scaled_fixed_D_query S j outer 0)
theorem scaledFixedDInput_actual_exit (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    ∃ c : BDL26FiniteTannerSquare.Two,∃ k : Fin S.half,
      xFlow (DirectOldXCounterexample.AP S) S (DirectOldXCounterexample.AX S j outer)
        (DirectOldXCounterexample.originalCxWord (DirectOldXCounterexample.AP S)
          (DirectOldXCounterexample.AA S) (DirectOldXCounterexample.AR S) S
          (scaledFixedDInput S j outer) (DirectOldXCounterexample.AX S j outer))=
        canonicalBasisWord (F:=BDL26Field) (rayImage (DirectOldXCounterexample.AP S)
          (DirectOldXCounterexample.AH S j outer) S (DirectOldXCounterexample.AHZ S j outer 0) c k) := by
  let P := DirectOldXCounterexample.AP S
  let A := DirectOldXCounterexample.AA S
  let R := DirectOldXCounterexample.AR S
  let x := DirectOldXCounterexample.AX S j outer
  let q := DirectOldXCounterexample.AH S j outer
  let z := DirectOldXCounterexample.AHZ S j outer
  let f := DirectOldXCounterexample.originalCxWord P A R S (scaledFixedDInput S j outer) x
  have hbd := DirectOldXCounterexample.originalCxWord_boundary P A R S (scaledFixedDInput S j outer) x
  rw [scaledFixedDInput_raw_query] at hbd
  have hw := DirectOldXCounterexample.originalCxWord_budget P A R S (scaledFixedDInput S j outer) x
  rw [scaledFixedDInput_raw_query,repair4_basis_weight_one] at hw
  have hsum (i : Fin 3) :
      (∑ k : Fin S.half,doubleCylinderCoboundary1 P x S f
        (Sum.inr (qToXSubdivisionBoundaryEdge P q x
          (DirectOldXCounterexample.AH_incident S j outer) S (z i,k))))=
        if i=0 then 1 else 0 := by
    rw [hbd]
    have hi := qToXSubdivisionBoundaryEdge_injective P q x
      (DirectOldXCounterexample.AH_incident S j outer) S
    have hz := DirectOldXCounterexample.AHZ_injective S j outer
    rw [Fintype.sum_eq_single (firstSegment S)]
    · have heq : qToXSubdivisionBoundaryEdge P q x
          (DirectOldXCounterexample.AH_incident S j outer) S (z i,firstSegment S)=
          DirectOldXCounterexample.actualHubD S j outer ↔ i=0 := by
        constructor
        · intro h
          change qToXSubdivisionBoundaryEdge P q x
            (DirectOldXCounterexample.AH_incident S j outer) S (z i,firstSegment S)=
            qToXSubdivisionBoundaryEdge P q x
              (DirectOldXCounterexample.AH_incident S j outer) S (z 0,firstSegment S) at h
          exact hz (congrArg Prod.fst (hi h))
        · intro h
          subst i
          rfl
      simp only [basis_value,Sum.inr.injEq,heq]
    · intro k hk
      have hn : (Sum.inr (qToXSubdivisionBoundaryEdge P q x
          (DirectOldXCounterexample.AH_incident S j outer) S (z i,k)) :
          DoubleCylinderFace P x S)≠Sum.inr (DirectOldXCounterexample.actualHubD S j outer) := by
        intro h
        have he := Sum.inr.inj h
        change qToXSubdivisionBoundaryEdge P q x
          (DirectOldXCounterexample.AH_incident S j outer) S (z i,k)=
          qToXSubdivisionBoundaryEdge P q x
            (DirectOldXCounterexample.AH_incident S j outer) S (z 0,firstSegment S) at he
        exact hk (congrArg Prod.snd (hi he))
      exact (basis_value _ _).trans (if_neg hn)
  apply actual_Cx_hub_ray_exit P A.toTannerSquareAdmissible S x q
    (DirectOldXCounterexample.AH_incident S j outer) z
    (DirectOldXCounterexample.AHZ_injective S j outer)
    (DirectOldXCounterexample.AL S j outer) (DirectOldXCounterexample.AL_ne_hub S j outer)
    (DirectOldXCounterexample.AL_incident S j outer) (DirectOldXCounterexample.ALZ S j outer)
    (fun _ => rfl) f hw
  · rw [hsum,hsum]
    decide
  · rw [hsum,hsum]
    decide
theorem scaledFixedDInput_actual_pair (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    ∃ p : BDL26FiniteTannerSquare.Two × Fin S.half,
      xFlow (DirectOldXCounterexample.AP S) S (DirectOldXCounterexample.AX S j outer)
        (DirectOldXCounterexample.originalCxWord (DirectOldXCounterexample.AP S)
          (DirectOldXCounterexample.AA S) (DirectOldXCounterexample.AR S) S
          (scaledFixedDInput S j outer) (DirectOldXCounterexample.AX S j outer))=
        canonicalBasisWord (F:=BDL26Field) (rayImage (DirectOldXCounterexample.AP S)
          (DirectOldXCounterexample.AH S j outer) S
          (DirectOldXCounterexample.AHZ S j outer 0) p.1 p.2) := by
  obtain ⟨c,k,h⟩ := scaledFixedDInput_actual_exit S j outer
  exact ⟨(c,k),h⟩
def actualSelectedCut (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : BDL26FiniteTannerSquare.Two × Fin S.half :=
  Classical.choose (scaledFixedDInput_actual_pair S j outer)
def actualOppositeCopy (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : BDL26FiniteTannerSquare.Two :=
  ActualCriticalStarGeometry.opposite (actualSelectedCut S j outer).1
def actualCutZero (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : Fin S.half :=
  if (actualSelectedCut S j outer).1=0 then (actualSelectedCut S j outer).2 else firstSegment S
def actualCutOne (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : Fin S.half :=
  if (actualSelectedCut S j outer).1=1 then (actualSelectedCut S j outer).2 else firstSegment S
def scaledHubW (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :=
  switchWord (DirectOldXCounterexample.AP S) (DirectOldXCounterexample.AH S j outer) S
    (DirectOldXCounterexample.AHZ S j outer 0) (DirectOldXCounterexample.AHZ S j outer 2)
    (DirectOldXCounterexample.AHZ S j outer 1) (actualCutZero S j outer)
def scaledHubK (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :=
  toggleWord (DirectOldXCounterexample.AP S) (DirectOldXCounterexample.AH S j outer) S
    (DirectOldXCounterexample.AHZ S j outer 0)
    (actualCutZero S j outer) (actualCutOne S j outer)
def scaledInput (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    DirectOldXCounterexample.ASyndrome S :=
  DirectOldXCounterexample.directInput (DirectOldXCounterexample.AP S)
    (DirectOldXCounterexample.AA S) (DirectOldXCounterexample.AR S) S
    (DirectOldXCounterexample.AX S j outer) (DirectOldXCounterexample.AH S j outer)
    (scaledAlpha S j outer (actualOppositeCopy S j outer)) (scaledHubW S j outer)
def scaledPhysicalEdge (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    DoubleCylinderEdge (DirectOldXCounterexample.AP S) (DirectOldXCounterexample.AX S j outer) S :=
  DirectOldXCounterexample.actualErrorEdge S j outer (actualOppositeCopy S j outer)
def scaledPhysical (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    BDL26CSSHamiltonian.Physical S 3 :=
  BDL26RXPhysicalCoordinateTrace.oldXPhysical S 1 (by decide) (seedQNode S j) outer
    (scaledPhysicalEdge S j outer)
end
end OriginalOldXScaleExtension
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace OriginalOldXScaleExtension
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RXDecoderAdapter BDL26DecodingGraph
open DirectOldXCounterexample
open MultiscaleDecoder.RXCoarseGraining MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open BDL26IndexedDecoder BDL26ActualFailureReadout BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping
open scoped Classical BigOperators
noncomputable section
def leafPrefix (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (copy : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q) (cut : Fin S.half) :=
  wholeCopy P q S copy+rayTail P q S copy z cut
def scaledActualTop (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : repair2C3Input S :=
  repair5_literal_to_actual S (scaledInput S j outer)
def scaledDomain (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    BDL26TransposedStoppedDecoder.XSyndromeDomain S 1 :=
  ⟨(scaledActualTop S j outer).val,by
    obtain ⟨e,he⟩ := (scaledActualTop S j outer).property
    exact ⟨e,(LinearMap.congr_fun
      (indexedFamily_coboundary1 S 3 (3 : LevelIndex 3)) e).symm.trans he⟩⟩
end
end OriginalOldXScaleExtension
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace OriginalOldXScaleExtension
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RXDecoderAdapter BDL26DecodingGraph
open DirectOldXCounterexample
open MultiscaleDecoder.RXCoarseGraining MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open BDL26IndexedDecoder BDL26ActualFailureReadout BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26LocalizedHistoryErrorDescent
open BDL26RXErrorPullback BDL26RXXStarTransport
open scoped Classical BigOperators
noncomputable section
abbrev scaledSigma (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :=
  repair2C3InputOfSyndrome S (scaledDomain S j outer)
abbrev scaledTau (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :=
  repair2C3PerturbTop S (scaledSigma S j outer)
    (repair2C3Flip S (scaledPhysical S j outer))
def scaledTop (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    LocalizedWord S 1 (scaledSigma S j outer) (scaledTau S j outer)
      (Fin.succ (0 : StepIndex 1)) :=
  initial S 1 (scaledSigma S j outer)
    (repair2C3Flip S (scaledPhysical S j outer))
    (elementaryCenter S 1 (scaledPhysical S j outer))
    (OriginalOneStepPhiBridge.original_flip_supported S 1 (scaledPhysical S j outer))
abbrev scaledA (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    Upper S 3 (2 : StepIndex 3) :=
  BDL26LocalizedHistoryErrorDescent.first S 1 (scaledSigma S j outer) (0 : StepIndex 1)
abbrev scaledB (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    Upper S 3 (2 : StepIndex 3) :=
  BDL26LocalizedHistoryErrorDescent.second S 1 (scaledSigma S j outer)
    (scaledTau S j outer) (0 : StepIndex 1) (scaledTop S j outer)
end
end OriginalOldXScaleExtension
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace OriginalOldXScaleExtension
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26RXDecoderAdapter
open BDL26DecodingGraph BDL26LocalizedHistoryErrorDescent BDL26ActualFailureReadout
open BDL26RXErrorPullback BDL26RXXStarTransport BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26ReplacementCochainMaps BDL26OwnerIncidenceMasks BDL26CSSHamiltonian
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26RXPhysicalCoordinateTrace
open DirectOldXCounterexample
open MultiscaleDecoder.RXCoarseGraining MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable section
def scaledX0 (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    Finset (AP S).X :=
  {BDL26RXPhysicalStarTransport.parentX S 3 (2 : StepIndex 3) (by decide)
    (scaledTop S j outer).center}
def scaledVeff (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    LocalPotential S (2 : StepIndex 3) (AX S j outer) :=
  if AX S j outer∈scaledX0 S j outer then
    localPotential S 3 (2 : StepIndex 3) (by decide) (AX S j outer)
      (scaledA S j outer) (scaledB S j outer) else 0
def scaledHubPotential (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : Word BDL26Field (QDoubleCylinderVertex (AP S) (AH S j outer) S) :=
  rxXQDegreeZero (AP S) (AA S).toTannerSquareAdmissible (AH S j outer)
    (AX S j outer) (AH_incident S j outer) S (scaledVeff S j outer)
def scaledBeta (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : BDL26Field :=
  scaledHubPotential S j outer (0,.inl (.inl ()))
end
end OriginalOldXScaleExtension
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26ActualFailureReadout BDL26RXPhysicalCoordinateTrace
open scoped Classical
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
namespace BaseDecoderTwoErrorWitness
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26ActualFailureReadout BDL26CSSHamiltonian
open scoped Classical
noncomputable section
def actualPairError (S : OddScale) : Word BDL26Field (Physical S 2) :=
  canonicalBasisWord (F:=BDL26Field) (ActualCriticalStarGeometry.r S 0 0)+
    canonicalBasisWord (F:=BDL26Field) (ActualCriticalStarGeometry.b S 0 0)
def actualPairResidual (S : OddScale) : Word BDL26Field (Physical S 2) :=
  actualPairError S+(fun q : Physical S 2 =>
    BDL26LevelTwoDecoder.decode S (zSyndrome S 2 (actualPairError S)) q)
def rawPairResidual (S : OddScale) : Word BDL26Field (RawTwo S).Q :=
  (ActualCriticalStarGeometry.pairWord S 0 0+
    (fun q : (RawTwo S).Q => BDL26LevelTwoDecoder.decode S 0 q))+
    (fun q : (RawTwo S).Q => BDL26LevelTwoDecoder.decode S
      (QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1 (RawTwo S) (ActualCriticalStarGeometry.pairWord S 0 0)) q)
end
end BaseDecoderTwoErrorWitness
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
noncomputable section
namespace QEC.Coding.BDL26BaseGeometricDomain
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open scoped Classical
end QEC.Coding.BDL26BaseGeometricDomain
end
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint.ActualCriticalStarGeometry
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26ActualFailureReadout BDL26RZMap1CoordinateBridge
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26RZLocalReplacement
open BDL26BaseGeometricDomain
open scoped Classical
noncomputable section
def geometric_sigma (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) :
    Word BDL26Field (P S).Z :=
  QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1 (P S) (pairWord S j copy)
end
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint.ActualCriticalStarGeometry
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26ActualFailureReadout
open scoped Classical
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint


