-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_LiteralPart3_QECert
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_LiteralPart3_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T10:53:04.68882+00:00
-- url     : https://prove2.me/theorems/7b3a2734-6810-498b-9f62-031309200a72
-- title:
--   RX primitive C2Q endpoint: literal segment 3
-- statement:
--   Definitions and structural lemmas for RXPrimitive C2 QEndpoint, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_LiteralPart2_QECert
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
noncomputable section
namespace QEC.Coding.BDL26ActualLocalizedResidualLift
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26HistorySyndromeSensitivity BDL26OwnerIncidenceMasks
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26ActualFailureReadout BDL26RZMap1CoordinateBridge
open BDL26CSSHamiltonian BDL26TransposedStoppedDecoder
open scoped Classical
end QEC.Coding.BDL26ActualLocalizedResidualLift
section OriginalCounterexampleWorking
attribute [local instance 2000] QEC.Coding.BDL26FiniteTannerSquare.TannerSquareData.xFintype
  QEC.Coding.BDL26FiniteTannerSquare.TannerSquareData.qFintype
  QEC.Coding.BDL26FiniteTannerSquare.TannerSquareData.zFintype
  QEC.Coding.BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  QEC.Coding.BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  QEC.Coding.BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] QEC.Coding.BDL26RXPrimitiveC2QEndpoint.repair3WordHAdd
  QEC.Coding.BDL26RXPrimitiveC2QEndpoint.repair6RegionWordHAdd
  QEC.Coding.BDL26RXPrimitiveC2QEndpoint.repair6C3TopHAdd
  QEC.Coding.BDL26RXPrimitiveC2QEndpoint.repair6C3UpperHAdd
  QEC.Coding.BDL26RXPrimitiveC2QEndpoint.repair6LiteralSyndromeHAdd
  QEC.Coding.BDL26RXPrimitiveC2QEndpoint.repair7TopLiteralCochainHAdd
  QEC.Coding.BDL26RXPrimitiveC2QEndpoint.repair7TopLiteralWordHAdd
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
open MultiscaleDecoder BDL26FiniteTannerSquare
open scoped Classical BigOperators
theorem flow_weight_le_one_word {I : Type} [Fintype I] [DecidableEq I]
    (w : Word BDL26Field I) (hw : HammingWeight w≤1) :
    w=0 ∨ ∃ p : I,w=canonicalBasisWord p := by
  classical
  by_cases hz : w=0
  · exact Or.inl hz
  right
  obtain ⟨p,hp⟩ : ∃ p : I,w p≠0 := by
    by_contra h
    push_neg at h
    apply hz
    funext p
    exact h p
  have hp1 : w p=1 := by
    rcases BDL26RXQEdgePairTransport.bit_cases (w p) with h0 | h1
    · exact False.elim (hp h0)
    · exact h1
  refine ⟨p,?_⟩
  funext q
  by_cases hqp : q=p
  · subst q
    simpa [basis_value] using hp1
  have hq : w q=0 := by
    by_contra hq
    have hsub : ({p,q} : Finset I)⊆hammingSupport w := by
      intro a ha
      simp only [Finset.mem_insert,Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq⟩
    have hc := (Finset.card_le_card hsub).trans hw
    have hne : p≠q := Ne.symm hqp
    have hcard : ({p,q} : Finset I).card=2 := by simp [hne]
    rw [hcard] at hc
    omega
  simpa [basis_value,hqp] using hq
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26RXPhysicalCoordinateTrace BDL26RXLocalReplacement BDL26RZLocalReplacement
open scoped Classical
abbrev OldXSeed (S : OddScale) :=
  Σ x : (state S 1).presentation.X, Σ c : BDL26FiniteTannerSquare.Two,
    DoubleCylinderEdge (state S 2).presentation (oldXOwner S 1 (by decide) x c) S
def oldXView (S : OddScale) (q : Physical S 3) : Option (OldXSeed S) :=
  match (BDL26RXDecoderAdapter.rxPhysicalQEquiv S 3 ⟨2,by omega⟩ (by decide)).symm q with
  | .inl ⟨.inr (x,c),d⟩ => some ⟨x,c,d⟩
  | _ => none
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare
open scoped Classical
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare
open scoped Classical BigOperators
theorem original_rectangle_coboundary
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f : Word BDL26Field (DoubleCylinderEdge P x S))
    (d : SubdivisionBoundaryEdge P x S) :
    doubleCylinderCoboundary1 P x S f (Sum.inr d) =
      (f (Sum.inl (0,d.val))+f (Sum.inl (1,d.val)))+
      (f (Sum.inr (subdivisionBoundaryEdgeStart P x S d))+
       f (Sum.inr (subdivisionBoundaryEdgeEnd P x S d))) := by
  classical
  rw [doubleCylinderCoboundary1,doubleCylinderBoundary2,
    wordLinearMapTranspose_toLin'_apply]
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [doubleCylinderFaceEdgeMatrix]
  have he (c : BDL26FiniteTannerSquare.Two) :
      (∑ e : SubdivisionEdge P x S,
        f (Sum.inl (c,e))*(if e=d.val then (1:BDL26Field) else 0)) =
        f (Sum.inl (c,d.val)) := by
    simp
  have hv :
      (∑ z : SubdivisionBoundaryVertex P x S,
        f (Sum.inr z)*
        ((if z=subdivisionBoundaryEdgeStart P x S d then (1:BDL26Field) else 0)+
         (if z=subdivisionBoundaryEdgeEnd P x S d then 1 else 0))) =
      f (Sum.inr (subdivisionBoundaryEdgeStart P x S d))+
      f (Sum.inr (subdivisionBoundaryEdgeEnd P x S d)) := by
    have hs (a : SubdivisionBoundaryVertex P x S) :
        (∑ z : SubdivisionBoundaryVertex P x S,
          if z=a then f (Sum.inr z) else 0)=f (Sum.inr a) := by
      calc
        _ = (if a=a then f (Sum.inr a) else 0) :=
          Finset.sum_eq_single a
            (fun z _ hza => if_neg hza)
            (fun h => False.elim (h (Finset.mem_univ a)))
        _ = f (Sum.inr a) := if_pos rfl
    simpa only [mul_add,Finset.sum_add_distrib,mul_ite,mul_one,mul_zero,hs]
  simpa only [Fin.sum_univ_two,he,hv]
theorem original_rectangle_pair
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f : Word BDL26Field (DoubleCylinderEdge P x S))
    (d e : SubdivisionBoundaryEdge P x S)
    (hs : subdivisionBoundaryEdgeStart P x S d=
      subdivisionBoundaryEdgeStart P x S e) :
    doubleCylinderCoboundary1 P x S f (Sum.inr d)+
      doubleCylinderCoboundary1 P x S f (Sum.inr e) =
    (f (Sum.inl (0,d.val))+f (Sum.inl (1,d.val)))+
    (f (Sum.inl (0,e.val))+f (Sum.inl (1,e.val)))+
    (f (Sum.inr (subdivisionBoundaryEdgeEnd P x S d))+
     f (Sum.inr (subdivisionBoundaryEdgeEnd P x S e))) := by
  rw [original_rectangle_coboundary,original_rectangle_coboundary,hs]
  have hcancel := repair3_scalar_add_self
    (f (Sum.inr (subdivisionBoundaryEdgeStart P x S e)))
  calc
    _ = ((f (Sum.inl (0,d.val))+f (Sum.inl (1,d.val)))+
          (f (Sum.inl (0,e.val))+f (Sum.inl (1,e.val)))+
          (f (Sum.inr (subdivisionBoundaryEdgeEnd P x S d))+
           f (Sum.inr (subdivisionBoundaryEdgeEnd P x S e))))+
        (f (Sum.inr (subdivisionBoundaryEdgeStart P x S e))+
         f (Sum.inr (subdivisionBoundaryEdgeStart P x S e))) := by ac_rfl
    _ = _ := by rw [hcancel,add_zero]
theorem two_nonzero_entries_cost_two {I : Type} [Fintype I]
    [DecidableEq I] (w : Word BDL26Field I) {a b : I}
    (hab : a≠b) (ha : w a≠0) (hb : w b≠0) :
    2≤HammingWeight w := by
  have hsub : ({a,b} : Finset I)⊆hammingSupport w := by
    intro k hk
    simp only [Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩
  have hc := Finset.card_le_card hsub
  have hcard : ({a,b} : Finset I).card=2 := by simp [hab]
  rw [hcard] at hc
  simpa only [HammingWeight_eq_card_hammingSupport] using hc
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare
open BDL26RXDecoderAdapter BDL26RXLocalReplacement BDL26TannerLocalRegularity
open scoped Classical BigOperators
theorem shared_bridge_zero
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X)
    (f : Word BDL26Field (DoubleCylinderEdge P x S))
    (hw : HammingWeight (xFlow P S x f)≤1)
    (q r : P.Q) (hqr : q≠r)
    (hxq : P.xq x q=true) (hxr : P.xq x r=true)
    (zq : QStarEdge P q) (zr : QStarEdge P r)
    (he : qToXDoubleCylinderEdge P A q x hxq S (Sum.inr zq)=
      qToXDoubleCylinderEdge P A r x hxr S (Sum.inr zr)) :
    f (qToXDoubleCylinderEdge P A q x hxq S (Sum.inr zq))=0 := by
  classical
  let i : RX2 P S := Sum.inl (Sum.inr ⟨q,Sum.inr zq⟩)
  let j : RX2 P S := Sum.inl (Sum.inr ⟨r,Sum.inr zr⟩)
  have hij : i≠j := by
    intro h
    have h' := Sum.inr.inj (Sum.inl.inj h)
    exact hqr (congrArg Sigma.fst h')
  have hi : xFlow P S x f i=
      f (qToXDoubleCylinderEdge P A q x hxq S (Sum.inr zq)) := by
    rw [xFlow_at_q P A]
    simp only [dif_pos hxq,rxXQDegreeOne,wordPullback_apply]
  have hj : xFlow P S x f j=
      f (qToXDoubleCylinderEdge P A r x hxr S (Sum.inr zr)) := by
    rw [xFlow_at_q P A]
    simp only [dif_pos hxr,rxXQDegreeOne,wordPullback_apply]
  by_contra hn
  have htwo := two_nonzero_entries_cost_two (xFlow P S x f) hij
    (by simpa only [hi] using hn) (by simpa only [hj,← he] using hn)
  omega
theorem two_parities_force_first_arm
    {I : Type} [Fintype I] [DecidableEq I]
    (w : Word BDL26Field I) (hw : HammingWeight w≤1)
    (e : Fin 3 × BDL26FiniteTannerSquare.Two → I) (hinj : Function.Injective e)
    (hrg : w (e (0,0))+w (e (0,1))+w (e (2,0))+w (e (2,1))=1)
    (hvg : w (e (1,0))+w (e (1,1))+w (e (2,0))+w (e (2,1))=0) :
    ∃ c : BDL26FiniteTannerSquare.Two,w=canonicalBasisWord (e (0,c)) := by
  rcases flow_weight_le_one_word w hw with hz | ⟨a,ha⟩
  · simp only [hz,Pi.zero_apply,zero_add] at hrg
    exact False.elim (zero_ne_one hrg)
  have hd (p q : Fin 3 × BDL26FiniteTannerSquare.Two) : e p=e q ↔ p=q := hinj.eq_iff
  subst w
  by_cases h0 : a=e (0,0)
  · exact ⟨0,congrArg canonicalBasisWord h0⟩
  by_cases h1 : a=e (0,1)
  · exact ⟨1,congrArg canonicalBasisWord h1⟩
  have h2 : a≠e (2,0) := by
    intro h
    subst a
    simp [basis_value,hd] at hvg
  have h3 : a≠e (2,1) := by
    intro h
    subst a
    simp [basis_value,hd] at hvg
  simp [basis_value,Ne.symm h0,Ne.symm h1,Ne.symm h2,Ne.symm h3] at hrg
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare
open BDL26RXDecoderAdapter BDL26RXLocalReplacement BDL26TannerLocalRegularity
open scoped Classical BigOperators
def firstHubRectangle (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (q : P.Q) (hxq : P.xq x q=true) (z : QStarEdge P q) :
    SubdivisionBoundaryEdge P x S :=
  qToXSubdivisionBoundaryEdge P q x hxq S (z,⟨0,S.half_pos⟩)
def hubArmCoordinate (P : TannerSquarePresentation) (S : OddScale)
    (q : P.Q) (z : QStarEdge P q) (c : BDL26FiniteTannerSquare.Two) : RX2 P S :=
  Sum.inl (Sum.inr ⟨q,Sum.inl (c,(z,⟨0,S.half_pos⟩))⟩)
theorem hubArmCoordinate_injective
    (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (z : Fin 3 → QStarEdge P q) (hz : Function.Injective z) :
    Function.Injective (fun p : Fin 3 × BDL26FiniteTannerSquare.Two => hubArmCoordinate P S q (z p.1) p.2) := by
  rintro ⟨i,c⟩ ⟨j,d⟩ h
  have he := Sum.inr.inj (Sum.inl.inj h)
  have he' := eq_of_heq (Sigma.mk.inj_iff.mp he).2
  have hp := Sum.inl.inj he'
  exact Prod.ext (hz (congrArg (fun t : BDL26FiniteTannerSquare.Two × QSubdivisionEdge P q S => t.2.1) hp))
    (congrArg Prod.fst hp)
theorem firstHubRectangle_start
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (q : P.Q) (hxq : P.xq x q=true) (z t : QStarEdge P q) :
    subdivisionBoundaryEdgeStart P x S (firstHubRectangle P S x q hxq z)=
      subdivisionBoundaryEdgeStart P x S (firstHubRectangle P S x q hxq t) := by
  apply Subtype.ext
  simp only [subdivisionBoundaryEdgeStart_value,firstHubRectangle,
    qToXSubdivisionBoundaryEdge,subdivisionOriginalBoundaryEdge,
    subdivisionEdgeStart,subdivisionSegmentStart,dif_pos rfl]
  apply congrArg Sum.inl
  apply Subtype.ext
  rfl
theorem firstHubRectangle_end
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (hh : S.half=1) (x : P.X)
    (q : P.Q) (hxq : P.xq x q=true) (z : QStarEdge P q) :
    Sum.inr (subdivisionBoundaryEdgeEnd P x S (firstHubRectangle P S x q hxq z))=
      qToXDoubleCylinderEdge P A q x hxq S (Sum.inr z) := by
  apply congrArg Sum.inr
  apply Subtype.ext
  simp only [subdivisionBoundaryEdgeEnd_value,firstHubRectangle,
    qToXSubdivisionBoundaryEdge,subdivisionOriginalBoundaryEdge,
    subdivisionEdgeEnd,subdivisionSegmentEnd,hh,dif_pos]
  apply congrArg Sum.inl
  apply Subtype.ext
  rfl
theorem shared_Z_bridge_image
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X) (q r : P.Q)
    (hxq : P.xq x q=true) (hxr : P.xq x r=true)
    (zq : QStarEdge P q) (zr : QStarEdge P r) (hz : zq.val=zr.val) :
    qToXDoubleCylinderEdge P A q x hxq S (Sum.inr zq)=
      qToXDoubleCylinderEdge P A r x hxr S (Sum.inr zr) := by
  apply congrArg Sum.inr
  apply Subtype.ext
  apply congrArg Sum.inl
  apply Subtype.ext
  exact congrArg Vertex.z hz
theorem actual_hub_exit_forced
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (hh : S.half=1) (x : P.X) (q : P.Q)
    (hxq : P.xq x q=true)
    (z : Fin 3 → QStarEdge P q) (hz : Function.Injective z)
    (leaf : Fin 3 → P.Q) (hleaf : ∀ i,leaf i≠q)
    (hxleaf : ∀ i,P.xq x (leaf i)=true)
    (lz : ∀ i,QStarEdge P (leaf i)) (hlz : ∀ i,(lz i).val=(z i).val)
    (f : Word BDL26Field (DoubleCylinderEdge P x S))
    (hw : HammingWeight (xFlow P S x f)≤1)
    (hrg : doubleCylinderCoboundary1 P x S f
        (Sum.inr (firstHubRectangle P S x q hxq (z 0)))+
      doubleCylinderCoboundary1 P x S f
        (Sum.inr (firstHubRectangle P S x q hxq (z 2)))=1)
    (hvg : doubleCylinderCoboundary1 P x S f
        (Sum.inr (firstHubRectangle P S x q hxq (z 1)))+
      doubleCylinderCoboundary1 P x S f
        (Sum.inr (firstHubRectangle P S x q hxq (z 2)))=0) :
    ∃ c : BDL26FiniteTannerSquare.Two,xFlow P S x f=canonicalBasisWord (hubArmCoordinate P S q (z 0) c) := by
  have hbridge (i : Fin 3) :
      f (Sum.inr (subdivisionBoundaryEdgeEnd P x S
        (firstHubRectangle P S x q hxq (z i))))=0 := by
    rw [firstHubRectangle_end P A S hh]
    exact shared_bridge_zero P A S x f hw q (leaf i) (Ne.symm (hleaf i))
      hxq (hxleaf i) (z i) (lz i)
      (shared_Z_bridge_image P A S x q (leaf i) hxq (hxleaf i)
        (z i) (lz i) (hlz i).symm)
  have hval (i : Fin 3) (c : BDL26FiniteTannerSquare.Two) :
      xFlow P S x f (hubArmCoordinate P S q (z i) c)=
      f (Sum.inl (c,(firstHubRectangle P S x q hxq (z i)).val)) := by
    unfold hubArmCoordinate
    rw [xFlow_at_q P A]
    simp only [dif_pos hxq,rxXQDegreeOne,wordPullback_apply]
    rfl
  have hpair (i j : Fin 3) :
      doubleCylinderCoboundary1 P x S f
          (Sum.inr (firstHubRectangle P S x q hxq (z i)))+
        doubleCylinderCoboundary1 P x S f
          (Sum.inr (firstHubRectangle P S x q hxq (z j)))=
      xFlow P S x f (hubArmCoordinate P S q (z i) 0)+
        xFlow P S x f (hubArmCoordinate P S q (z i) 1)+
        xFlow P S x f (hubArmCoordinate P S q (z j) 0)+
        xFlow P S x f (hubArmCoordinate P S q (z j) 1) := by
    rw [original_rectangle_pair P x S f _ _
      (firstHubRectangle_start P S x q hxq (z i) (z j)),hbridge i,hbridge j]
    simp only [zero_add,add_zero,hval]
    ac_rfl
  apply two_parities_force_first_arm (xFlow P S x f) hw
    (fun p : Fin 3 × BDL26FiniteTannerSquare.Two => hubArmCoordinate P S q (z p.1) p.2)
    (hubArmCoordinate_injective P S q z hz)
  · exact (hpair 0 2).symm.trans hrg
  · exact (hpair 1 2).symm.trans hvg
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
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
noncomputable def originalCxWord (sigma : (CF).Syndrome U) (x : P.X) :
    Word BDL26Field (DoubleCylinderEdge P x S) :=
  (wordEquiv (xCorrectionEquiv P S x)).symm
    (restrictWordLinear ((LX).correctionRegion x) (cxComponentTotal G sigma.val x))
theorem originalCxWord_boundary (sigma : (CF).Syndrome U) (x : P.X) :
    doubleCylinderCoboundary1 P x S (originalCxWord P A R S sigma x)=
      (wordEquiv (xSyndromeEquiv P S x)).symm
        (restrictWordLinear ((LX).syndromeRegion x) sigma.val) := by
  have hr : CxLocalRangeAt G sigma.val x :=
    (G).contract.cx_local_ranges_of_syndrome sigma x
  have hd := cxComponentTotal_local_delta G sigma.val x hr
  funext face
  have he := congrFun hd (xSyndromeEquiv P S x face)
  erw [localCx_delta1_apply] at he
  exact he
theorem originalCxWord_budget (sigma : (CF).Syndrome U) (x : P.X) :
    HammingWeight (xFlow P S x (originalCxWord P A R S sigma x))≤
      HammingWeight ((wordEquiv (xSyndromeEquiv P S x)).symm
        (restrictWordLinear ((LX).syndromeRegion x) sigma.val)) := by
  have hr : CxLocalRangeAt G sigma.val x :=
    (G).contract.cx_local_ranges_of_syndrome sigma x
  have hw := cxComponentTotal_local_flow_weight G sigma.val x hr
  change HammingWeight (xFlow P S x (originalCxWord P A R S sigma x))≤_ at hw
  exact hw.trans_eq (wordEquiv_weight (xSyndromeEquiv P S x).symm _).symm
end
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26IndexedDecoder BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
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
def directXExtension (x : P.X)
    (alpha : Word BDL26Field (DoubleCylinderEdge P x S)) : (CF).Cochain1 U :=
  extendWordLinear ((LX).correctionRegion x)
    (wordEquiv (xCorrectionEquiv P S x) alpha)
def directQExtension (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) : (CF).Cochain1 U :=
  extendWordLinear ((LQ).correctionRegion q)
    (wordEquiv (qCorrectionEquiv P S q) w)
def pureXInput (x : P.X)
    (alpha : Word BDL26Field (DoubleCylinderEdge P x S)) : (CF).Syndrome U :=
  ⟨(CF).coboundary1 U (directXExtension P A R S x alpha),
    ⟨directXExtension P A R S x alpha,rfl⟩⟩
def directInput (x : P.X) (q : P.Q)
    (alpha : Word BDL26Field (DoubleCylinderEdge P x S))
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) : (CF).Syndrome U :=
  ⟨(CF).coboundary1 U
      (directXExtension P A R S x alpha+directQExtension P A R S q w),
    ⟨directXExtension P A R S x alpha+directQExtension P A R S q w,rfl⟩⟩
end
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare
open BDL26RXDecoderAdapter BDL26RXLocalReplacement BDL26TannerLocalRegularity
open scoped Classical BigOperators
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
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
theorem firstHubRectangle_injective (x : P.X) (q : P.Q)
    (hxq : P.xq x q=true) :
    Function.Injective (firstHubRectangle P S x q hxq) := by
  intro z t h
  have he := qToXSubdivisionBoundaryEdge_injective P q x hxq S h
  exact congrArg Prod.fst he
theorem original_D_query_hub_exit
    (hh : S.half=1) (x : P.X) (q : P.Q) (hxq : P.xq x q=true)
    (z : Fin 3 → QStarEdge P q) (hz : Function.Injective z)
    (leaf : Fin 3 → P.Q) (hleaf : ∀ i,leaf i≠q)
    (hxleaf : ∀ i,P.xq x (leaf i)=true)
    (lz : ∀ i,QStarEdge P (leaf i)) (hlz : ∀ i,(lz i).val=(z i).val)
    (sigma : (CF).Syndrome U)
    (hquery : (wordEquiv (xSyndromeEquiv P S x)).symm
      (restrictWordLinear ((LX).syndromeRegion x) sigma.val)=
      canonicalBasisWord (Sum.inr (firstHubRectangle P S x q hxq (z 0)))) :
    ∃ c : BDL26FiniteTannerSquare.Two,xFlow P S x (originalCxWord P A R S sigma x)=
      canonicalBasisWord (hubArmCoordinate P S q (z 0) c) := by
  have hbd := originalCxWord_boundary P A R S sigma x
  rw [hquery] at hbd
  have hw := originalCxWord_budget P A R S sigma x
  rw [hquery,repair4_basis_weight_one] at hw
  have hd : Function.Injective (fun i : Fin 3 => firstHubRectangle P S x q hxq (z i)) :=
    (firstHubRectangle_injective P S x q hxq).comp hz
  have h02 : firstHubRectangle P S x q hxq (z 0)≠
      firstHubRectangle P S x q hxq (z 2) := fun h => (by decide : (0:Fin 3)≠2) (hd h)
  have h01 : firstHubRectangle P S x q hxq (z 0)≠
      firstHubRectangle P S x q hxq (z 1) := fun h => (by decide : (0:Fin 3)≠1) (hd h)
  apply actual_hub_exit_forced P A.toTannerSquareAdmissible S hh x q hxq
    z hz leaf hleaf hxleaf lz hlz (originalCxWord P A R S sigma x) hw
  · rw [hbd]
    simp [basis_value,h02,Ne.symm h02]
  · rw [hbd]
    simp [basis_value,h01,Ne.symm h01,h02,Ne.symm h02]
end
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare
open BDL26RXDecoderAdapter BDL26RXLocalReplacement BDL26TannerLocalRegularity
open scoped Classical BigOperators
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
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
theorem directXExtension_restrict_same (x : P.X)
    (alpha : Word BDL26Field (DoubleCylinderEdge P x S)) :
    restrictWordLinear ((LX).correctionRegion x) (directXExtension P A R S x alpha)=
      wordEquiv (xCorrectionEquiv P S x) alpha := by
  exact region_restrict_extend _ _
include A R
end
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open BDL26DecodingGraph
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
abbrev AP (S : OddScale) := (state S 2).presentation
abbrev AA (S : OddScale) := (state S 2).admissible
abbrev AR (S : OddScale) := (state S 2).regular
abbrev AX (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :=
  ActualCriticalStarGeometry.x S j outer
abbrev AH (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :=
  ActualCriticalStarGeometry.b S j outer
def AL (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (i : Fin 3) : (AP S).Q :=
  if i=0 then ActualCriticalStarGeometry.r S j outer else
  if i=1 then ActualCriticalStarGeometry.v S j outer else
    ActualCriticalStarGeometry.g S j outer
def AZ (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (i : Fin 3) : (AP S).Z :=
  if i=0 then ActualCriticalStarGeometry.zr S j outer else
  if i=1 then ActualCriticalStarGeometry.zv S j outer else
    ActualCriticalStarGeometry.zg S j outer
theorem AL_incident (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (i : Fin 3) :
    (AP S).xq (AX S j outer) (AL S j outer i)=true := by
  fin_cases i
  all_goals exact ActualCriticalStarGeometry.terminal_incident S j outer _ _
theorem AH_incident (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    (AP S).xq (AX S j outer) (AH S j outer)=true :=
  ActualCriticalStarGeometry.terminal_incident S j outer _ _
theorem AL_ne_hub (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (i : Fin 3) :
    AL S j outer i≠AH S j outer := by
  have h := ActualCriticalStarGeometry.ports_distinct S j outer
  fin_cases i
  · exact h.1
  · exact Ne.symm h.2.2.2.1
  · exact Ne.symm h.2.2.2.2.1
theorem AL_check (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (i : Fin 3) :
    (AP S).qz (AL S j outer i) (AZ S j outer i)=true := by
  have h := ActualCriticalStarGeometry.leaf_unique S j outer
  fin_cases i
  · exact h.1.1
  · exact h.2.1.1
  · exact h.2.2.1
theorem AH_check (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (i : Fin 3) :
    (AP S).qz (AH S j outer) (AZ S j outer i)=true := by
  apply (ActualCriticalStarGeometry.hub_neighbours S j outer _).mpr
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
def AHZ (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (i : Fin 3) :
    QStarEdge (AP S) (AH S j outer) := ⟨AZ S j outer i,AH_check S j outer i⟩
def ALZ (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (i : Fin 3) :
    QStarEdge (AP S) (AL S j outer i) := ⟨AZ S j outer i,AL_check S j outer i⟩
theorem AHZ_injective (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    Function.Injective (AHZ S j outer) := by
  intro i k he
  have h := ActualCriticalStarGeometry.checks_distinct S j outer
  have hv := congrArg Subtype.val he
  fin_cases i <;> fin_cases k
  all_goals first | rfl | exact False.elim (h.1 hv) |
    exact False.elim (h.1 hv.symm) | exact False.elim (h.2.1 hv) |
    exact False.elim (h.2.1 hv.symm) | exact False.elim (h.2.2 hv) |
    exact False.elim (h.2.2 hv.symm)
abbrev ASyndrome (S : OddScale) :=
  (literalDecoderData (AP S) (AA S) (AR S) S).family.Syndrome
    (Fin.succ (0 : StepIndex 1))
def actualHubD (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    SubdivisionBoundaryEdge (AP S) (AX S j outer) S :=
  firstHubRectangle (AP S) S (AX S j outer) (AH S j outer)
    (AH_incident S j outer) (AHZ S j outer 0)
theorem actual_D_original_exit (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (sigma : ASyndrome S)
    (hquery : (wordEquiv (xSyndromeEquiv (AP S) S (AX S j outer))).symm
      (restrictWordLinear ((literalLx (AP S) (AA S) (AR S) S).syndromeRegion
        (AX S j outer)) sigma.val)=
      canonicalBasisWord (Sum.inr (actualHubD S j outer))) :
    ∃ c : BDL26FiniteTannerSquare.Two,xFlow (AP S) S (AX S j outer)
      (originalCxWord (AP S) (AA S) (AR S) S sigma (AX S j outer))=
      canonicalBasisWord (hubArmCoordinate (AP S) S (AH S j outer) (AHZ S j outer 0) c) := by
  exact original_D_query_hub_exit (AP S) (AA S) (AR S) S hh
    (AX S j outer) (AH S j outer) (AH_incident S j outer)
    (AHZ S j outer) (AHZ_injective S j outer) (AL S j outer)
    (AL_ne_hub S j outer) (AL_incident S j outer) (ALZ S j outer)
    (fun _ => rfl) sigma hquery
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare
open scoped Classical BigOperators
theorem doubleCylinder_basis_column
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (e : DoubleCylinderEdge P x S) (f : DoubleCylinderFace P x S) :
    doubleCylinderCoboundary1 P x S (canonicalBasisWord e) f=
      doubleCylinderFaceEdgeMatrix P x S e f := by
  rw [doubleCylinderCoboundary1,doubleCylinderBoundary2,
    wordLinearMapTranspose_toLin'_apply]
  simp [basis_value]
theorem halfOne_subdivision_original_column
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) (hh : S.half=1)
    (e : XStarEdge P x) (f : XStarFace P x) :
    subdivisionFaceEdgeMatrix P x S (Sum.inl (e,⟨0,S.half_pos⟩))
      (f,⟨0,S.half_pos⟩,⟨0,S.half_pos⟩)=faceEdgeMatrix P e.val f.val := by
  classical
  let k : Fin S.half := ⟨0,S.half_pos⟩
  let z : Fin (S.half+1) := ⟨0,by omega⟩
  let o : Fin (S.half+1) := ⟨1,by omega⟩
  have h0 : (0 : Nat) ≠ S.half := by omega
  have h1 : (1 : Nat) = S.half := hh.symm
  have hH0 : subdivisionHorizontalEdge P x S f k z=
      Sum.inl (xStarFaceXQEdge P x f 0,k) := by
    exact dif_pos rfl
  have hV0 : subdivisionVerticalEdge P x S f z k=
      Sum.inl (xStarFaceXQEdge P x f 1,k) := by
    exact dif_pos rfl
  have hH1 : subdivisionHorizontalEdge P x S f k o=
      Sum.inl (xStarFaceQZEdge P x f 1,k) := by
    exact (dif_neg (by decide : (1:Nat)≠0)).trans (dif_pos h1)
  have hV1 : subdivisionVerticalEdge P x S f o k=
      Sum.inl (xStarFaceQZEdge P x f 0,k) := by
    exact (dif_neg (by decide : (1:Nat)≠0)).trans (dif_pos h1)
  change (((if Sum.inl (e,k)=subdivisionHorizontalEdge P x S f k z then (1:BDL26Field) else 0)+
    (if Sum.inl (e,k)=subdivisionVerticalEdge P x S f o k then 1 else 0))+
    (if Sum.inl (e,k)=subdivisionHorizontalEdge P x S f k o then 1 else 0))+
    (if Sum.inl (e,k)=subdivisionVerticalEdge P x S f z k then 1 else 0)=_
  rw [hH0,hV1,hH1,hV0]
  simp only [Sum.inl.injEq,Prod.mk.injEq,and_true,faceEdgeMatrix,
    xStarFaceXQEdge,xStarFaceQZEdge,Subtype.ext_iff]
  ac_rfl
theorem radial_cellular_column
    (P : TannerSquarePresentation) (x : P.X) (r : P.Q)
    (hx : P.xq x r=true) (f : P.Face) (hfx : P.faceX f=x) :
    faceEdgeMatrix P (Sum.inl ⟨(x,r),hx⟩) f=
      if r=P.faceQ f 0 ∨ r=P.faceQ f 1 then 1 else 0 := by
  have hn : P.faceQ f 0≠P.faceQ f 1 :=
    fun h => (by decide : (0:BDL26FiniteTannerSquare.Two)≠1) (P.faceQ_injective f h)
  by_cases h0 : r=P.faceQ f 0
  · have h1 : r≠P.faceQ f 1 := fun h => hn (h0.symm.trans h)
    simp [faceEdgeMatrix,faceXQEdge,faceQZEdge,hfx,h0,h1,hn,Ne.symm hn]
  · by_cases h1 : r=P.faceQ f 1
    · simp [faceEdgeMatrix,faceXQEdge,faceQZEdge,hfx,h0,h1,hn,Ne.symm hn]
    · simp [faceEdgeMatrix,faceXQEdge,faceQZEdge,hfx,h0,h1,hn,Ne.symm hn]
theorem QZ_cellular_column
    (P : TannerSquarePresentation) (q : P.Q) (z : P.Z)
    (hq : P.qz q z=true) (f : P.Face) :
    faceEdgeMatrix P (Sum.inr ⟨(q,z),hq⟩) f=
      if z=P.faceZ f ∧ (q=P.faceQ f 0 ∨ q=P.faceQ f 1) then 1 else 0 := by
  have hn : P.faceQ f 0≠P.faceQ f 1 :=
    fun h => (by decide : (0:BDL26FiniteTannerSquare.Two)≠1) (P.faceQ_injective f h)
  by_cases hz : z=P.faceZ f
  · by_cases h0 : q=P.faceQ f 0
    · have h1 : q≠P.faceQ f 1 := fun h => hn (h0.symm.trans h)
      simp [faceEdgeMatrix,faceXQEdge,faceQZEdge,hz,h0,h1,hn,Ne.symm hn]
    · by_cases h1 : q=P.faceQ f 1
      · simp [faceEdgeMatrix,faceXQEdge,faceQZEdge,hz,h0,h1,hn,Ne.symm hn]
      · simp [faceEdgeMatrix,faceXQEdge,faceQZEdge,hz,h0,h1,hn,Ne.symm hn]
  · simp [faceEdgeMatrix,faceXQEdge,faceQZEdge,hz]
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26DecodingGraph
open scoped Classical BigOperators
def actualStarFace (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    XStarFace (AP S) (AX S j outer) :=
  ⟨ActualCriticalStarGeometry.fr S j outer,by
    have hfx : (AP S).faceX (ActualCriticalStarGeometry.fr S j outer)=AX S j outer :=
      ActualCriticalStarGeometry.faceFromShared_X
        (AP S) (AX S j outer) (AZ S j outer 0) (AL S j outer 0)
        (AL_incident S j outer 0) (AL_check S j outer 0)
    simpa only [xStarFaceMember,decide_eq_true_eq] using hfx⟩
def actualRadialStarEdge (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    XStarEdge (AP S) (AX S j outer) :=
  xStarFaceXQEdge (AP S) (AX S j outer) (actualStarFace S j outer)
    (ActualCriticalStarGeometry.cr S j outer)
def actualHubStarEdge (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    XStarEdge (AP S) (AX S j outer) :=
  xStarBoundaryEdgeToStar (AP S) (AX S j outer)
    (qToXBoundaryEdge (AP S) (AH S j outer) (AX S j outer)
      (AH_incident S j outer) (AHZ S j outer 0))
def actualSmallFace (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    SubdivisionFace (AP S) (AX S j outer) S :=
  (actualStarFace S j outer,⟨0,S.half_pos⟩,⟨0,S.half_pos⟩)
def actualAlphaEdge (S : OddScale) (j : Fin 2) (outer c : BDL26FiniteTannerSquare.Two) :
    DoubleCylinderEdge (AP S) (AX S j outer) S :=
  Sum.inl (c,Sum.inl (actualRadialStarEdge S j outer,⟨0,S.half_pos⟩))
def actualErrorEdge (S : OddScale) (j : Fin 2) (outer c : BDL26FiniteTannerSquare.Two) :
    DoubleCylinderEdge (AP S) (AX S j outer) S :=
  Sum.inl (c,(actualHubD S j outer).val)
theorem actualRadialStarEdge_value (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    (actualRadialStarEdge S j outer).val=
      Sum.inl ⟨(AX S j outer,AL S j outer 0),AL_incident S j outer 0⟩ := by
  apply congrArg Sum.inl
  apply Subtype.ext
  apply Prod.ext
  · change (AP S).faceX (ActualCriticalStarGeometry.fr S j outer)=AX S j outer
    exact ActualCriticalStarGeometry.faceFromShared_X (AP S) (AX S j outer)
      (AZ S j outer 0) (AL S j outer 0)
      (AL_incident S j outer 0) (AL_check S j outer 0)
  · change (AP S).faceQ (ActualCriticalStarGeometry.fr S j outer)
      (ActualCriticalStarGeometry.cr S j outer)=AL S j outer 0
    have hr : AL S j outer 0=ActualCriticalStarGeometry.r S j outer := by
      simp only [AL,if_pos rfl,if_true]
    exact (ActualCriticalStarGeometry.fr_leaf_corner S j outer).trans hr.symm
theorem actual_radial_incident_face (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two)
    (f : XStarFace (AP S) (AX S j outer)) :
    (AL S j outer 0=(AP S).faceQ f.val 0 ∨
      AL S j outer 0=(AP S).faceQ f.val 1) ↔ f=actualStarFace S j outer := by
  constructor
  · intro hf
    have hqz : (AP S).qz (AL S j outer 0) ((AP S).faceZ f.val)=true := by
      rcases hf with h | h
      · simpa only [h] using (AP S).data.faceQ_qz f.val 0
      · simpa only [h] using (AP S).data.faceQ_qz f.val 1
    have hz : (AP S).faceZ f.val=AZ S j outer 0 :=
      (ActualCriticalStarGeometry.leaf_unique S j outer).1.2 _ hqz
    apply Subtype.ext
    apply (AR S).faceXZ_injective
    apply Prod.ext
    · exact (show (AP S).faceX f.val=AX S j outer from by
        simpa only [xStarFaceMember,decide_eq_true_eq] using f.property).trans
        (show (AP S).faceX (actualStarFace S j outer).val=AX S j outer from by
          simpa only [xStarFaceMember,decide_eq_true_eq] using (actualStarFace S j outer).property).symm
    · exact hz.trans (ActualCriticalStarGeometry.faceFromShared_Z (AP S) (AX S j outer) (AZ S j outer 0) (AL S j outer 0) (AL_incident S j outer 0) (AL_check S j outer 0)).symm
  · intro hf
    subst f
    have hr : AL S j outer 0=ActualCriticalStarGeometry.r S j outer := by
      simp only [AL,if_pos rfl,if_true]
    have h : (AP S).faceQ (actualStarFace S j outer).val
        (ActualCriticalStarGeometry.cr S j outer)=AL S j outer 0 :=
      (ActualCriticalStarGeometry.fr_leaf_corner S j outer).trans hr.symm
    have hc := two_eq_zero_or_one
      (ActualCriticalStarGeometry.cr S j outer)
    rcases hc with hc | hc
    · exact Or.inl (by simpa only [hc] using h.symm)
    · exact Or.inr (by simpa only [hc] using h.symm)
theorem actual_radial_original_matrix (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two)
    (f : XStarFace (AP S) (AX S j outer)) :
    faceEdgeMatrix (AP S) (actualRadialStarEdge S j outer).val f.val=
      if f=actualStarFace S j outer then 1 else 0 := by
  rw [actualRadialStarEdge_value,radial_cellular_column]
  · exact indicator_iff _ _ (actual_radial_incident_face S j outer f)
  · simpa [xStarFaceMember] using f.property
theorem actual_hub_original_matrix (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two)
    (f : XStarFace (AP S) (AX S j outer)) :
    faceEdgeMatrix (AP S) (actualHubStarEdge S j outer).val f.val=
      if f=actualStarFace S j outer then 1 else 0 := by
  change faceEdgeMatrix (AP S)
    (Sum.inr ⟨(AH S j outer,AZ S j outer 0),AH_check S j outer 0⟩) f.val=_
  rw [QZ_cellular_column]
  have hiff : (AZ S j outer 0=(AP S).faceZ f.val ∧
      (AH S j outer=(AP S).faceQ f.val 0 ∨ AH S j outer=(AP S).faceQ f.val 1)) ↔
      f=actualStarFace S j outer := by
    constructor
    · intro h
      apply Subtype.ext
      apply (AR S).faceXZ_injective
      apply Prod.ext
      · exact (show (AP S).faceX f.val=AX S j outer from by
        simpa only [xStarFaceMember,decide_eq_true_eq] using f.property).trans
          (show (AP S).faceX (actualStarFace S j outer).val=AX S j outer from by
            simpa only [xStarFaceMember,decide_eq_true_eq] using (actualStarFace S j outer).property).symm
      · exact h.1.symm.trans (ActualCriticalStarGeometry.faceFromShared_Z (AP S) (AX S j outer) (AZ S j outer 0) (AL S j outer 0) (AL_incident S j outer 0) (AL_check S j outer 0)).symm
    · intro hf
      subst f
      refine ⟨(ActualCriticalStarGeometry.faceFromShared_Z (AP S) (AX S j outer) (AZ S j outer 0) (AL S j outer 0) (AL_incident S j outer 0) (AL_check S j outer 0)).symm,?_⟩
      have h : (AP S).faceQ (actualStarFace S j outer).val
          (ActualCriticalStarGeometry.opposite (ActualCriticalStarGeometry.cr S j outer))=
            AH S j outer := ActualCriticalStarGeometry.fr_hub_corner S j outer
      have hc := two_eq_zero_or_one
        (ActualCriticalStarGeometry.opposite (ActualCriticalStarGeometry.cr S j outer))
      rcases hc with hc | hc
      · exact Or.inl (by simpa only [hc] using h.symm)
      · exact Or.inr (by simpa only [hc] using h.symm)
  exact indicator_iff _ _ hiff
theorem nested_scalar_indicator (p q : Prop) [Decidable p] [Decidable q] :
    (if p then (if q then (1:BDL26Field) else 0) else 0)=
      (if p ∧ q then 1 else 0) := by
  by_cases hp : p <;> by_cases hq : q <;>
    simp only [hp,hq,if_true,if_false,true_and,false_and,and_true,and_false]
theorem copied_square_basis_value (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f f0 : XStarFace P x) (k : Fin S.half)
    (c d : BDL26FiniteTannerSquare.Two) :
    (canonicalBasisWord (F:=BDL26Field) (Sum.inl (c,f0,k,k)) :
      Word BDL26Field (DoubleCylinderFace P x S)) (Sum.inl (d,f,k,k))=
        (if c=d ∧ f=f0 then 1 else 0) := by
  let point : DoubleCylinderFace P x S := Sum.inl (d,f,k,k)
  let target : DoubleCylinderFace P x S := Sum.inl (c,f0,k,k)
  have hi : point=target ↔ c=d ∧ f=f0 := by
    constructor
    · intro h
      have hp : (d,f,k,k)=(c,f0,k,k) := Sum.inl.inj h
      exact ⟨(congrArg Prod.fst hp).symm,congrArg (fun z => z.2.1) hp⟩
    · rintro ⟨hc,hf⟩
      cases hc
      cases hf
      rfl
  by_cases hp : point=target
  · exact ((basis_value (I:=DoubleCylinderFace P x S) target point).trans (if_pos hp)).trans
      (if_pos (hi.mp hp)).symm
  · exact ((basis_value (I:=DoubleCylinderFace P x S) target point).trans (if_neg hp)).trans
      (if_neg (fun hq => hp (hi.mpr hq))).symm
theorem actualAlpha_boundary (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer c : BDL26FiniteTannerSquare.Two) :
    doubleCylinderCoboundary1 (AP S) (AX S j outer) S
      (canonicalBasisWord (actualAlphaEdge S j outer c))=
      canonicalBasisWord (Sum.inl (c,actualSmallFace S j outer)) := by
  funext face
  rw [doubleCylinder_basis_column]
  rcases face with ⟨d,f,i,k⟩ | rect
  · have hi : i=⟨0,S.half_pos⟩ := Fin.ext (by have h := i.isLt;omega)
    have hk : k=⟨0,S.half_pos⟩ := Fin.ext (by have h := k.isLt;omega)
    subst i
    subst k
    change (if c=d then subdivisionFaceEdgeMatrix (AP S) (AX S j outer) S
      (Sum.inl (actualRadialStarEdge S j outer,⟨0,S.half_pos⟩))
      (f,⟨0,S.half_pos⟩,⟨0,S.half_pos⟩) else 0)=_
    rw [halfOne_subdivision_original_column _ _ _ hh,actual_radial_original_matrix]
    exact (nested_scalar_indicator (c=d) (f=actualStarFace S j outer)).trans
      (copied_square_basis_value (AP S) (AX S j outer) S f (actualStarFace S j outer)
        ⟨0,S.half_pos⟩ c d).symm
  · have hne : (Sum.inl (actualRadialStarEdge S j outer,⟨0,S.half_pos⟩) :
        SubdivisionEdge (AP S) (AX S j outer) S)≠rect.val := by
      intro he
      have hr := rect.property
      rw [← he] at hr
      change xStarBoundaryEdgeMember (AP S) (AX S j outer)
        (actualRadialStarEdge S j outer).val=true at hr
      rw [actualRadialStarEdge_value] at hr
      change false=true at hr
      cases hr
    change (if (Sum.inl (actualRadialStarEdge S j outer,⟨0,S.half_pos⟩) :
        SubdivisionEdge (AP S) (AX S j outer) S)=rect.val then (1:BDL26Field) else 0)=_
    have hz : (canonicalBasisWord (F:=BDL26Field) (Sum.inl (c,actualSmallFace S j outer)) :
        Word BDL26Field (DoubleCylinderFace (AP S) (AX S j outer) S)) (Sum.inr rect)=0 :=
      (basis_value (I:=DoubleCylinderFace (AP S) (AX S j outer) S)
        (Sum.inl (c,actualSmallFace S j outer)) (Sum.inr rect)).trans
          (if_neg (by intro h;cases h))
    exact (if_neg hne).trans hz.symm
theorem actualError_boundary (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer c : BDL26FiniteTannerSquare.Two) :
    doubleCylinderCoboundary1 (AP S) (AX S j outer) S
      (canonicalBasisWord (actualErrorEdge S j outer c))=
      canonicalBasisWord (Sum.inl (c,actualSmallFace S j outer))+
        canonicalBasisWord (Sum.inr (actualHubD S j outer)) := by
  funext face
  rw [doubleCylinder_basis_column]
  rcases face with ⟨d,f,i,k⟩ | rect
  · have hi : i=⟨0,S.half_pos⟩ := Fin.ext (by have h := i.isLt;omega)
    have hk : k=⟨0,S.half_pos⟩ := Fin.ext (by have h := k.isLt;omega)
    subst i
    subst k
    change (if c=d then subdivisionFaceEdgeMatrix (AP S) (AX S j outer) S
      (Sum.inl (actualHubStarEdge S j outer,⟨0,S.half_pos⟩))
      (f,⟨0,S.half_pos⟩,⟨0,S.half_pos⟩) else 0)=_
    rw [halfOne_subdivision_original_column _ _ _ hh,actual_hub_original_matrix]
    have hs := copied_square_basis_value (AP S) (AX S j outer) S f
      (actualStarFace S j outer) ⟨0,S.half_pos⟩ c d
    have hz : (canonicalBasisWord (F:=BDL26Field) (Sum.inr (actualHubD S j outer)) :
        Word BDL26Field (DoubleCylinderFace (AP S) (AX S j outer) S))
        (Sum.inl (d,f,⟨0,S.half_pos⟩,⟨0,S.half_pos⟩))=0 :=
      (basis_value (I:=DoubleCylinderFace (AP S) (AX S j outer) S)
        (Sum.inr (actualHubD S j outer))
        (Sum.inl (d,f,⟨0,S.half_pos⟩,⟨0,S.half_pos⟩))).trans
          (if_neg (by intro h;cases h))
    exact (nested_scalar_indicator (c=d) (f=actualStarFace S j outer)).trans
      ((congrArg₂ (fun a b : BDL26Field => a+b) hs hz).trans (add_zero _)).symm
  · change (if (actualHubD S j outer).val=rect.val then (1:BDL26Field) else 0)=_
    have hs : (canonicalBasisWord (F:=BDL26Field) (Sum.inl (c,actualSmallFace S j outer)) :
        Word BDL26Field (DoubleCylinderFace (AP S) (AX S j outer) S)) (Sum.inr rect)=0 :=
      (basis_value (I:=DoubleCylinderFace (AP S) (AX S j outer) S)
        (Sum.inl (c,actualSmallFace S j outer)) (Sum.inr rect)).trans
          (if_neg (by intro h;cases h))
    have he : (Sum.inr rect : DoubleCylinderFace (AP S) (AX S j outer) S)=
        Sum.inr (actualHubD S j outer) ↔ (actualHubD S j outer).val=rect.val := by
      constructor
      · intro h
        exact (congrArg Subtype.val (Sum.inr.inj h)).symm
      · intro h
        exact congrArg Sum.inr (Subtype.ext h.symm)
    have hr : (canonicalBasisWord (F:=BDL26Field) (Sum.inr (actualHubD S j outer)) :
        Word BDL26Field (DoubleCylinderFace (AP S) (AX S j outer) S)) (Sum.inr rect)=
          (if (actualHubD S j outer).val=rect.val then (1:BDL26Field) else 0) := by
      by_cases hp : (Sum.inr rect : DoubleCylinderFace (AP S) (AX S j outer) S)=
          Sum.inr (actualHubD S j outer)
      · exact ((basis_value (I:=DoubleCylinderFace (AP S) (AX S j outer) S)
          (Sum.inr (actualHubD S j outer)) (Sum.inr rect)).trans (if_pos hp)).trans
            (if_pos (he.mp hp)).symm
      · exact ((basis_value (I:=DoubleCylinderFace (AP S) (AX S j outer) S)
          (Sum.inr (actualHubD S j outer)) (Sum.inr rect)).trans (if_neg hp)).trans
            (if_neg (fun hq => hp (he.mpr hq))).symm
    exact ((congrArg₂ (fun a b : BDL26Field => a+b) hs hr).trans (zero_add _)).symm
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
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
theorem pureXInput_raw_query (x : P.X)
    (f : Word BDL26Field (DoubleCylinderEdge P x S)) :
    (wordEquiv (xSyndromeEquiv P S x)).symm
      (restrictWordLinear ((LX).syndromeRegion x) (pureXInput P A R S x f).val)=
      doubleCylinderCoboundary1 P x S f := by
  have hd : restrictWordLinear ((LX).syndromeRegion x) (pureXInput P A R S x f).val=
      (G).contract.rx_local_complexes.cxDelta1 x (wordEquiv (xCorrectionEquiv P S x) f) := by
    change restrictWordLinear ((LX).syndromeRegion x)
      ((CF).coboundary1 U (directXExtension P A R S x f))=_
    erw [(G).contract.support_decomposition.cxDelta1_restriction_global,
      directXExtension_restrict_same]
    all_goals rfl
  rw [hd]
  funext face
  change (G).contract.rx_local_complexes.cxDelta1 x
    (wordEquiv (xCorrectionEquiv P S x) f) (xSyndromeEquiv P S x face)=_
  erw [localCx_delta1_apply,LinearEquiv.symm_apply_apply]
  rfl
end
def fixedDInput (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : ASyndrome S :=
  pureXInput (AP S) (AA S) (AR S) S (AX S j outer)
    (canonicalBasisWord (actualAlphaEdge S j outer 0)+
     canonicalBasisWord (actualErrorEdge S j outer 0))
theorem fixedDInput_raw_query (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    (wordEquiv (xSyndromeEquiv (AP S) S (AX S j outer))).symm
      (restrictWordLinear ((literalLx (AP S) (AA S) (AR S) S).syndromeRegion
        (AX S j outer)) (fixedDInput S j outer).val)=
      canonicalBasisWord (Sum.inr (actualHubD S j outer)) := by
  have h := pureXInput_raw_query (AP S) (AA S) (AR S) S (AX S j outer)
    (canonicalBasisWord (actualAlphaEdge S j outer 0)+
      canonicalBasisWord (actualErrorEdge S j outer 0))
  have hd := (map_add (doubleCylinderCoboundary1 (AP S) (AX S j outer) S)
    (canonicalBasisWord (actualAlphaEdge S j outer 0))
    (canonicalBasisWord (actualErrorEdge S j outer 0))).trans
      (congrArg₂ (fun a b : Word BDL26Field (DoubleCylinderFace (AP S) (AX S j outer) S) => a+b)
        (actualAlpha_boundary S hh j outer 0) (actualError_boundary S hh j outer 0))
  refine h.trans (hd.trans ?_)
  funext face
  let a : BDL26Field := canonicalBasisWord (Sum.inl (0,actualSmallFace S j outer)) face
  let d : BDL26Field := canonicalBasisWord (Sum.inr (actualHubD S j outer)) face
  change a+(a+d)=d
  rw [← add_assoc,repair3_scalar_add_self,zero_add]
noncomputable def chosenHubCopy (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : BDL26FiniteTannerSquare.Two :=
  Classical.choose (actual_D_original_exit S hh j outer (fixedDInput S j outer)
    (fixedDInput_raw_query S hh j outer))
def oppositeErrorCopy (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : BDL26FiniteTannerSquare.Two :=
  ActualCriticalStarGeometry.opposite (chosenHubCopy S hh j outer)
def directHubW (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    Word BDL26Field (QDoubleCylinderVertex (AP S) (AH S j outer) S) :=
  CriticalOriginalChoice.coneWord (AP S) (AH S j outer) S 0+
    CriticalOriginalChoice.terminalWord (AP S) (AH S j outer) S 0 (AHZ S j outer 2)+
    CriticalOriginalChoice.terminalWord (AP S) (AH S j outer) S 1 (AHZ S j outer 2)
def counterexampleInput (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : ASyndrome S :=
  directInput (AP S) (AA S) (AR S) S (AX S j outer) (AH S j outer)
    (canonicalBasisWord (actualAlphaEdge S j outer (oppositeErrorCopy S hh j outer)))
    (directHubW S j outer)
def counterexamplePhysicalEdge (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : DoubleCylinderEdge (AP S) (AX S j outer) S :=
  actualErrorEdge S j outer (oppositeErrorCopy S hh j outer)
def counterexamplePhysical (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : BDL26CSSHamiltonian.Physical S 3 :=
  BDL26RXPhysicalCoordinateTrace.oldXPhysical S 1 (by decide)
    (seedQNode S j) outer (counterexamplePhysicalEdge S hh j outer)
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
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
noncomputable def originalCqWord (sigma : (CF).Syndrome U) (q : P.Q) :
    Word BDL26Field (QDoubleCylinderVertex P q S) :=
  (wordEquiv (qCorrectionEquiv P S q)).symm
    (restrictWordLinear ((LQ).correctionRegion q) (cqComponentTotal G sigma.val q))
end
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RXDecoderAdapter BDL26DecodingGraph
open scoped Classical BigOperators
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
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
def rawQRead (q : P.Q) : (CF).Cochain2 U →ₗ[BDL26Field]
    Word BDL26Field (QDoubleCylinderEdge P q S) :=
  ((wordEquiv (qSyndromeEquiv P S q)).symm).toLinearMap.comp
    (restrictWordLinear ((LQ).syndromeRegion q))
end
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open scoped Classical BigOperators
namespace CriticalOriginalChoice
open BDL26RXLocalReplacement BDL26TannerLocalRegularity BDL26RXDecoderAdapter
end CriticalOriginalChoice
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
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
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RXDecoderAdapter BDL26DecodingGraph
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
def directHubK (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    Word BDL26Field (QDoubleCylinderVertex (AP S) (AH S j outer) S) :=
  CriticalOriginalChoice.terminalWord (AP S) (AH S j outer) S 0 (AHZ S j outer 0)+
    CriticalOriginalChoice.terminalWord (AP S) (AH S j outer) S 1 (AHZ S j outer 0)
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open BDL26IndexedDecoder BDL26ActualFailureReadout BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping
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
def counterexampleActualTop (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : repair2C3Input S :=
  repair5_literal_to_actual S (counterexampleInput S hh j outer)
def counterexampleDomain (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : BDL26TransposedStoppedDecoder.XSyndromeDomain S 1 :=
  ⟨(counterexampleActualTop S hh j outer).val,by
    obtain ⟨e,he⟩ := (counterexampleActualTop S hh j outer).property
    exact ⟨e,(LinearMap.congr_fun
      (indexedFamily_coboundary1 S 3 (3 : LevelIndex 3)) e).symm.trans he⟩⟩
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26RXDecoderAdapter
open BDL26RXErrorPullback BDL26RXXStarTransport
open scoped Classical BigOperators
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26RXDecoderAdapter
open BDL26DecodingGraph BDL26LocalizedHistoryErrorDescent BDL26ActualFailureReadout
open BDL26RXErrorPullback BDL26RXXStarTransport
open scoped Classical BigOperators
abbrev counterSigma (S : OddScale) (hh : S.half=1) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :=
  repair2C3InputOfSyndrome S (counterexampleDomain S hh j outer)
abbrev counterTau (S : OddScale) (hh : S.half=1) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :=
  repair2C3PerturbTop S (counterSigma S hh j outer)
    (repair2C3Flip S (counterexamplePhysical S hh j outer))
def counterTop (S : OddScale) (hh : S.half=1) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    LocalizedWord S 1 (counterSigma S hh j outer) (counterTau S hh j outer)
      (Fin.succ (0 : StepIndex 1)) :=
  initial S 1 (counterSigma S hh j outer)
    (repair2C3Flip S (counterexamplePhysical S hh j outer))
    (elementaryCenter S 1 (counterexamplePhysical S hh j outer))
    (OriginalOneStepPhiBridge.original_flip_supported S 1 (counterexamplePhysical S hh j outer))
abbrev counterA (S : OddScale) (hh : S.half=1) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    Upper S 3 (2 : StepIndex 3) :=
  BDL26LocalizedHistoryErrorDescent.first S 1 (counterSigma S hh j outer) (0 : StepIndex 1)
abbrev counterB (S : OddScale) (hh : S.half=1) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    Upper S 3 (2 : StepIndex 3) :=
  BDL26LocalizedHistoryErrorDescent.second S 1 (counterSigma S hh j outer)
    (counterTau S hh j outer) (0 : StepIndex 1) (counterTop S hh j outer)
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26RXDecoderAdapter
open BDL26DecodingGraph BDL26LocalizedHistoryErrorDescent BDL26ActualFailureReadout
open BDL26RXErrorPullback BDL26RXXStarTransport
open scoped Classical BigOperators
def counterX0 (S : OddScale) (hh : S.half=1) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    Finset (AP S).X :=
  {BDL26RXPhysicalStarTransport.parentX S 3 (2 : StepIndex 3) (by decide)
    (counterTop S hh j outer).center}
def counterVeff (S : OddScale) (hh : S.half=1) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    LocalPotential S (2 : StepIndex 3) (AX S j outer) :=
  if AX S j outer∈counterX0 S hh j outer then
    localPotential S 3 (2 : StepIndex 3) (by decide) (AX S j outer)
      (counterA S hh j outer) (counterB S hh j outer) else 0
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26RXDecoderAdapter
open BDL26DecodingGraph BDL26LocalizedHistoryErrorDescent BDL26ActualFailureReadout
open BDL26RXErrorPullback BDL26RXXStarTransport BDL26TannerLocalRegularity
open MultiscaleDecoder.RXCoarseGraining MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26RXDecoderAdapter
open BDL26DecodingGraph BDL26RXLocalReplacement BDL26TannerLocalRegularity
open MultiscaleDecoder.RXCoarseGraining MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
def counterHubPotential (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : Word BDL26Field (QDoubleCylinderVertex (AP S) (AH S j outer) S) :=
  rxXQDegreeZero (AP S) (AA S).toTannerSquareAdmissible (AH S j outer)
    (AX S j outer) (AH_incident S j outer) S (counterVeff S hh j outer)
def counterBeta (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : BDL26Field :=
  counterHubPotential S hh j outer (0,.inl (.inl ()))
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26RXDecoderAdapter
open BDL26DecodingGraph BDL26RXLocalReplacement BDL26TannerLocalRegularity
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26ReplacementCochainMaps
open scoped Classical BigOperators
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26RXDecoderAdapter
open BDL26DecodingGraph BDL26LocalizedHistoryErrorDescent BDL26ActualFailureReadout
open BDL26RXLocalReplacement BDL26TannerLocalRegularity
open scoped Classical BigOperators
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26RXLocalReplacement BDL26TannerLocalRegularity
open MultiscaleDecoder.RXCoarseGraining MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
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
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26RXDecoderAdapter
open BDL26DecodingGraph BDL26LocalizedHistoryErrorDescent BDL26ActualFailureReadout
open BDL26RXErrorPullback BDL26RXLocalReplacement BDL26TannerLocalRegularity
open MultiscaleDecoder.RXCoarseGraining MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26DecodingGraph
open BDL26ActualFailureReadout BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
end OriginalCounterexampleWorking


