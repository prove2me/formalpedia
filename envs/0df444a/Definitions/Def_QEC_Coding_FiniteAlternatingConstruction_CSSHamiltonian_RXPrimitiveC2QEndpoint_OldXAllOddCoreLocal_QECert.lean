-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_OldXAllOddCoreLocal_QECert
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_OldXAllOddCoreLocal_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T21:14:57.258264+00:00
-- url     : https://prove2.me/theorems/fdffb217-bffd-4717-8a70-170713af3edb
-- title:
--   All-odd OldX local readout core
-- statement:
--   Exact local geometry and readout lemmas for the all-odd OldX proof.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L18360-L18373

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_OldXAllOddCoreBase_QECert
import Theorems.Thm_QEC_Coding_BDL26GlobalLookupLinearity_executableLinear_actual
import Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzOldX_incidence_iff
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_graphBoundary_pathChain
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
theorem actualGlobal_zero_of_encoded_kernel_OldXBounded_QECert (S : OddScale)
    (a k : Word F (levelTwoPresentation S).Q) (q : (levelTwoPresentation S).Q)
    (hk : tannerCoboundary1 (levelTwoPresentation S) k=0) (hq : k q=1)
    (hp : ∀ p, Encodable.encode (executableCoordinate S p)<
      Encodable.encode (executableCoordinate S q) → k p=0) :
    BDL26GlobalLookupLinearity.actualGlobal S
      (tannerCoboundary1 (levelTwoPresentation S) a) q=0 := by
  have hkernel : BDL26GlobalLookupLinearity.executableLinear S
      (BDL26LevelTwoDecoder.toExecutableError S k)=0 := by
    rw [BDL26GlobalLookupLinearity.executableLinear_actual,hk]
    rfl
  have hpoint : BDL26LevelTwoDecoder.toExecutableError S k (executableCoordinate S q)=1 := by
    simpa [BDL26LevelTwoDecoder.toExecutableError,executableCoordinate] using hq
  have hprefix (p : BDL26LevelTwoDecoder.ExecutableQ S)
      (h : Encodable.encode p<Encodable.encode (executableCoordinate S q)) :
      BDL26LevelTwoDecoder.toExecutableError S k p=0 := by
    apply hp (cast (BDL26LevelTwoDecoder.executableQ_eq S) p)
    simpa [executableCoordinate] using h
  have h := global_zero_of_encoded_kernel_OldXBounded_QECert
    (BDL26GlobalLookupLinearity.executableLinear S)
    (BDL26LevelTwoDecoder.toExecutableError S a) (executableCoordinate S q)
    (BDL26LevelTwoDecoder.toExecutableError S k) hkernel hprefix hpoint
  change BDL26GlobalLookupLinearity.executableGlobal S
    (BDL26LevelTwoDecoder.toExecutableSyndrome S
      (tannerCoboundary1 (levelTwoPresentation S) a)) (executableCoordinate S q)=0
  rw [← BDL26GlobalLookupLinearity.executableLinear_actual S a]
  exact h
private theorem actualGlobal_zero_of_first_actual_star_coordinate (S : OddScale)
    (a : Word F (levelTwoPresentation S).Q) (x : (levelTwoPresentation S).X)
    (q : (levelTwoPresentation S).Q) (hxq : (levelTwoPresentation S).xq x q=true)
    (hfirst : ∀ p, (levelTwoPresentation S).xq x p=true → p≠q →
      Encodable.encode (executableCoordinate S q)<Encodable.encode (executableCoordinate S p)) :
    BDL26GlobalLookupLinearity.actualGlobal S
      (tannerCoboundary1 (levelTwoPresentation S) a) q=0 := by
  let k := tannerCoboundary0 (levelTwoPresentation S) (canonicalBasisWord (F:=F) x)
  apply actualGlobal_zero_of_encoded_kernel_OldXBounded_QECert S a k q
  · have h := LinearMap.congr_fun
      (BDL26LevelTwoDistance.tannerCoboundary_squared (levelTwoPresentation S))
        (canonicalBasisWord (F:=F) x)
    simpa only [LinearMap.comp_apply,LinearMap.zero_apply,k] using h
  · dsimp only [k]
    rw [tannerCoboundary0_canonicalBasis_apply,if_pos hxq]
  · intro p hlt
    dsimp only [k]
    rw [tannerCoboundary0_canonicalBasis_apply]
    apply if_neg
    intro hxp
    by_cases he : p=q
    · subst p
      exact (Nat.lt_irrefl _ hlt)
    · have hgt := hfirst p hxp he
      exact (Nat.lt_asymm hlt hgt)
private theorem xq_heq {U V : TannerSquarePresentation} (h : U=V) :
    HEq U.xq V.xq := by cases h; rfl
private theorem actual_raw_xq (S : OddScale) :
    ((levelTwoPresentation S).xq : (RawTwo S).X → (RawTwo S).Q → Bool)=
      (RawTwo S).xq :=
  eq_of_heq (xq_heq (congrArg ConstructionState.presentation (levelTwoState_eq_pair S)))
private theorem actualGlobal_zero_of_first_star_coordinate (S : OddScale)
    (a : Word F (levelTwoPresentation S).Q) (x : (RawTwo S).X)
    (q : (RawTwo S).Q) (hxq : (RawTwo S).xq x q=true)
    (hfirst : ∀ p, (RawTwo S).xq x p=true → p≠q →
      Encodable.encode (executableCoordinate S q)<Encodable.encode (executableCoordinate S p)) :
    BDL26GlobalLookupLinearity.actualGlobal S
      (tannerCoboundary1 (levelTwoPresentation S) a) q=0 := by
  apply actualGlobal_zero_of_first_actual_star_coordinate S a x q
  · exact (congrFun (congrFun (actual_raw_xq S) x) q).trans hxq
  · intro p hp hn
    exact hfirst p ((congrFun (congrFun (actual_raw_xq S) x) p).symm.trans hp) hn
private theorem encoded_endpoint_lt (S : OddScale) (r r' : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (hx' : (RawOne S).xq x r'=true) (c : BDL26FiniteTannerSquare.Two)
    (hlt : Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)<
      Encodable.encode (r' : (BDL26LevelTwoDecoder.executableLevelOne S).Q)) :
    Encodable.encode (executableCoordinate S (Sum.inr ⟨r,(c,Sum.inl (Sum.inr ⟨x,hx⟩))⟩))<
      Encodable.encode (executableCoordinate S (Sum.inr ⟨r',(c,Sum.inl (Sum.inr ⟨x,hx'⟩))⟩)) := by
  have hpair := Nat.pair_lt_pair_left
    (Nat.pair c.val
      (2*(2*Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)+1))) hlt
  have hnumber :
      2*Nat.pair (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
        (Nat.pair c.val (2*(2*Encodable.encode
          (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)+1)))+1 <
      2*Nat.pair (Encodable.encode (r' : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
        (Nat.pair c.val (2*(2*Encodable.encode
          (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)+1)))+1 := by omega
  exact (encoded_endpoint_OldXCore_QECert S r x hx c).trans_lt
    (hnumber.trans_eq (encoded_endpoint_OldXCore_QECert S r' x hx' c).symm)
theorem global_endpoint_of_least_old_neighbor_OldXCore_QECert (S : OddScale)
    (a : Word F (levelTwoPresentation S).Q) (r : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (c : BDL26FiniteTannerSquare.Two)
    (hmin : ∀ r' : (RawOne S).Q, (RawOne S).xq x r'=true → r'≠r →
      Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)<
        Encodable.encode (r' : (BDL26LevelTwoDecoder.executableLevelOne S).Q)) :
    BDL26GlobalLookupLinearity.actualGlobal S
      (tannerCoboundary1 (levelTwoPresentation S) a)
      (.inr ⟨r,(c,.inl (.inr ⟨x,hx⟩))⟩)=0 := by
  apply actualGlobal_zero_of_first_star_coordinate S a (.inr (x,c))
    (.inr ⟨r,(c,.inl (.inr ⟨x,hx⟩))⟩)
  · exact (BDL26ReplacementCochainMaps.rzOldX_incidence_iff (RawOne S)
      (rxState S baseState).admissible.toTannerSquareAdmissible S x c
      (Sum.inr ⟨r,(c,Sum.inl (Sum.inr ⟨x,hx⟩))⟩)).mpr ⟨r,hx,rfl⟩
  · intro p hi hn
    change rzXQIncidence (RawOne S)
      (rxState S baseState).admissible.toTannerSquareAdmissible S (.inr (x,c)) p=true at hi
    obtain ⟨r',hx',hp⟩ :=
      (BDL26ReplacementCochainMaps.rzOldX_incidence_iff _ _ _ _ _ _).mp hi
    have hne : r'≠r := by
      intro he
      subst r'
      exact hn hp
    have hlt := encoded_endpoint_lt S r r' x hx hx' c (hmin r' hx' hne)
    have hcoordinate := congrArg (fun p : (RawTwo S).Q =>
      Encodable.encode (executableCoordinate S p)) hp
    exact hlt.trans_eq hcoordinate.symm
theorem global_first_radial_endpoint_zero_OldXCore_QECert (S : OddScale)
    (a : Word F (levelTwoPresentation S).Q) (x : (RawOne S).X)
    (hx : (RawOne S).xq x
      (.inl ⟨(0 : BaseX),.inl (0,.inl (seedRadial 0,⟨0,S.half_pos⟩))⟩)=true)
    (c : BDL26FiniteTannerSquare.Two) :
    BDL26GlobalLookupLinearity.actualGlobal S
      (tannerCoboundary1 (levelTwoPresentation S) a)
      (.inr ⟨.inl ⟨(0 : BaseX),.inl (0,.inl (seedRadial 0,⟨0,S.half_pos⟩))⟩,
        (c,.inl (.inr ⟨x,hx⟩))⟩)=0 := by
  apply global_endpoint_of_least_old_neighbor_OldXCore_QECert S a (firstRadialQ S) x hx c
  intro r' hx' hn
  have hz : Encodable.encode
      (firstRadialQ S : (BDL26LevelTwoDecoder.executableLevelOne S).Q)=0 := by rfl
  have hne : Encodable.encode
      (r' : (BDL26LevelTwoDecoder.executableLevelOne S).Q)≠0 := by
    intro he
    apply hn
    exact Encodable.encode_injective (he.trans hz.symm)
  omega
private theorem lastQEdge_start (S : OddScale) (h : 2≤S.half)
    (r : (RawOne S).Q) (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (c : BDL26FiniteTannerSquare.Two) :
    qDoubleCylinderEdgeStart (transposePresentation (RawOne S)) r S
      (lastQEdge S r x hx c)=(c,.inr (⟨x,hx⟩,lastInterior S h)) := by
  change (c,if hn : S.half-1=0 then _ else _)=_
  rw [dif_neg (by omega)]
  congr 2 <;> (apply Fin.ext; dsimp [lastInterior]; omega)
private theorem lastQEdge_end (S : OddScale) (r : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (c : BDL26FiniteTannerSquare.Two) :
    qDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) r S
      (lastQEdge S r x hx c)=(c,.inl (.inr ⟨x,hx⟩)) := by
  have hlast : S.half-1+1=S.half := by have := S.half_pos; omega
  simp [lastQEdge,qDoubleCylinderEdgeEnd,qSubdivisionEdgeEnd,hlast,qStarEdgeEnd]
private theorem shiftedOldXBoundary_eq (S : OddScale) (h : 2≤S.half)
    (x : (RawOne S).X) (c : BDL26FiniteTannerSquare.Two) :
    tannerCoboundary0 (RawTwo S) (shiftedOldXPotential S x c)=
      ∑ r : (RawOne S).Q, if hx : (RawOne S).xq x r=true then
        canonicalBasisWord (F:=F) (.inr ⟨r,(c,.inr (⟨x,hx⟩,lastInterior S h))⟩) +
          ∑ z : (RawOne S).Z, if hz : (RawOne S).qz r z=true then
            canonicalBasisWord (F:=F) (.inl ⟨z,qToZDoubleCylinderEdge (RawOne S)
              (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S
              (lastQEdge S r x hx c)⟩) else 0
      else 0 := by
  apply mapped_shifted_sum_cancel_OldXBounded_QECert (tannerCoboundary0 (RawTwo S))
    (canonicalBasisWord (F:=F) (.inr (x,c)))
    (fun r : (RawOne S).Q => (RawOne S).xq x r=true)
    (fun r hx => canonicalBasisWord (F:=F) (.inl (.inr ⟨r,lastQEdge S r x hx c⟩)))
    (fun r hx => canonicalBasisWord (F:=F) (.inr ⟨r,(c,.inl (.inr ⟨x,hx⟩))⟩))
    (fun r hx => canonicalBasisWord (F:=F) (.inr ⟨r,(c,.inr (⟨x,hx⟩,lastInterior S h))⟩))
    (fun r hx => ∑ z : (RawOne S).Z, if hz : (RawOne S).qz r z=true then
      canonicalBasisWord (F:=F) (.inl ⟨z,qToZDoubleCylinderEdge (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S
        (lastQEdge S r x hx c)⟩) else 0)
  · exact BDL26ReplacementCochainMaps.rzOldX_delta0 (RawOne S)
      (rxState S baseState).admissible S x c
  · intro r hx
    have hedge := rzMap1QEdge_delta0_canonicalBasis (RawOne S)
      (rxState S baseState).admissible S r (lastQEdge S r x hx c)
    change tannerCoboundary0 (RawTwo S)
      (canonicalBasisWord (F:=F) (.inl (.inr ⟨r,lastQEdge S r x hx c⟩)))=_ at hedge
    apply hedge.trans
    dsimp only [rzMap1QEdgeDelta0BasisImage]
    erw [lastQEdge_start S h r x hx c,lastQEdge_end S r x hx c]
    all_goals rfl
theorem global_last_interior_of_least_old_neighbor_OldXCore_QECert (S : OddScale)
    (h : 2≤S.half) (a : Word F (levelTwoPresentation S).Q) (r : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (c : BDL26FiniteTannerSquare.Two)
    (hmin : ∀ r' : (RawOne S).Q, (RawOne S).xq x r'=true → r'≠r →
      Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)<
        Encodable.encode (r' : (BDL26LevelTwoDecoder.executableLevelOne S).Q)) :
    BDL26GlobalLookupLinearity.actualGlobal S
      (tannerCoboundary1 (levelTwoPresentation S) a)
      (.inr ⟨r,(c,.inr (⟨x,hx⟩,lastInterior S h))⟩)=0 := by
  let k := tannerCoboundary0 (RawTwo S) (shiftedOldXPotential S x c)
  have hrle (r' : (RawOne S).Q) (hx' : (RawOne S).xq x r'=true) :
      Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)≤
        Encodable.encode (r' : (BDL26LevelTwoDecoder.executableLevelOne S).Q) := by
    by_cases he : r'=r
    · subst r'; exact le_rfl
    · exact (hmin r' hx' he).le
  apply actualGlobal_zero_of_encoded_kernel_OldXBounded_QECert S a k
    (.inr ⟨r,(c,.inr (⟨x,hx⟩,lastInterior S h))⟩)
  · have hs := LinearMap.congr_fun
      (BDL26LevelTwoDistance.tannerCoboundary_squared (RawTwo S))
        (shiftedOldXPotential S x c)
    change tannerCoboundary1 (RawTwo S) k=0
    change tannerCoboundary1 (RawTwo S)
      (tannerCoboundary0 (RawTwo S) (shiftedOldXPotential S x c))=0 at hs
    exact hs
  · have hvalue := congrFun (shiftedOldXBoundary_eq S h x c)
      (.inr ⟨r,(c,.inr (⟨x,hx⟩,lastInterior S h))⟩)
    apply hvalue.trans
    erw [conditional_word_sum_apply_OldXBounded_QECert,Finset.sum_eq_single r]
    · erw [dif_pos hx]
      have hlocal := disjoint_conditional_basis_apply_OldXBounded_QECert
        (fun z : (RawOne S).Z => (RawOne S).qz r z=true)
        (fun z hz => (.inl ⟨z,qToZDoubleCylinderEdge (RawOne S)
          (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S
          (lastQEdge S r x hx c)⟩ : (RawTwo S).Q))
        (.inr ⟨r,(c,.inr (⟨x,hx⟩,lastInterior S h))⟩)
        (by intro z hz he; cases he)
      exact (generic_basis_plus_value_OldXBounded_QECert _ _ _ hlocal).trans (if_pos rfl)
    · intro r' _ hn
      by_cases hx' : (RawOne S).xq x r'=true
      · erw [dif_pos hx']
        have hlocal := disjoint_conditional_basis_apply_OldXBounded_QECert
          (fun z : (RawOne S).Z => (RawOne S).qz r' z=true)
          (fun z hz => (.inl ⟨z,qToZDoubleCylinderEdge (RawOne S)
            (rxState S baseState).admissible.toTannerSquareAdmissible r' z hz S
            (lastQEdge S r' x hx' c)⟩ : (RawTwo S).Q))
          (.inr ⟨r,(c,.inr (⟨x,hx⟩,lastInterior S h))⟩)
          (by intro z hz he; cases he)
        have hne : (Sum.inr ⟨r,(c,Sum.inr (⟨x,hx⟩,lastInterior S h))⟩ : (RawTwo S).Q)≠
            Sum.inr ⟨r',(c,Sum.inr (⟨x,hx'⟩,lastInterior S h))⟩ := by
          intro he
          exact hn (congrArg Sigma.fst (Sum.inr.inj he)).symm
        exact (generic_basis_plus_value_OldXBounded_QECert _ _ _ hlocal).trans (if_neg hne)
      · simp only [dif_neg hx',word_zero_eval]
    · intro hn
      exact False.elim (hn (Finset.mem_univ r))
  · intro p hprefix
    have hvalue := congrFun (shiftedOldXBoundary_eq S h x c) p
    apply hvalue.trans
    erw [conditional_word_sum_apply_OldXBounded_QECert]
    apply Finset.sum_eq_zero
    intro r' _
    by_cases hx' : (RawOne S).xq x r'=true
    · erw [dif_pos hx']
      have hQ : p≠(.inr ⟨r',(c,.inr (⟨x,hx'⟩,lastInterior S h))⟩ : (RawTwo S).Q) := by
        intro he
        have hcode := congrArg (fun q : (RawTwo S).Q =>
          Encodable.encode (executableCoordinate S q)) he
        have hbefore := hcode.symm.trans_lt hprefix
        by_cases hrr : r'=r
        · subst r'
          exact Nat.lt_irrefl _ hbefore
        · exact Nat.lt_asymm hbefore
            (encoded_interior_lt_OldXBounded_QECert S r r' x hx hx' c (lastInterior S h) (hmin r' hx' hrr))
      have hlocal := disjoint_conditional_basis_apply_OldXBounded_QECert
        (fun z : (RawOne S).Z => (RawOne S).qz r' z=true)
        (fun z hz => (.inl ⟨z,qToZDoubleCylinderEdge (RawOne S)
          (rxState S baseState).admissible.toTannerSquareAdmissible r' z hz S
          (lastQEdge S r' x hx' c)⟩ : (RawTwo S).Q)) p (by
          intro z hz he
          have hcode := congrArg (fun q : (RawTwo S).Q =>
            Encodable.encode (executableCoordinate S q)) he
          have hlate := encoded_interior_before_radial_OldXBounded_QECert S r r' x hx hx' z hz c
            (lastInterior S h) (lastSegment S) (hrle r' hx') (by
              dsimp [lastInterior,lastSegment]
              omega)
          exact Nat.lt_asymm (hcode.symm.trans_lt hprefix) hlate)
      exact (generic_basis_plus_value_OldXBounded_QECert _ _ _ hlocal).trans (if_neg hQ)
    · simp only [dif_neg hx',word_zero_eval]
theorem shiftedFacePath0_support_OldXCore_QECert (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (i : Fin (S.half-1))
    (e : SubdivisionEdge P x S) (he : pathChain (shiftedFacePath0 P x S f i) e≠0) :
    (∃ k : Fin S.half, k.val≤ i.val ∧
      e=.inr (.inr (f,lastInterior S (by have := i.isLt; omega),k))) ∨
      e=.inr (.inl (f,lastSegment S,i)) := by
  have hh : 2≤S.half := by have := i.isLt; omega
  have hc0 : S.half-1≠0 := by omega
  have hch : S.half-1≠S.half := by omega
  have ht0 : i.val+1≠0 := by omega
  have hth : i.val+1≠S.half := by have := i.isLt; omega
  have hs : pathChain (shiftedFacePath0 P x S f i)=
      pathChain (verticalAtColumnPath P x S f (lastGridInterior S) (i.val+1)
        (by have := i.isLt; omega))+
      Pi.single (subdivisionHorizontalEdge P x S f (lastSegment S)
        (gridAt S (i.val+1) (by have := i.isLt; omega))) (1:F) := rfl
  rw [hs,Pi.add_apply] at he
  by_cases hp : pathChain (verticalAtColumnPath P x S f (lastGridInterior S)
      (i.val+1) (by have := i.isLt; omega)) e=0
  · right
    rw [hp,zero_add,Pi.single_apply] at he
    have hneq : ¬ e≠subdivisionHorizontalEdge P x S f (lastSegment S)
        (gridAt S (i.val+1) (by have := i.isLt; omega)) := by
      intro hn
      exact he (if_neg hn)
    have heq := not_not.mp hneq
    rw [heq]
    simp [subdivisionHorizontalEdge,gridAt,ht0,hth,finInteriorIndex] <;> (congr 3 <;> apply Fin.ext <;> dsimp [gridAt] <;> omega)
  · left
    obtain ⟨k,hk,heq⟩ := verticalAtColumnPath_support P x S f
      (lastGridInterior S) (i.val+1) _ e hp
    refine ⟨k,by omega,?_⟩
    rw [heq]
    simp [subdivisionVerticalEdge,lastGridInterior,hc0,hch,finInteriorIndex,lastInterior] <;>
      (congr 3 <;> apply Fin.ext <;> dsimp [lastGridInterior,lastInterior] <;> omega)
theorem shiftedFacePath1_support_OldXCore_QECert (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (i : Fin (S.half-1))
    (e : SubdivisionEdge P x S) (he : pathChain (shiftedFacePath1 P x S f i) e≠0) :
    (∃ k : Fin S.half, k.val≤ i.val ∧
      e=.inr (.inl (f,k,lastInterior S (by have := i.isLt; omega)))) ∨
      e=.inr (.inr (f,i,lastSegment S)) := by
  have hh : 2≤S.half := by have := i.isLt; omega
  have hc0 : S.half-1≠0 := by omega
  have hch : S.half-1≠S.half := by omega
  have ht0 : i.val+1≠0 := by omega
  have hth : i.val+1≠S.half := by have := i.isLt; omega
  have hs : pathChain (shiftedFacePath1 P x S f i)=
      pathChain (horizontalAtRowPath P x S f (lastGridInterior S) (i.val+1)
        (by have := i.isLt; omega))+
      Pi.single (subdivisionVerticalEdge P x S f
        (gridAt S (i.val+1) (by have := i.isLt; omega)) (lastSegment S)) (1:F) := rfl
  rw [hs,Pi.add_apply] at he
  by_cases hp : pathChain (horizontalAtRowPath P x S f (lastGridInterior S)
      (i.val+1) (by have := i.isLt; omega)) e=0
  · right
    rw [hp,zero_add,Pi.single_apply] at he
    have hneq : ¬ e≠subdivisionVerticalEdge P x S f
        (gridAt S (i.val+1) (by have := i.isLt; omega)) (lastSegment S) := by
      intro hn
      exact he (if_neg hn)
    have heq := not_not.mp hneq
    rw [heq]
    simp [subdivisionVerticalEdge,gridAt,ht0,hth,finInteriorIndex] <;> (congr 3 <;> apply Fin.ext <;> dsimp [gridAt] <;> omega)
  · left
    obtain ⟨k,hk,heq⟩ := horizontalAtRowPath_support P x S f
      (lastGridInterior S) (i.val+1) _ e hp
    refine ⟨k,by omega,?_⟩
    rw [heq]
    simp [subdivisionHorizontalEdge,lastGridInterior,hc0,hch,finInteriorIndex,lastInterior] <;>
      (congr 3 <;> apply Fin.ext <;> dsimp [lastGridInterior,lastInterior] <;> omega)
private theorem rz_q_basis_delta_generic (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (r : P.Q)
    (v : QDoubleCylinderVertex (transposePresentation P) r S) :
    tannerCoboundary1 (rzReplacementPresentation P A S)
      (canonicalBasisWord (F:=F) (.inr ⟨r,v⟩))=
      ∑ z : P.Z, if hz : P.qz r z=true then
        extendZVertexWord P S z (canonicalBasisWord (F:=F)
          (qToZDoubleCylinderVertex P A r z hz S v)) else 0 := by
  ext ⟨z,v'⟩
  erw [tannerCoboundary1_canonicalBasis_apply,Finset.sum_apply]
  change (if rzQZIncidence P A S (.inr ⟨r,v⟩) ⟨z,v'⟩=true then (1:F) else 0)=_
  erw [Finset.sum_eq_single z]
  · by_cases hz : P.qz r z=true
    · erw [dif_pos hz]
      have hinc : rzQZIncidence P A S (.inr ⟨r,v⟩) ⟨z,v'⟩=true ↔
          qToZDoubleCylinderVertex P A r z hz S v=v' := by
        change decide (∃ h : P.qz r z=true,
          qToZDoubleCylinderVertex P A r z h S v=v')=true ↔ _
        simp only [decide_eq_true_eq]
        exact ⟨fun ⟨_,he⟩ => he,fun he => ⟨hz,he⟩⟩
      have hext : extendZVertexWord P S z
          (canonicalBasisWord (F:=F) (qToZDoubleCylinderVertex P A r z hz S v))
          ⟨z,v'⟩=
          (if v'=qToZDoubleCylinderVertex P A r z hz S v then 1 else 0) := by
        simp only [extendZVertexWord,↓reduceDIte,basis_value] <;> split_ifs <;> rfl
      apply (indicator_iff _ _ hinc).trans
      calc
        _ = (if v'=qToZDoubleCylinderVertex P A r z hz S v then 1 else 0) :=
          indicator_iff _ _ ⟨Eq.symm,Eq.symm⟩
        _ = _ := hext.symm
    · erw [dif_neg hz]
      have hn : ¬rzQZIncidence P A S (.inr ⟨r,v⟩) ⟨z,v'⟩=true := by
        change ¬decide (∃ h : P.qz r z=true,
          qToZDoubleCylinderVertex P A r z h S v=v')=true
        simpa only [decide_eq_true_eq] using
          (fun h : ∃ h : P.qz r z=true,
            qToZDoubleCylinderVertex P A r z h S v=v' => hz h.1)
      exact if_neg hn
  · intro z' _ hne
    by_cases hz : P.qz r z'=true <;>
      simp [hz,extendZVertexWord,Ne.symm hne]
  · simp
private theorem unique_z_qBasis_delta1 (S : OddScale) (r : (RawOne S).Q)
    (z : (RawOne S).Z) (hz : (RawOne S).qz r z=true)
    (hu : ∀ z', (RawOne S).qz r z'=true → z'=z)
    (v : QDoubleCylinderVertex (transposePresentation (RawOne S)) r S) :
    tannerCoboundary1 (RawTwo S) (canonicalBasisWord (F:=F) (.inr ⟨r,v⟩))=
      extendZVertexWord (RawOne S) S z (canonicalBasisWord (F:=F)
        (qToZDoubleCylinderVertex (RawOne S)
          (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S v)) := by
  calc
    _ = ∑ z' : (RawOne S).Z, if h : (RawOne S).qz r z'=true then
        extendZVertexWord (RawOne S) S z' (canonicalBasisWord (F:=F)
          (qToZDoubleCylinderVertex (RawOne S)
            (rxState S baseState).admissible.toTannerSquareAdmissible r z' h S v)) else 0 :=
      rz_q_basis_delta_generic (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible S r v
    _ = _ := by
      rw [Finset.sum_eq_single z]
      · exact dif_pos hz
      · intro z' _ hn
        have hnot : ¬(RawOne S).qz r z'=true := fun h => hn (hu z' h)
        exact dif_neg hnot
      · intro hn
        exact False.elim (hn (Finset.mem_univ z))
theorem linear_word_add_zero_OldXBounded_QECert {I J : Type}
    (D : Word F I →ₗ[F] Word F J) (a b : Word F I)
    (ha : D a=0) (hb : D b=0) : D (a+b)=0 := by
  rw [map_add,ha,hb,zero_add]
private theorem linear_three_cancel {I J : Type}
    (D : Word F I →ₗ[F] Word F J) (a b c : Word F I)
    (u v w : Word F J) (ha : D a=u) (hb : D b=v)
    (hc : D c=(w+u)+(w+v)) : D (a+b+c)=0 := by
  rw [map_add,map_add,ha,hb,hc]
  exact three_words_cancel_OldXBounded_QECert u v w
private theorem extended_two_paths_boundary (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (z : P.Z)
    (root u v : ZDoubleCylinderVertex P z S)
    (p : UndirectedPath (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S) root u)
    (p' : UndirectedPath (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S) root v) :
    tannerCoboundary1 (rzReplacementPresentation P A.toTannerSquareAdmissible S)
      (extendZEdgeWord P S z (pathChain p+pathChain p'))=
        (extendZVertexWord P S z (canonicalBasisWord (F:=F) root)+
          extendZVertexWord P S z (canonicalBasisWord (F:=F) u))+
        (extendZVertexWord P S z (canonicalBasisWord (F:=F) root)+
          extendZVertexWord P S z (canonicalBasisWord (F:=F) v)) := by
  rw [rzCoboundary1_extendZEdgeWord P A S z,map_add]
  have hp : rzCzGraphBoundary P z S (pathChain p)=
      canonicalBasisWord (F:=F) root+canonicalBasisWord (F:=F) u :=
    graphBoundary_pathChain _ _ root p
  have hp' : rzCzGraphBoundary P z S (pathChain p')=
      canonicalBasisWord (F:=F) root+canonicalBasisWord (F:=F) v :=
    graphBoundary_pathChain _ _ root p'
  rw [hp,hp',extendZVertexWord_add,extendZVertexWord_add,extendZVertexWord_add]
theorem twoArmKernel_closed_OldXBounded_QECert (S : OddScale)
    (r r' : (RawOne S).Q) (z : (RawOne S).Z)
    (hz : (RawOne S).qz r z=true) (hz' : (RawOne S).qz r' z=true)
    (hu : ∀ z', (RawOne S).qz r z'=true → z'=z)
    (hu' : ∀ z', (RawOne S).qz r' z'=true → z'=z)
    (v : QDoubleCylinderVertex (transposePresentation (RawOne S)) r S)
    (v' : QDoubleCylinderVertex (transposePresentation (RawOne S)) r' S)
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
        (rxState S baseState).admissible.toTannerSquareAdmissible r' z hz' S v')) :
    tannerCoboundary1 (RawTwo S) (twoArmKernel S r r' z hz hz' v v' root p p')=0 := by
  exact linear_three_cancel (tannerCoboundary1 (RawTwo S))
    (canonicalBasisWord (F:=F) (.inr ⟨r,v⟩))
    (canonicalBasisWord (F:=F) (.inr ⟨r',v'⟩))
    (extendZEdgeWord (RawOne S) S z (pathChain p+pathChain p'))
    (extendZVertexWord (RawOne S) S z (canonicalBasisWord (F:=F)
      (qToZDoubleCylinderVertex (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S v)))
    (extendZVertexWord (RawOne S) S z (canonicalBasisWord (F:=F)
      (qToZDoubleCylinderVertex (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible r' z hz' S v')))
    (extendZVertexWord (RawOne S) S z (canonicalBasisWord (F:=F) root))
    (unique_z_qBasis_delta1 S r z hz hu v)
    (unique_z_qBasis_delta1 S r' z hz' hu' v')
    (extended_two_paths_boundary (RawOne S) (rxState S baseState).admissible
      S z root _ _ p p')
theorem stripSeedCocycle_closed_OldXBounded_QECert (j : Fin 2) :
    tannerCoboundary1 baseTannerSquarePresentation (stripSeedCocycle j)=0 := by
  fin_cases j <;> decide
theorem terminalOldKernel_closed_OldXBounded_QECert (S : OddScale) (j : Fin 2) :
    tannerCoboundary1 (RawOne S) (terminalOldKernel S j)=0 := by
  have hrx := LinearMap.congr_fun
    (BDL26ReplacementCochainMaps.rxMap_commutes_coboundary1
      baseTannerSquarePresentation S) (stripSeedCocycle j)
  change BDL26ReplacementCochainMaps.rxCoboundary1 baseTannerSquarePresentation S
      (BDL26ReplacementCochainMaps.rxMap1Coord baseTannerSquarePresentation S
        (stripSeedCocycle j))=
    BDL26ReplacementCochainMaps.rxMap2Coord baseTannerSquarePresentation S
      (tannerCoboundary1 baseTannerSquarePresentation (stripSeedCocycle j)) at hrx
  rw [stripSeedCocycle_closed_OldXBounded_QECert,map_zero] at hrx
  have hmap : tannerCoboundary1 (RawOne S)
      (BDL26ReplacementCochainMaps.rxMap1Coord baseTannerSquarePresentation S
        (stripSeedCocycle j))=0 := by
    erw [BDL26RXLocalReplacement.rxPresentation_coboundary1_eq
      baseTannerSquarePresentation baseTannerSquareAdmissibleV4
      baseTannerSquareCellularRegular S]
    exact hrx
  have hb := LinearMap.congr_fun
    (BDL26LevelTwoDistance.tannerCoboundary_squared (RawOne S)) (stripPotential S j)
  change tannerCoboundary1 (RawOne S)
    (tannerCoboundary0 (RawOne S) (stripPotential S j))=0 at hb
  have hmap' : tannerCoboundary1 (RawOne S) (rawSeedLift S j)=0 := hmap
  exact linear_word_add_zero_OldXBounded_QECert (tannerCoboundary1 (RawOne S))
    (rawSeedLift S j) (tannerCoboundary0 (RawOne S) (stripPotential S j)) hmap' hb
theorem base_star_face_cases_OldXBounded_QECert (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) :
    ∃ k : Fin 2, f=stripFace k x := by
  fin_cases x
  · exact (by decide : ∀ f : XStarFace baseTannerSquarePresentation (0 : BaseX),
      ∃ k : Fin 2, f=stripFace k 0) f
  · exact (by decide : ∀ f : XStarFace baseTannerSquarePresentation (1 : BaseX),
      ∃ k : Fin 2, f=stripFace k 1) f
theorem grid_vertex_view_OldXBounded_QECert (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) (i j : Fin (S.half+1)) :
    subdivisionGridVertex P x S f i j=
      if hi0 : i.val=0 then
        if hj0 : j.val=0 then Sum.inl (xStarFaceXVertex P x f)
        else if hjm : j.val=S.half then Sum.inl (xStarFaceQVertex P x f 1)
        else Sum.inr (Sum.inl (xStarFaceXQEdge P x f 1,finInteriorIndex S j hj0 hjm))
      else if him : i.val=S.half then
        if hj0 : j.val=0 then Sum.inl (xStarFaceQVertex P x f 0)
        else if hjm : j.val=S.half then Sum.inl (xStarFaceZVertex P x f)
        else Sum.inr (Sum.inl (xStarFaceQZEdge P x f 0,finInteriorIndex S j hj0 hjm))
      else if hj0 : j.val=0 then
        Sum.inr (Sum.inl (xStarFaceXQEdge P x f 0,finInteriorIndex S i hi0 him))
      else if hjm : j.val=S.half then
        Sum.inr (Sum.inl (xStarFaceQZEdge P x f 1,finInteriorIndex S i hi0 him))
      else Sum.inr (Sum.inr
        (f,finInteriorIndex S i hi0 him,finInteriorIndex S j hj0 hjm)) := rfl
theorem segment_end_view_OldXCore_QECert (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (e : XStarEdge P x) (k : Fin S.half) :
    subdivisionSegmentEnd P x S e k=
      if h : k.val+1=S.half then Sum.inl (xStarEdgeEnd P x e)
      else Sum.inr (Sum.inl (e,⟨k.val,by have := k.isLt; omega⟩)) := rfl
private theorem stripMember_face_x (S : OddScale) (j : Fin 2) (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) :
    stripMember j x S (.inl (xStarFaceXVertex _ _ f))=false := rfl
private theorem stripMember_face_q (S : OddScale) (j : Fin 2) (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) (c : BDL26FiniteTannerSquare.Two) :
    stripMember j x S (.inl (xStarFaceQVertex _ _ f c))=
      decide (f=stripFace j x ∧ c=0) := by
  dsimp only [stripMember,xStarFaceQVertex]
  apply Bool.decide_congr
  obtain ⟨k,rfl⟩ := base_star_face_cases_OldXBounded_QECert x f
  dsimp only [stripFace,stripQ,XStarFace,TannerSquarePresentation.X,
    TannerSquarePresentation.Q,TannerSquarePresentation.Z,TannerSquarePresentation.Face,
    TannerSquarePresentation.faceX,TannerSquarePresentation.faceQ,TannerSquarePresentation.faceZ,
    TannerSquarePresentation.xq,TannerSquarePresentation.qz,
    baseTannerSquarePresentation,baseTannerSquareData,baseZeroX,
    BaseX,BaseQubit,BaseZ,BaseFace,BDL26FiniteTannerSquare.Two] at *
  fin_cases j <;> fin_cases x <;> fin_cases k <;> fin_cases c
  all_goals
    norm_num [baseFaceQ,baseFaceZ,Subtype.ext_iff,
      raw_two_eq_value_OldXBounded_QECert,raw_four_eq_value_OldXBounded_QECert,raw_five_eq_value_OldXBounded_QECert,
      Fin.val_mk,Fin.val_zero,Fin.val_one]
  all_goals first | rfl | omega
private theorem stripMember_face_z (S : OddScale) (j : Fin 2) (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) :
    stripMember j x S (.inl (xStarFaceZVertex _ _ f))=
      decide (f=stripFace j x) := by
  dsimp only [stripMember,xStarFaceZVertex]
  apply Bool.decide_congr
  obtain ⟨k,rfl⟩ := base_star_face_cases_OldXBounded_QECert x f
  dsimp only [stripFace,stripQ,XStarFace,TannerSquarePresentation.X,
    TannerSquarePresentation.Q,TannerSquarePresentation.Z,TannerSquarePresentation.Face,
    TannerSquarePresentation.faceX,TannerSquarePresentation.faceQ,TannerSquarePresentation.faceZ,
    TannerSquarePresentation.xq,TannerSquarePresentation.qz,
    baseTannerSquarePresentation,baseTannerSquareData,baseZeroX,
    BaseX,BaseQubit,BaseZ,BaseFace,BDL26FiniteTannerSquare.Two] at *
  fin_cases j <;> fin_cases x <;> fin_cases k
  all_goals
    norm_num [baseFaceQ,baseFaceZ,Subtype.ext_iff,
      raw_two_eq_value_OldXBounded_QECert,raw_four_eq_value_OldXBounded_QECert,raw_five_eq_value_OldXBounded_QECert,
      Fin.val_mk,Fin.val_zero,Fin.val_one]
  all_goals first | rfl | omega
private theorem stripMember_face_xq (S : OddScale) (j : Fin 2) (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) (c : BDL26FiniteTannerSquare.Two)
    (i : Fin (S.half-1)) :
    stripMember j x S (.inr (.inl (xStarFaceXQEdge _ _ f c,i)))=false := rfl
private theorem stripMember_face_qz (S : OddScale) (j : Fin 2) (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) (c : BDL26FiniteTannerSquare.Two)
    (i : Fin (S.half-1)) :
    stripMember j x S (.inr (.inl (xStarFaceQZEdge _ _ f c,i)))=
      decide (f=stripFace j x ∧ c=0) := by
  dsimp only [stripMember,xStarFaceQZEdge,faceQZEdge]
  apply Bool.decide_congr
  obtain ⟨k,rfl⟩ := base_star_face_cases_OldXBounded_QECert x f
  dsimp only [stripFace,stripQ,XStarFace,TannerSquarePresentation.X,
    TannerSquarePresentation.Q,TannerSquarePresentation.Z,TannerSquarePresentation.Face,
    TannerSquarePresentation.faceX,TannerSquarePresentation.faceQ,TannerSquarePresentation.faceZ,
    TannerSquarePresentation.xq,TannerSquarePresentation.qz,
    baseTannerSquarePresentation,baseTannerSquareData,baseZeroX,
    BaseX,BaseQubit,BaseZ,BaseFace,BDL26FiniteTannerSquare.Two] at *
  fin_cases j <;> fin_cases x <;> fin_cases k <;> fin_cases c
  all_goals
    norm_num [baseFaceQ,baseFaceZ,Subtype.ext_iff,
      raw_two_eq_value_OldXBounded_QECert,raw_four_eq_value_OldXBounded_QECert,raw_five_eq_value_OldXBounded_QECert,
      Fin.val_mk,Fin.val_zero,Fin.val_one]
  all_goals first | rfl | omega
private theorem stripMember_face_cell (S : OddScale) (j : Fin 2) (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) (i k : Fin (S.half-1)) :
    stripMember j x S (.inr (.inr (f,i,k)))=false := rfl
private theorem stripMember_grid (S : OddScale) (j : Fin 2) (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) (a b : Fin (S.half+1)) :
    stripMember j x S (subdivisionGridVertex baseTannerSquarePresentation x S f a b)=
      decide (f=stripFace j x ∧ a.val=S.half) := by
  have hm : S.half≠0 := S.half_pos.ne'
  have h01 : (0 : BDL26FiniteTannerSquare.Two)≠1 := by decide
  have h10 : (1 : BDL26FiniteTannerSquare.Two)≠0 := by decide
  by_cases hf : f=stripFace j x
  all_goals erw [grid_vertex_view_OldXBounded_QECert]
  all_goals split_ifs
  all_goals simp_all only [stripMember_face_x,stripMember_face_q,stripMember_face_z,
    stripMember_face_xq,stripMember_face_qz,stripMember_face_cell,hm,Ne.symm hm,h01,h10,
    true_and,false_and,and_true,and_false,decide_true,decide_false,
    Bool.false_eq_true,Bool.true_eq_false,not_true_eq_false,not_false_eq_true]
private theorem terminalOldKernel_horizontal (S : OddScale) (j : Fin 2)
    (x : BaseX) (c : BDL26FiniteTannerSquare.Two)
    (f : XStarFace baseTannerSquarePresentation x) (i : Fin S.half)
    (row : Fin (S.half+1)) :
    terminalOldKernel S j (.inl ⟨x,.inl (c,
      subdivisionHorizontalEdge baseTannerSquarePresentation x S f i row)⟩)=
      if f=stripFace j x ∧ i.val+1=S.half then 1 else 0 := by
  erw [terminalOldKernel,Pi.add_apply,rawSeedLift,
    BDL26ReplacementCochainMaps.rxMap1Coord_localEdge,zero_add,rx_local_gradient]
  change (if stripMember j x S (subdivisionEdgeStart baseTannerSquarePresentation x S
      (subdivisionHorizontalEdge baseTannerSquarePresentation x S f i row)) then
      (1:F) else 0)+
    (if stripMember j x S (subdivisionEdgeEnd baseTannerSquarePresentation x S
      (subdivisionHorizontalEdge baseTannerSquarePresentation x S f i row)) then
      (1:F) else 0)=_
  erw [own_horizontal_start,own_horizontal_end,
    stripMember_grid,stripMember_grid]
  have hi : i.val≠S.half := Nat.ne_of_lt i.isLt
  simp only [finCastGrid,finSuccGrid,Fin.val_mk,hi,false_and,and_false,decide_false,
    Bool.false_eq_true,if_false,zero_add,decide_eq_true_eq]
  by_cases hp : f=stripFace j x ∧ i.val+1=S.half
  · simp [hp]
  · simp [hp]
private theorem terminalOldKernel_vertical (S : OddScale) (j : Fin 2)
    (x : BaseX) (c : BDL26FiniteTannerSquare.Two)
    (f : XStarFace baseTannerSquarePresentation x) (column : Fin (S.half+1))
    (i : Fin S.half) :
    terminalOldKernel S j (.inl ⟨x,.inl (c,
      subdivisionVerticalEdge baseTannerSquarePresentation x S f column i)⟩)=0 := by
  erw [terminalOldKernel,Pi.add_apply,rawSeedLift,
    BDL26ReplacementCochainMaps.rxMap1Coord_localEdge,zero_add,rx_local_gradient]
  change (if stripMember j x S (subdivisionEdgeStart baseTannerSquarePresentation x S
      (subdivisionVerticalEdge baseTannerSquarePresentation x S f column i)) then
      (1:F) else 0)+
    (if stripMember j x S (subdivisionEdgeEnd baseTannerSquarePresentation x S
      (subdivisionVerticalEdge baseTannerSquarePresentation x S f column i)) then
      (1:F) else 0)=0
  erw [own_vertical_start,own_vertical_end,
    stripMember_grid,stripMember_grid]
  exact ZModModule.add_self _
theorem subdivision_edge_grid_cover_OldXCore_QECert (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (x : P.X) (S : OddScale)
    (e : SubdivisionEdge P x S) :
    (∃ (f : XStarFace P x) (i : Fin S.half) (row : Fin (S.half+1)),
      e=subdivisionHorizontalEdge P x S f i row) ∨
    (∃ (f : XStarFace P x) (column : Fin (S.half+1)) (i : Fin S.half),
      e=subdivisionVerticalEdge P x S f column i) := by
  rcases e with ⟨⟨edge,hm⟩,k⟩ | h | v
  · rcases edge with edge | edge
    · obtain ⟨⟨f,c⟩,hf⟩ := A.xRadialFaceOwner x edge hm
      fin_cases c
      · left
        refine ⟨f,k,0,?_⟩
        simpa [subdivisionHorizontalEdge] using
          congrArg (fun e : XStarEdge P x => (Sum.inl (e,k) : SubdivisionEdge P x S)) hf.symm
      · right
        refine ⟨f,0,k,?_⟩
        simpa [subdivisionVerticalEdge] using
          congrArg (fun e : XStarEdge P x => (Sum.inl (e,k) : SubdivisionEdge P x S)) hf.symm
    · obtain ⟨⟨f,c⟩,hf⟩ := A.xBoundaryFaceOwner x edge hm
      fin_cases c
      · right
        refine ⟨f,gridAt S S.half le_rfl,k,?_⟩
        simpa [subdivisionVerticalEdge,gridAt,S.half_pos.ne'] using
          congrArg (fun e : XStarEdge P x => (Sum.inl (e,k) : SubdivisionEdge P x S)) hf.symm
      · left
        refine ⟨f,k,gridAt S S.half le_rfl,?_⟩
        simpa [subdivisionHorizontalEdge,gridAt,S.half_pos.ne'] using
          congrArg (fun e : XStarEdge P x => (Sum.inl (e,k) : SubdivisionEdge P x S)) hf.symm
  · rcases h with ⟨f,i,k⟩
    left
    refine ⟨f,i,finInteriorGrid S k,?_⟩
    have hk0 : (finInteriorGrid S k).val≠0 := by simp [finInteriorGrid]
    have hkh : (finInteriorGrid S k).val≠S.half := by
      have := k.isLt
      dsimp [finInteriorGrid]
      omega
    unfold subdivisionHorizontalEdge
    rw [dif_neg hk0,dif_neg hkh]
    apply congrArg (fun k' : Fin (S.half-1) =>
      (Sum.inr (Sum.inl (f,i,k')) : SubdivisionEdge P x S))
    apply Fin.ext
    change k.val=(k.val+1)-1
    omega
  · rcases v with ⟨f,k,i⟩
    right
    refine ⟨f,finInteriorGrid S k,i,?_⟩
    have hk0 : (finInteriorGrid S k).val≠0 := by simp [finInteriorGrid]
    have hkh : (finInteriorGrid S k).val≠S.half := by
      have := k.isLt
      dsimp [finInteriorGrid]
      omega
    unfold subdivisionVerticalEdge
    rw [dif_neg hk0,dif_neg hkh]
    apply congrArg (fun k' : Fin (S.half-1) =>
      (Sum.inr (Sum.inr (f,k',i)) : SubdivisionEdge P x S))
    apply Fin.ext
    change k.val=(k.val+1)-1
    omega
theorem terminalOldKernel_target_OldXBounded_QECert (S : OddScale) (j : Fin 2)
    (c : BDL26FiniteTannerSquare.Two) :
    terminalOldKernel S j (.inl ⟨(0 : BaseX),
      .inl (c,.inl (seedRadial j,lastSegment S))⟩)=1 := by
  have h := terminalOldKernel_horizontal S j (0 : BaseX) c (seedFace j) (lastSegment S) 0
  have hedge : subdivisionHorizontalEdge baseTannerSquarePresentation (0 : BaseX) S
      (seedFace j) (lastSegment S) 0=(.inl (seedRadial j,lastSegment S) :
        SubdivisionEdge baseTannerSquarePresentation 0 S) := by
    simp only [subdivisionHorizontalEdge,Fin.val_zero,↓reduceDIte]
    exact congrArg (fun e : XStarEdge baseTannerSquarePresentation (0 : BaseX) =>
      (Sum.inl (e,lastSegment S) : SubdivisionEdge baseTannerSquarePresentation 0 S))
        ((seedRadial_face_zero j (seedFace j)).mpr rfl).symm
  erw [hedge] at h
  apply h.trans
  apply if_pos
  constructor
  · fin_cases j <;> rfl
  · dsimp only [lastSegment]; have := S.half_pos; omega
private theorem qVertexX_coordinate (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (x : P.X) (q : P.Q)
    (hx : P.xq x q=true) (v : QDoubleCylinderVertex P q S)
    (u : DoubleCylinderVertex P x S) :
    qDoubleCylinderVertexXIncidence P q x S u v=
      vertexIndicator u (qToXDoubleCylinderVertexAtRoot P q x hx S (A.qzRoot q) v) := by
  rcases u with ⟨uc,u⟩
  rcases v with ⟨vc,v⟩
  fin_cases uc <;> fin_cases vc
  all_goals rcases u with u | edgeInterior | faceInterior
  all_goals rcases v with v | edgeInterior'
  all_goals
    first
    | (rcases v with cone | endpoint <;>
        simp [qDoubleCylinderVertexXIncidence,qSubdivisionVertexXIncidence,
          qToXDoubleCylinderVertexAtRoot,qToXSubdivisionVertexAtRoot,
          qToXBoundaryVertexAtRoot,xStarBoundaryVertexToStar,xBoundaryEdgeStart,
          xBoundaryEdgeEnd,qToXBoundaryEdge,vertexIndicator,Subtype.ext_iff,
          Prod.ext_iff,hx])
    | simp [qDoubleCylinderVertexXIncidence,qSubdivisionVertexXIncidence,
        qToXDoubleCylinderVertexAtRoot,qToXSubdivisionVertexAtRoot,
        qToXBoundaryVertexAtRoot,xStarBoundaryVertexToStar,xBoundaryEdgeStart,
        xBoundaryEdgeEnd,qToXBoundaryEdge,vertexIndicator,Subtype.ext_iff,Prod.ext_iff,hx]
  all_goals
    rcases edgeInterior with ⟨⟨edge,hm⟩,i⟩
    rcases edge with xq | qz
    · simp [xStarBoundaryEdgeToStar,vertexIndicator,Subtype.ext_iff] at hm ⊢
    · simp [xStarBoundaryEdgeToStar,qToXBoundaryEdge,vertexIndicator,
        Subtype.ext_iff,Prod.ext_iff,and_assoc]
theorem rx_q_gradient_OldXBounded_QECert (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (p : Word F (RX0 P S))
    (q : P.Q) (v : QDoubleCylinderVertex P q S) :
    BDL26ReplacementCochainMaps.rxCoboundary0 P S p (.inr ⟨q,v⟩)=
      ∑ x : P.X, if hx : P.xq x q=true then
        p ⟨x,qToXDoubleCylinderVertexAtRoot P q x hx S (A.qzRoot q) v⟩ else 0 := by
  unfold BDL26ReplacementCochainMaps.rxCoboundary0 rxBoundary1
  rw [wordLinearMapTranspose_toLin'_apply,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P.xq x q=true
  · rw [dif_pos hx]
    change (∑ u : DoubleCylinderVertex P x S,
      p ⟨x,u⟩*qDoubleCylinderVertexXIncidence P q x S u v)=_
    simp_rw [qVertexX_coordinate P A S x q hx v]
    let target := qToXDoubleCylinderVertexAtRoot P q x hx S (A.qzRoot q) v
    rw [Finset.sum_eq_single target]
    · simp [vertexIndicator,target]
    · intro u _ hu
      change u≠qToXDoubleCylinderVertexAtRoot P q x hx S (A.qzRoot q) v at hu
      simp only [vertexIndicator,if_neg hu,mul_zero]
    · intro hn
      exact False.elim (hn (Finset.mem_univ target))
  · simp [rxBoundary1Matrix,qDoubleCylinderVertexXIncidence,
      qSubdivisionVertexXIncidence,hx]
private theorem stripPotential_port_cone (S : OddScale) (j : Fin 2)
    (x : BaseX) (q : BaseQubit) (hx : baseTannerSquarePresentation.xq x q=true)
    (root : QStarEdge baseTannerSquarePresentation q) (c : BDL26FiniteTannerSquare.Two) :
    stripPotential S j ⟨x,qToXDoubleCylinderVertexAtRoot baseTannerSquarePresentation
      q x hx S root (c,.inl (.inl ()))⟩=
        if decide (q=stripQ j x) then 1 else 0 := by
  dsimp only [stripPotential,stripMember,qToXDoubleCylinderVertexAtRoot,
    qToXSubdivisionVertexAtRoot,qToXBoundaryVertexAtRoot,qToXBoundaryEdge,
    xBoundaryEdgeStart,xBoundaryEdgeEnd,xStarBoundaryVertexToStar,xStarBoundaryEdgeToStar]
  apply indicator_iff
  simp only [decide_eq_true_eq]
  all_goals rfl
private theorem stripPotential_port_endpoint (S : OddScale) (j : Fin 2)
    (x : BaseX) (q : BaseQubit) (hx : baseTannerSquarePresentation.xq x q=true)
    (root edge : QStarEdge baseTannerSquarePresentation q) (c : BDL26FiniteTannerSquare.Two) :
    stripPotential S j ⟨x,qToXDoubleCylinderVertexAtRoot baseTannerSquarePresentation
      q x hx S root (c,.inl (.inr edge))⟩=
        if decide (edge.val=j) then 1 else 0 := rfl
private theorem stripPotential_port_interior (S : OddScale) (j : Fin 2)
    (x : BaseX) (q : BaseQubit) (hx : baseTannerSquarePresentation.xq x q=true)
    (root edge : QStarEdge baseTannerSquarePresentation q) (c : BDL26FiniteTannerSquare.Two)
    (i : Fin (S.half-1)) :
    stripPotential S j ⟨x,qToXDoubleCylinderVertexAtRoot baseTannerSquarePresentation
      q x hx S root (c,.inr (edge,i))⟩=
        if decide (q=stripQ j x ∧ edge.val=j) then 1 else 0 := by
  dsimp only [stripPotential,stripMember,qToXDoubleCylinderVertexAtRoot,
    qToXSubdivisionVertexAtRoot,qToXBoundaryVertexAtRoot,qToXBoundaryEdge,
    xBoundaryEdgeStart,xBoundaryEdgeEnd,xStarBoundaryVertexToStar,xStarBoundaryEdgeToStar]
  apply indicator_iff
  simp only [decide_eq_true_eq]
  all_goals rfl
theorem strip_sum_cone_OldXBounded_QECert (j : Fin 2) (q : BaseQubit) :
    (∑ x : BaseX, if hx : baseTannerSquarePresentation.xq x q=true then
      (if decide (q=stripQ j x) then (1:F) else 0) else 0)=stripSeedCocycle j q := by
  have h10 : (1:F)≠0 := one_ne_zero
  have h01 : (0:F)≠1 := zero_ne_one
  rw [Fin.sum_univ_two]
  simp only [base_xq_matrix_value_OldXCore_QECert]
  fin_cases j <;> fin_cases q
  all_goals
    norm_num [baseBoundary1Matrix,stripQ,stripSeedCocycle,
      base_X_eq_value_OldXBounded_QECert,base_Q_eq_value_OldXBounded_QECert,base_Z_eq_value_OldXBounded_QECert,Fin.ext_iff,
      Fin.val_mk,Fin.val_zero,Fin.val_one,ZModModule.add_self,h10,h01]
theorem strip_sum_endpoint_OldXBounded_QECert (j : Fin 2) (q : BaseQubit) (z : baseTannerSquarePresentation.Z)
    (hz : baseTannerSquarePresentation.qz q z=true) :
    (∑ x : BaseX, if hx : baseTannerSquarePresentation.xq x q=true then
      (if decide (z=j) then (1:F) else 0) else 0)=stripSeedCocycle j q := by
  have h10 : (1:F)≠0 := one_ne_zero
  have h01 : (0:F)≠1 := zero_ne_one
  rw [Fin.sum_univ_two]
  simp only [base_xq_matrix_value_OldXCore_QECert]
  have hz' := (base_qz_matrix_value_OldXCore_QECert q z).symm.trans hz
  have hqz : baseBoundary2Matrix q z≠0 := of_decide_eq_true hz'
  dsimp only [stripFace,stripQ,XStarFace,TannerSquarePresentation.X,
    TannerSquarePresentation.Q,TannerSquarePresentation.Z,TannerSquarePresentation.Face,
    TannerSquarePresentation.faceX,TannerSquarePresentation.faceQ,TannerSquarePresentation.faceZ,
    TannerSquarePresentation.xq,TannerSquarePresentation.qz,
    baseTannerSquarePresentation,baseTannerSquareData,baseZeroX,
    BaseX,BaseQubit,BaseZ,BaseFace,BDL26FiniteTannerSquare.Two] at *
  fin_cases j <;> fin_cases q <;> fin_cases z
  all_goals norm_num [baseBoundary2Matrix] at hqz
  all_goals
    norm_num [baseBoundary1Matrix,stripSeedCocycle,
      raw_two_eq_value_OldXBounded_QECert,raw_four_eq_value_OldXBounded_QECert,raw_five_eq_value_OldXBounded_QECert,
      Fin.val_mk,Fin.val_zero,Fin.val_one,ZModModule.add_self,h10,h01]
  all_goals first | rfl | omega
private theorem strip_sum_interior (j : Fin 2) (q : BaseQubit) (z : baseTannerSquarePresentation.Z)
    (hz : baseTannerSquarePresentation.qz q z=true) :
    (∑ x : BaseX, if hx : baseTannerSquarePresentation.xq x q=true then
      (if decide (q=stripQ j x ∧ z=j) then (1:F) else 0) else 0)=stripSeedCocycle j q := by
  have h10 : (1:F)≠0 := one_ne_zero
  have h01 : (0:F)≠1 := zero_ne_one
  rw [Fin.sum_univ_two]
  simp only [base_xq_matrix_value_OldXCore_QECert]
  have hz' := (base_qz_matrix_value_OldXCore_QECert q z).symm.trans hz
  have hqz : baseBoundary2Matrix q z≠0 := of_decide_eq_true hz'
  dsimp only [stripFace,stripQ,XStarFace,TannerSquarePresentation.X,
    TannerSquarePresentation.Q,TannerSquarePresentation.Z,TannerSquarePresentation.Face,
    TannerSquarePresentation.faceX,TannerSquarePresentation.faceQ,TannerSquarePresentation.faceZ,
    TannerSquarePresentation.xq,TannerSquarePresentation.qz,
    baseTannerSquarePresentation,baseTannerSquareData,baseZeroX,
    BaseX,BaseQubit,BaseZ,BaseFace,BDL26FiniteTannerSquare.Two] at *
  fin_cases j <;> fin_cases q <;> fin_cases z
  all_goals norm_num [baseBoundary2Matrix] at hqz
  all_goals
    norm_num [baseBoundary1Matrix,stripSeedCocycle,
      raw_two_eq_value_OldXBounded_QECert,raw_four_eq_value_OldXBounded_QECert,raw_five_eq_value_OldXBounded_QECert,
      Fin.val_mk,Fin.val_zero,Fin.val_one,ZModModule.add_self,h10,h01]
  all_goals first | rfl | omega
private theorem stripPotential_q_gradient (S : OddScale) (j : Fin 2) (q : BaseQubit)
    (v : QDoubleCylinderVertex baseTannerSquarePresentation q S) :
    tannerCoboundary0 (RawOne S) (stripPotential S j) (.inr ⟨q,v⟩)=
      stripSeedCocycle j q := by
  erw [BDL26RXLocalReplacement.rxPresentation_coboundary0_eq
    baseTannerSquarePresentation baseTannerSquareAdmissibleV4
    baseTannerSquareCellularRegular S]
  erw [rx_q_gradient_OldXBounded_QECert baseTannerSquarePresentation baseTannerSquareAdmissible S]
  change (∑ x : BaseX, if hx : baseTannerSquarePresentation.xq x q=true then
    stripPotential S j ⟨x,qToXDoubleCylinderVertexAtRoot baseTannerSquarePresentation
      q x hx S (baseTannerSquareAdmissible.qzRoot q) v⟩ else 0)=stripSeedCocycle j q
  rcases v with ⟨c,(cone | endpoint) | ⟨edge,i⟩⟩
  · cases cone
    simp_rw [stripPotential_port_cone]
    exact strip_sum_cone_OldXBounded_QECert j q
  · rcases endpoint with ⟨z,hz⟩
    change BaseZ at z
    simp_rw [stripPotential_port_endpoint]
    exact strip_sum_endpoint_OldXBounded_QECert j q z hz
  · rcases edge with ⟨z,hz⟩
    change BaseZ at z
    simp_rw [stripPotential_port_interior]
    exact strip_sum_interior j q z hz
private theorem terminalOldKernel_q_zero (S : OddScale) (j : Fin 2) (q : BaseQubit)
    (v : QDoubleCylinderVertex baseTannerSquarePresentation q S) :
    terminalOldKernel S j (.inr ⟨q,v⟩)=0 := by
  erw [terminalOldKernel,Pi.add_apply,rawSeedLift,
    BDL26ReplacementCochainMaps.rxMap1Coord_qVertex,stripPotential_q_gradient]
  exact ZModModule.add_self _
theorem terminalOldKernel_support_OldXBounded_QECert (S : OddScale) (j : Fin 2)
    (r : (RawOne S).Q) (hr : terminalOldKernel S j r≠0) :
    ∃ (x : BaseX) (c : BDL26FiniteTannerSquare.Two) (row : Fin (S.half+1)),
      r=stripHorizontal S j x c row := by
  change RX1 baseTannerSquarePresentation S at r
  rcases r with ⟨x,e⟩ | ⟨q,v⟩
  · rcases e with ⟨c,e⟩ | v
    · rcases subdivision_edge_grid_cover_OldXCore_QECert baseTannerSquarePresentation
        baseTannerSquareAdmissibleV4 x S e with hh | hv
      · obtain ⟨f,i,row,he⟩ := hh
        subst e
        erw [terminalOldKernel_horizontal] at hr
        have h : f=stripFace j x ∧ i.val+1=S.half := by
          by_contra hn
          erw [if_neg hn] at hr
          exact hr rfl
        rcases h with ⟨hf,hi⟩
        subst f
        have hilast : i=lastSegment S := by
          apply Fin.ext
          have := i.isLt
          dsimp [lastSegment]
          omega
        subst i
        exact ⟨x,c,row,rfl⟩
      · obtain ⟨f,column,i,he⟩ := hv
        subst e
        erw [terminalOldKernel_vertical] at hr
        exact False.elim (hr rfl)
    · erw [terminalOldKernel,Pi.add_apply,rawSeedLift,
        BDL26ReplacementCochainMaps.rxMap1Coord_localEdge,zero_add,
        rx_local_gradient] at hr
      change ((if stripMember j x S v.val then (1:F) else 0)+
        (if stripMember j x S v.val then (1:F) else 0))≠0 at hr
      exact False.elim (hr (ZModModule.add_self _))
  · exact False.elim (hr (terminalOldKernel_q_zero S j q v))
private theorem qBasis_delta1 (S : OddScale) (r : (RawOne S).Q)
    (v : QDoubleCylinderVertex (transposePresentation (RawOne S)) r S) :
    tannerCoboundary1 (RawTwo S) (canonicalBasisWord (F:=F) (.inr ⟨r,v⟩))=
      ∑ z : (RawOne S).Z, if hz : (RawOne S).qz r z=true then
        extendZVertexWord (RawOne S) S z (canonicalBasisWord (F:=F)
          (qToZDoubleCylinderVertex (RawOne S)
            (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S v))
      else 0 := by
  exact rz_q_basis_delta_generic (RawOne S)
    (rxState S baseState).admissible.toTannerSquareAdmissible S r v
private theorem portBasis_delta1 (S : OddScale) (vertices : PortVertices S)
    (roots : PortRoots S) (paths : PortPaths S vertices roots) (r : (RawOne S).Q) :
    tannerCoboundary1 (RawTwo S) (portBasis S vertices roots paths r)=
      ∑ z : (RawOne S).Z, if (RawOne S).qz r z=true then
        extendZVertexWord (RawOne S) S z (canonicalBasisWord (F:=F) (roots z)) else 0 := by
  erw [portBasis,map_add,qBasis_delta1,map_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : (RawOne S).qz r z=true
  · erw [dif_pos hz,dif_pos hz,if_pos hz,
      rzCoboundary1_extendZEdgeWord (RawOne S)
        (rxState S baseState).admissible S z]
    have hp : rzCzGraphBoundary (RawOne S) z S (pathChain (paths r z hz))=
        canonicalBasisWord (F:=F) (roots z)+canonicalBasisWord (F:=F)
          (qToZDoubleCylinderVertex (RawOne S)
            (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S
            (vertices r)) := graphBoundary_pathChain _ _ _ _
    erw [hp,extendZVertexWord_add]
    exact words_cancel_middle_OldXBounded_QECert _ _
  · erw [dif_neg hz,dif_neg hz,if_neg hz]
    exact (zero_add ((tannerCoboundary1 (RawTwo S))
      (0 : Word F (RawTwo S).Q))).trans (map_zero _)
theorem portKernel_closed_OldXBounded_QECert (S : OddScale) (vertices : PortVertices S)
    (roots : PortRoots S) (paths : PortPaths S vertices roots)
    (w : Word F (RawOne S).Q) (hw : tannerCoboundary1 (RawOne S) w=0) :
    tannerCoboundary1 (RawTwo S) (portKernel S vertices roots paths w)=0 := by
  have hmap : tannerCoboundary1 (RawTwo S) (portKernel S vertices roots paths w)=
      ∑ r : (RawOne S).Q, w r •
        (∑ z : (RawOne S).Z, if (RawOne S).qz r z=true then
          extendZVertexWord (RawOne S) S z (canonicalBasisWord (F:=F) (roots z)) else 0) := by
    erw [portKernel,map_sum]
    apply Finset.sum_congr rfl
    intro r _
    exact (map_smul (tannerCoboundary1 (RawTwo S)) (w r)
      (portBasis S vertices roots paths r)).trans
        (congrArg (fun out : Word F (RawTwo S).Z => w r • out)
          (portBasis_delta1 S vertices roots paths r))
  refine hmap.trans ?_
  refine (collect_indicator_sums_OldXBounded_QECert w (RawOne S).qz
    (fun z => (extendZVertexWord (RawOne S) S z
      (canonicalBasisWord (F:=F) (roots z)) : Word F (RawTwo S).Z))).trans ?_
  apply Finset.sum_eq_zero
  intro z _
  have hz := congrFun hw z
  change (∑ r : (RawOne S).Q,
    w r*(if (RawOne S).qz r z=true then 1 else 0))=0 at hz
  exact (congrArg (fun c : F => c •
    extendZVertexWord (RawOne S) S z (canonicalBasisWord (F:=F) (roots z))) hz).trans
      (zero_smul _ _)
theorem portKernel_q_OldXBounded_QECert (S : OddScale) (vertices : PortVertices S)
    (roots : PortRoots S) (paths : PortPaths S vertices roots)
    (w : Word F (RawOne S).Q) (r : (RawOne S).Q)
    (v : QDoubleCylinderVertex (transposePresentation (RawOne S)) r S) :
    portKernel S vertices roots paths w (.inr ⟨r,v⟩)=
      w r*(if v=vertices r then 1 else 0) := by
  have hport (r' : (RawOne S).Q) :
      portBasis S vertices roots paths r' (.inr ⟨r,v⟩)=
        if (.inr ⟨r,v⟩ : (RawTwo S).Q)=.inr ⟨r',vertices r'⟩ then 1 else 0 := by
    change (canonicalBasisWord (F:=F) (Sum.inr ⟨r',vertices r'⟩ : (RawTwo S).Q)+
      ∑ z : (RawOne S).Z, if hz : (RawOne S).qz r' z=true then
        extendZEdgeWord (RawOne S) S z (pathChain (paths r' z hz)) else 0)
        (.inr ⟨r,v⟩)=_
    apply generic_basis_plus_value_OldXBounded_QECert
    have hs := word_sum_eval_OldXBounded_QECert (fun z : (RawOne S).Z =>
      if hz : (RawOne S).qz r' z=true then
        extendZEdgeWord (RawOne S) S z (pathChain (paths r' z hz)) else 0)
      (.inr ⟨r,v⟩ : (RawTwo S).Q)
    refine hs.trans (Finset.sum_eq_zero ?_)
    intro z _
    by_cases hz : (RawOne S).qz r' z=true
    · simpa only [dif_pos hz] using
        extend_edge_at_port_OldXBounded_QECert (RawOne S) S z (pathChain (paths r' z hz)) r v
    · simp only [dif_neg hz,word_zero_eval]
  calc
    _ = ∑ r' : (RawOne S).Q, w r'*portBasis S vertices roots paths r' (.inr ⟨r,v⟩) :=
      sum_scaled_words_apply_OldXBounded_QECert w (portBasis S vertices roots paths) _
    _ = _ := by
      erw [Finset.sum_eq_single r]
      · rw [hport]
        by_cases he : v=vertices r
        · subst v
          simp
        · simp [he,Sigma.mk.injEq]
      · intro r' _ hn
        rw [hport]
        have hne : (.inr ⟨r,v⟩ : (RawTwo S).Q)≠.inr ⟨r',vertices r'⟩ := by
          intro he
          exact hn (congrArg Sigma.fst (Sum.inr.inj he)).symm
        rw [if_neg hne,mul_zero]
      · simp
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
end
end


