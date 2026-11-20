-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_LiteralPart1_QECert
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint_LiteralPart1_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T10:35:42.931656+00:00
-- url     : https://prove2.me/theorems/5fc0ea4b-5b00-4cb3-9451-469c38a4a599
-- title:
--   RX primitive C2Q endpoint: literal segment 1
-- statement:
--   Definitions and structural lemmas for RXPrimitive C2 QEndpoint, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveFailureLocalization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_physicalMarks_base
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_physicalMarks_step
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCx_delta1_apply
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_raw_delta0_x
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_wordEquiv_weight
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xFlow_at_q
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_qLocalCoboundary_apply
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_boundary1Matrix_eq
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_boundary2Matrix_eq
import Theorems.Thm_QEC_Coding_BDL26RXQEdgePairTransport_bit_cases
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_qToXSubdivisionEdge_end
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_qToXSubdivisionEdge_start
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_cxComponentTotal_local_delta
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_cxComponentTotal_local_flow_weight
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXConstructionContractSlice_cx_local_ranges_of_syndrome
import Theorems.Thm_QEC_Semantics_CompletelyPositive_add
import Theorems.Thm_QEC_Semantics_JumpProtected_add
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_add
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
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26CSSHamiltonian BDL26ActualFailureReadout BDL26LevelTwoCode
open BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder BDL26RXPhysicalCoordinateTrace
open scoped Classical BigOperators
local instance rawOneXEncodable (S : OddScale) : Encodable (RawOne S).X :=
  inferInstanceAs (Encodable (BDL26LevelTwoDecoder.executableLevelOne S).X)
local instance rawOneQEncodable (S : OddScale) : Encodable (RawOne S).Q :=
  inferInstanceAs (Encodable (BDL26LevelTwoDecoder.executableLevelOne S).Q)
local instance rawOneZEncodable (S : OddScale) : Encodable (RawOne S).Z :=
  inferInstanceAs (Encodable (BDL26LevelTwoDecoder.executableLevelOne S).Z)
local instance executableTransposeFaceEncodable (S : OddScale) :
    Encodable (transposePresentation (BDL26LevelTwoDecoder.executableLevelOne S)).Face :=
  inferInstanceAs (Encodable (BDL26LevelTwoDecoder.executableLevelOne S).Face)
local instance executableTransposeEdgeEncodable (S : OddScale) :
    Encodable (BDL26FiniteTannerSquare.Edge
      (transposePresentation (BDL26LevelTwoDecoder.executableLevelOne S))) := by
  letI : Encodable (transposePresentation
      (BDL26LevelTwoDecoder.executableLevelOne S)).X :=
    inferInstanceAs (Encodable (BDL26LevelTwoDecoder.executableLevelOne S).Z)
  letI : Encodable (transposePresentation
      (BDL26LevelTwoDecoder.executableLevelOne S)).Q :=
    inferInstanceAs (Encodable (BDL26LevelTwoDecoder.executableLevelOne S).Q)
  letI : Encodable (transposePresentation
      (BDL26LevelTwoDecoder.executableLevelOne S)).Z :=
    inferInstanceAs (Encodable (BDL26LevelTwoDecoder.executableLevelOne S).X)
  dsimp only [BDL26FiniteTannerSquare.Edge,XQEdge,QZEdge]
  infer_instance
local instance baseZeroX : OfNat baseTannerSquarePresentation.X 0 :=
  inferInstanceAs (OfNat BaseX 0)
local instance rawRX0Encodable (S : OddScale) :
    Encodable (RX0 baseTannerSquarePresentation S) :=
  inferInstanceAs (Encodable (BDL26LevelTwoDecoder.executableLevelOne S).X)
local instance rawRX1Encodable (S : OddScale) :
    Encodable (RX1 baseTannerSquarePresentation S) :=
  inferInstanceAs (Encodable (BDL26LevelTwoDecoder.executableLevelOne S).Q)
local instance baseXEncodable : Encodable baseTannerSquarePresentation.X :=
  inferInstanceAs (Encodable (Fin 2))
local instance baseQEncodable : Encodable baseTannerSquarePresentation.Q :=
  inferInstanceAs (Encodable (Fin 5))
local instance baseZEncodable : Encodable baseTannerSquarePresentation.Z :=
  inferInstanceAs (Encodable (Fin 2))
local instance baseFaceEncodable : Encodable baseTannerSquarePresentation.Face :=
  inferInstanceAs (Encodable (Fin 4))
attribute [local instance] QEC.Coding.BDL26RXPrimitiveC2QEndpoint.rawOneXEncodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.rawOneQEncodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.rawOneZEncodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.executableTransposeFaceEncodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.executableTransposeEdgeEncodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.baseZeroX QEC.Coding.BDL26RXPrimitiveC2QEndpoint.rawRX0Encodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.rawRX1Encodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.baseXEncodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.baseQEncodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.baseZEncodable QEC.Coding.BDL26RXPrimitiveC2QEndpoint.baseFaceEncodable
theorem boundary_edge_qz_view (P : TannerSquarePresentation) (x : P.X)
    (e : QZEdge P) :
    xStarBoundaryEdgeMember P x (.inr e)=decide (∃ f : P.Face,
      xStarFaceMember P x f=true ∧ (e=faceQZEdge P f 0 ∨ e=faceQZEdge P f 1)) := by
  change decide (∃ f : P.Face, xStarFaceMember P x f=true ∧
    decide (e=faceQZEdge P f 0 ∨ e=faceQZEdge P f 1)=true)=_
  apply Bool.decide_congr
  simp only [decide_eq_true_eq]
theorem indicator_iff (p q : Prop) [Decidable p] [Decidable q]
    (h : p ↔ q) : (if p then (1:F) else 0)=(if q then (1:F) else 0) := by
  by_cases hp : p
  · simp only [if_pos hp,if_pos (h.mp hp)]
  · simp only [if_neg hp,if_neg (fun hq => hp (h.mpr hq))]
theorem basis_value {I : Type} (i j : I) :
    canonicalBasisWord (F:=F) i j=(if j=i then 1 else 0) := by
  classical
  by_cases h : j=i
  · subst j
    simp [canonicalBasisWord]
  · simp [canonicalBasisWord,h,Ne.symm h]
attribute [local simp] basis_value
theorem basis_eq_single {I : Type} [DecidableEq I] (i : I) :
    canonicalBasisWord (F:=F) i=Pi.single i 1 := by
  classical
  funext j
  by_cases h : j=i
  · subst j
    simp [basis_value]
  · simp [basis_value,Pi.single_apply,h,Ne.symm h]
theorem word_add_eval {I : Type} (a b : Word F I) (i : I) :
    (a+b) i=a i+b i := rfl
theorem word_smul_eval {I : Type} (c : F) (w : Word F I) (i : I) :
    (c • w) i=c*w i := rfl
theorem word_zero_eval {I : Type} (i : I) : (0 : Word F I) i=0 := rfl
attribute [local simp] word_add_eval word_smul_eval word_zero_eval
theorem sigma_same_index_inj {I : Type} {A : I → Type} {i : I}
    (u v : A i) (h : (Sigma.mk i u : Sigma A)=Sigma.mk i v) : u=v := by
  exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
theorem scalar_unit_pair {I : Type} [DecidableEq I]
    (v start finish : I) (hne : start≠finish) (p : Bool)
    (h : (if p=true then (1:F) else 0)=
      canonicalBasisWord (F:=F) v start+canonicalBasisWord (F:=F) v finish) :
    p=true ↔ v=start ∨ v=finish := by
  simp only [basis_value] at h
  constructor
  · intro hp
    by_cases hs : v=start
    · exact Or.inl hs
    · by_cases ht : v=finish
      · exact Or.inr ht
      · have bad : (1:F)=0 := by simpa [hp,hs,Ne.symm hs,ht,Ne.symm ht] using h
        exact False.elim (one_ne_zero bad)
  · rintro (rfl | rfl)
    · by_contra hp
      have bad : (0:F)=1 := by simpa [hp,hne,Ne.symm hne] using h
      exact zero_ne_one bad
    · by_contra hp
      have bad : (0:F)=1 := by simpa [hp,hne,Ne.symm hne] using h
      exact zero_ne_one bad
theorem transposed_face_member (P : TannerSquarePresentation)
    (z : P.Z) (f : P.Face) :
    xStarFaceMember (transposePresentation P) z f=true ↔ P.faceZ f=z := by
  change decide (P.data.faceZ f=z)=true ↔ P.data.faceZ f=z
  by_cases h : P.data.faceZ f=z <;> simp [h]
theorem two_eq_zero_or_one (c : BDL26FiniteTannerSquare.Two) :
    c=0 ∨ c=1 := by fin_cases c <;> simp
def finCastGrid {m : Nat} (i : Fin m) : Fin (m+1) :=
  ⟨i.val,Nat.lt_succ_of_lt i.isLt⟩
def finSuccGrid {m : Nat} (i : Fin m) : Fin (m+1) :=
  ⟨i.val+1,by have := i.isLt; omega⟩
theorem own_horizontal_start (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) (i : Fin S.half) (row : Fin (S.half+1)) :
    subdivisionEdgeStart P x S (subdivisionHorizontalEdge P x S f i row)=
      subdivisionGridVertex P x S f (finCastGrid i) row := by
  exact (subdivisionHorizontalEdge_start P x S f i row).trans
    (congrArg (fun a : Fin (S.half+1) => subdivisionGridVertex P x S f a row) (by apply Fin.ext; rfl))
theorem own_horizontal_end (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) (i : Fin S.half) (row : Fin (S.half+1)) :
    subdivisionEdgeEnd P x S (subdivisionHorizontalEdge P x S f i row)=
      subdivisionGridVertex P x S f (finSuccGrid i) row := by
  exact (subdivisionHorizontalEdge_end P x S f i row).trans
    (congrArg (fun a : Fin (S.half+1) => subdivisionGridVertex P x S f a row) (by apply Fin.ext; rfl))
theorem own_vertical_start (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) (column : Fin (S.half+1)) (i : Fin S.half) :
    subdivisionEdgeStart P x S (subdivisionVerticalEdge P x S f column i)=
      subdivisionGridVertex P x S f column (finCastGrid i) := by
  exact (subdivisionVerticalEdge_start P x S f column i).trans
    (congrArg (fun a : Fin (S.half+1) => subdivisionGridVertex P x S f column a) (by apply Fin.ext; rfl))
theorem own_vertical_end (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) (column : Fin (S.half+1)) (i : Fin S.half) :
    subdivisionEdgeEnd P x S (subdivisionVerticalEdge P x S f column i)=
      subdivisionGridVertex P x S f column (finSuccGrid i) := by
  exact (subdivisionVerticalEdge_end P x S f column i).trans
    (congrArg (fun a : Fin (S.half+1) => subdivisionGridVertex P x S f column a) (by apply Fin.ext; rfl))
def finInteriorGrid (S : OddScale) (i : Fin (S.half-1)) : Fin (S.half+1) :=
  ⟨i.val+1,by have := S.half_pos; have := i.isLt; omega⟩
def finInteriorIndex (S : OddScale) (i : Fin (S.half+1))
    (h0 : i.val≠0) (hh : i.val≠S.half) : Fin (S.half-1) :=
  ⟨i.val-1,by have := i.isLt; omega⟩
abbrev Seed (S : OddScale) := Σ r : (RawOne S).Q,
  Σ e : QDoubleCylinderEdge (transposePresentation (RawOne S)) r S,
    DoubleCylinderEdge (state S 2).presentation (c2QEdgeOwner S r e) S
def extractC3 (S : OddScale) (q : Physical S 3) : Option (Seed S) :=
  match (BDL26RXDecoderAdapter.rxPhysicalQEquiv S 3 ⟨2,by omega⟩ (by decide)).symm q with
  | .inl ⟨.inl (.inr ⟨r,e⟩),d⟩ => some ⟨r,e,d⟩
  | _ => none
def extractC4 (S : OddScale) (q : Physical S 4) : Option (Physical S 3) :=
  match (BDL26RZPhysicalStarTransport.upperQChart S 4 ⟨3,by omega⟩ (by decide)).symm q with
  | .inr ⟨q,_⟩ => some q
  | .inl _ => none
def seedQ (j : Fin 2) : BaseQubit := ⟨j.val,by omega⟩
def seedRadial (j : Fin 2) : XStarEdge baseTannerSquarePresentation (0 : BaseX) :=
  ⟨.inl ⟨(0,seedQ j),by fin_cases j <;> decide⟩,by fin_cases j <;> decide⟩
def seedCenter : XStarVertex baseTannerSquarePresentation (0 : BaseX) :=
  ⟨Vertex.x 0,by decide⟩
def seedQVertex (j : Fin 2) : XStarVertex baseTannerSquarePresentation (0 : BaseX) :=
  ⟨Vertex.q (seedQ j),by fin_cases j <;> decide⟩
theorem seedRadial_end (j : Fin 2) :
    xStarEdgeEnd _ _ (seedRadial j)=seedQVertex j := by fin_cases j <;> rfl
def seedFace (j : Fin 2) : XStarFace baseTannerSquarePresentation (0 : BaseX) :=
  ⟨⟨j.val,by omega⟩,by fin_cases j <;> decide⟩
theorem seedRadial_face_zero : ∀ (j : Fin 2)
    (f : XStarFace baseTannerSquarePresentation (0 : BaseX)),
    seedRadial j=xStarFaceXQEdge _ _ f 0 ↔ f=seedFace j := by decide
theorem seedRadial_face_one : ∀ (j : Fin 2)
    (f : XStarFace baseTannerSquarePresentation (0 : BaseX)),
    seedRadial j≠xStarFaceXQEdge _ _ f 1 := by decide
theorem seedRadial_ne_qz (j : Fin 2)
    (f : XStarFace baseTannerSquarePresentation (0 : BaseX))
    (c : BDL26FiniteTannerSquare.Two) : seedRadial j≠xStarFaceQZEdge _ _ f c := by
  intro h
  have hv := congrArg Subtype.val h
  cases hv
theorem seedRadial_horizontal (S : OddScale) (j : Fin 2) (i : Fin S.half)
    (f : XStarFace baseTannerSquarePresentation (0 : BaseX))
    (a : Fin S.half) (b : Fin (S.half+1)) :
    (.inl (seedRadial j,i) : SubdivisionEdge baseTannerSquarePresentation (0 : BaseX) S)=
        subdivisionHorizontalEdge _ _ S f a b ↔
      f=seedFace j ∧ i=a ∧ b.val=0 := by
  by_cases hb0 : b.val=0
  · simp [subdivisionHorizontalEdge,hb0,seedRadial_face_zero]
  · by_cases hbm : b.val=S.half
    · have hm0 : S.half≠0 := S.half_pos.ne'
      simp [subdivisionHorizontalEdge,hb0,hbm,hm0,seedRadial_ne_qz]
    · simp [subdivisionHorizontalEdge,hb0,hbm]
theorem seedRadial_vertical (S : OddScale) (j : Fin 2) (i : Fin S.half)
    (f : XStarFace baseTannerSquarePresentation (0 : BaseX))
    (a : Fin (S.half+1)) (b : Fin S.half) :
    (.inl (seedRadial j,i) : SubdivisionEdge baseTannerSquarePresentation (0 : BaseX) S)≠
      subdivisionVerticalEdge _ _ S f a b := by
  unfold subdivisionVerticalEdge
  split_ifs <;> simp [seedRadial_face_one,seedRadial_ne_qz]
theorem face_matrix_expanded (T : TannerSquarePresentation) (x : T.X)
    (S : OddScale) (e : SubdivisionEdge T x S) (f : XStarFace T x)
    (a b : Fin S.half) :
    subdivisionFaceEdgeMatrix T x S e (f,a,b)=
      (((if e=subdivisionHorizontalEdge T x S f a (finCastGrid b) then (1:F) else 0)+
        (if e=subdivisionVerticalEdge T x S f (finSuccGrid a) b then 1 else 0))+
        (if e=subdivisionHorizontalEdge T x S f a (finSuccGrid b) then 1 else 0))+
        (if e=subdivisionVerticalEdge T x S f (finCastGrid a) b then 1 else 0) := rfl
theorem seedRadial_localMatrix (S : OddScale) (j : Fin 2) (i : Fin S.half)
    (f : SubdivisionFace baseTannerSquarePresentation (0 : BaseX) S) :
    subdivisionFaceEdgeMatrix baseTannerSquarePresentation (0 : BaseX) S
        (.inl (seedRadial j,i)) f=
      if f=(seedFace j,i,⟨0,S.half_pos⟩) then 1 else 0 := by
  rcases f with ⟨f,a,b⟩
  have hv0 := seedRadial_vertical S j i f (finSuccGrid a) b
  have hv1 := seedRadial_vertical S j i f (finCastGrid a) b
  have ht : ¬(.inl (seedRadial j,i) :
      SubdivisionEdge baseTannerSquarePresentation (0 : BaseX) S)=
        subdivisionHorizontalEdge _ _ S f a (finSuccGrid b) := by
    erw [seedRadial_horizontal]
    simp [finSuccGrid]
  have hb : ((.inl (seedRadial j,i) :
      SubdivisionEdge baseTannerSquarePresentation (0 : BaseX) S)=
        subdivisionHorizontalEdge _ _ S f a (finCastGrid b)) ↔
      (f,a,b)=(seedFace j,i,⟨0,S.half_pos⟩) := by
    erw [seedRadial_horizontal]
    simp [finCastGrid,Fin.ext_iff,eq_comm,and_assoc]
  erw [face_matrix_expanded]
  simp only [if_neg hv0,if_neg ht,if_neg hv1,add_zero]
  exact indicator_iff _ _ hb
def seedRadialCheck (S : OddScale) (j : Fin 2) (i : Fin S.half) : (RawOne S).Z :=
  .inl (.inl ⟨(0 : BaseX),.inl (0,(seedFace j,i,⟨0,S.half_pos⟩))⟩)
theorem seedRadial_qEdge_zero (S : OddScale) (j : Fin 2) (i : Fin S.half)
    (q : BaseQubit) (e : QDoubleCylinderEdge baseTannerSquarePresentation q S) :
    qDoubleCylinderEdgeXIncidence baseTannerSquarePresentation q 0 S
      (.inl (0,.inl (seedRadial j,i))) e=0 := by
  unfold qDoubleCylinderEdgeXIncidence
  by_cases hxq : baseTannerSquarePresentation.xq (0 : BaseX) q=true
  · erw [dif_pos hxq]
    have hn : (.inl (0,.inl (seedRadial j,i)) :
        DoubleCylinderEdge baseTannerSquarePresentation (0 : BaseX) S)≠
        qToXDoubleCylinderEdgeRaw baseTannerSquarePresentation q 0 hxq S e := by
      rcases e with ⟨c,z,k⟩ | z
      · intro he
        have tag := congrArg (fun edge : DoubleCylinderEdge
            baseTannerSquarePresentation (0 : BaseX) S =>
          match edge with
          | .inl (_, .inl (a,_)) => match a.val with
              | .inl _ => true
              | .inr _ => false
          | _ => false) he
        change true=false at tag
        cases tag
      · intro he
        cases he
    erw [if_neg hn]
  · erw [dif_neg hxq]
theorem rx_local_column_indicator (P : TannerSquarePresentation)
    (S : OddScale) (x0 : P.X) (edge : DoubleCylinderEdge P x0 S)
    (face : DoubleCylinderFace P x0 S)
    (hl : ∀ f, doubleCylinderFaceEdgeMatrix P x0 S edge f=
      if f=face then 1 else 0)
    (hq : ∀ (q : P.Q) (e : QDoubleCylinderEdge P q S),
      qDoubleCylinderEdgeXIncidence P q x0 S edge e=0) (z : RX2 P S) :
    rxBoundary2Matrix P S (.inl ⟨x0,edge⟩) z=
      if z=(.inl (.inl ⟨x0,face⟩) : RX2 P S) then 1 else 0 := by
  classical
  rcases z with (⟨x,f⟩ | ⟨q,e⟩) | ⟨z,c⟩
  · by_cases h : x0=x
    · subst x
      simp [rxBoundary2Matrix,hl,Sigma.mk.injEq]
    · simp [rxBoundary2Matrix,h,Ne.symm h,Sigma.mk.injEq]
  · simp [rxBoundary2Matrix,hq]
  · simp [rxBoundary2Matrix]
theorem rx_q_column_indicator (P : TannerSquarePresentation)
    (S : OddScale) (q0 : P.Q) (vertex : QDoubleCylinderVertex P q0 S)
    (edge : QDoubleCylinderEdge P q0 S)
    (hq : ∀ e, qDoubleCylinderEdgeVertexIncidence P q0 S vertex e=
      if e=edge then 1 else 0)
    (hz : ∀ z, qDoubleCylinderVertexZIncidence P q0 S vertex z=0)
    (z : RX2 P S) :
    rxBoundary2Matrix P S (.inr ⟨q0,vertex⟩) z=
      if z=(.inl (.inr ⟨q0,edge⟩) : RX2 P S) then 1 else 0 := by
  classical
  rcases z with (⟨x,f⟩ | ⟨q,e⟩) | ⟨z,c⟩
  · simp [rxBoundary2Matrix]
  · by_cases h : q0=q
    · subst q
      simp [rxBoundary2Matrix,hq,Sigma.mk.injEq]
    · simp [rxBoundary2Matrix,h,Ne.symm h,Sigma.mk.injEq]
  · simp [rxBoundary2Matrix,hz]
theorem raw_boundary1_view (S : OddScale) (x : (RawOne S).X)
    (r : (RawOne S).Q) :
    rxBoundary1Matrix baseTannerSquarePresentation S x r=
      if (RawOne S).xq x r=true then (1:F) else 0 := by
  exact rxPresentation_boundary1Matrix_eq baseTannerSquarePresentation
    baseTannerSquareAdmissibleV4 S x r
theorem raw_boundary2_view (S : OddScale) (r : (RawOne S).Q)
    (z : (RawOne S).Z) :
    rxBoundary2Matrix baseTannerSquarePresentation S r z=
      if (RawOne S).qz r z=true then (1:F) else 0 := by
  exact rxPresentation_boundary2Matrix_eq baseTannerSquarePresentation
    baseTannerSquareAdmissibleV4 S r z
theorem seedRadial_matrix (S : OddScale) (j : Fin 2) (i : Fin S.half)
    (z : (RawOne S).Z) :
    rxBoundary2Matrix baseTannerSquarePresentation S
        (.inl ⟨(0 : BaseX),.inl (0,.inl (seedRadial j,i))⟩) z=
      if z=seedRadialCheck S j i then 1 else 0 := by
  have hl : ∀ f, doubleCylinderFaceEdgeMatrix baseTannerSquarePresentation (0 : BaseX) S
      (.inl (0,.inl (seedRadial j,i))) f=
        if f=(.inl (0,(seedFace j,i,⟨0,S.half_pos⟩))) then 1 else 0 := by
    intro f
    rcases f with ⟨c,f⟩ | b
    · by_cases hc : c=0
      · subst c
        change subdivisionFaceEdgeMatrix baseTannerSquarePresentation (0 : BaseX) S
          (.inl (seedRadial j,i)) f=
            if (Sum.inl (0,f) : DoubleCylinderFace baseTannerSquarePresentation (0 : BaseX) S)=
                .inl (0,(seedFace j,i,⟨0,S.half_pos⟩)) then 1 else 0
        have hm := seedRadial_localMatrix S j i f
        apply hm.trans
        apply indicator_iff
        constructor
        · intro hf
          exact congrArg (fun g : SubdivisionFace baseTannerSquarePresentation (0 : BaseX) S =>
            (Sum.inl ((0 : BDL26FiniteTannerSquare.Two),g) :
              DoubleCylinderFace baseTannerSquarePresentation (0 : BaseX) S)) hf
        · intro he
          exact congrArg Prod.snd (Sum.inl.inj he)
      · simp only [doubleCylinderFaceEdgeMatrix,if_neg (Ne.symm hc),
          Sum.inl.injEq,Prod.mk.injEq,hc,false_and,if_false]
    · have hb : (.inl (seedRadial j,i) :
          SubdivisionEdge baseTannerSquarePresentation (0 : BaseX) S)≠b.val := by
        intro he
        have hm := b.property
        erw [← he] at hm
        change xStarBoundaryEdgeMember baseTannerSquarePresentation (0 : BaseX)
          (seedRadial j).val=true at hm
        change false=true at hm
        cases hm
      simp only [doubleCylinderFaceEdgeMatrix,Sum.inr_ne_inl,if_false]
      exact if_neg hb
  have hm := rx_local_column_indicator baseTannerSquarePresentation S
    (0 : BaseX) (.inl (0,.inl (seedRadial j,i)))
    (.inl (0,(seedFace j,i,⟨0,S.half_pos⟩))) hl (seedRadial_qEdge_zero S j i) z
  convert hm using 1 <;> congr 1
theorem seedRadial_degree_one (S : OddScale) (j : Fin 2) (i : Fin S.half) :
    (RawOne S).qz (.inl ⟨(0 : BaseX),.inl (0,.inl (seedRadial j,i))⟩)
        (seedRadialCheck S j i)=true ∧
      ∀ z : (RawOne S).Z,
        (RawOne S).qz (.inl ⟨(0 : BaseX),.inl (0,.inl (seedRadial j,i))⟩) z=true →
          z=seedRadialCheck S j i := by
  have hi (z : (RawOne S).Z) := rxPresentation_boundary2Matrix_eq
    baseTannerSquarePresentation baseTannerSquareAdmissibleV4 S
      (.inl ⟨(0 : BaseX),.inl (0,.inl (seedRadial j,i))⟩) z
  constructor
  · have ht := hi (seedRadialCheck S j i)
    change _=(if (RawOne S).qz (.inl ⟨(0 : BaseX),.inl (0,.inl (seedRadial j,i))⟩) (seedRadialCheck S j i)=true then (1:F) else 0) at ht
    erw [seedRadial_matrix,if_pos rfl] at ht
    by_contra hn
    rw [if_neg hn] at ht
    exact one_ne_zero ht
  · intro z hz
    have ht := hi z
    change _=(if (RawOne S).qz (.inl ⟨(0 : BaseX),.inl (0,.inl (seedRadial j,i))⟩) z=true then (1:F) else 0) at ht
    erw [seedRadial_matrix,if_pos hz] at ht
    by_contra hn
    rw [if_neg hn] at ht
    exact one_ne_zero ht.symm
def seedZEdge (j : Fin 2) : QStarEdge baseTannerSquarePresentation (seedQ j) :=
  ⟨j,by fin_cases j <;> decide⟩
theorem seedZEdge_unique (j : Fin 2)
    (z : QStarEdge baseTannerSquarePresentation (seedQ j)) : z=seedZEdge j := by
  fin_cases j
  · exact (by decide : ∀ z : QStarEdge baseTannerSquarePresentation (seedQ 0),
      z=seedZEdge 0) z
  · exact (by decide : ∀ z : QStarEdge baseTannerSquarePresentation (seedQ 1),
      z=seedZEdge 1) z
def seedConeCheck (S : OddScale) (j : Fin 2) : (RawOne S).Z :=
  .inl (.inr ⟨seedQ j,.inl (0,(seedZEdge j,⟨0,S.half_pos⟩))⟩)
theorem seedCone_matrix (S : OddScale) (j : Fin 2) (z : (RawOne S).Z) :
    rxBoundary2Matrix baseTannerSquarePresentation S
        (.inr ⟨seedQ j,(0,.inl (.inl ()))⟩) z=
      if z=seedConeCheck S j then 1 else 0 := by
  have hq : ∀ e, qDoubleCylinderEdgeVertexIncidence baseTannerSquarePresentation
      (seedQ j) S (0,.inl (.inl ())) e=
        if e=(.inl (0,(seedZEdge j,⟨0,S.half_pos⟩))) then 1 else 0 := by
    intro e
    rcases e with ⟨c,z,i⟩ | z
    · have hz := seedZEdge_unique j z
      subst z
      fin_cases c <;> by_cases hi : i.val=0 <;> by_cases hm : i.val+1=S.half <;>
        simp_all [qDoubleCylinderEdgeVertexIncidence,
          qDoubleCylinderEdgeStart,qDoubleCylinderEdgeEnd,qSubdivisionEdgeStart,
          qSubdivisionEdgeEnd,qStarEdgeStart,qStarEdgeEnd,
          S.half_pos.ne',Ne.symm S.half_pos.ne',hi,hm,Fin.ext_iff]
    · simp [qDoubleCylinderEdgeVertexIncidence,qDoubleCylinderEdgeStart,
        qDoubleCylinderEdgeEnd,qStarEdgeEnd]
  have hz : ∀ z, qDoubleCylinderVertexZIncidence baseTannerSquarePresentation
      (seedQ j) S (0,.inl (.inl ())) z=0 := by
    intro z
    simp [qDoubleCylinderVertexZIncidence]
  have hm := rx_q_column_indicator baseTannerSquarePresentation S (seedQ j)
    (0,.inl (.inl ())) (.inl (0,(seedZEdge j,⟨0,S.half_pos⟩))) hq hz z
  convert hm using 1 <;> congr 1
theorem seedCone_degree_one (S : OddScale) (j : Fin 2) :
    (RawOne S).qz (.inr ⟨seedQ j,(0,.inl (.inl ()))⟩) (seedConeCheck S j)=true ∧
      ∀ z : (RawOne S).Z,
        (RawOne S).qz (.inr ⟨seedQ j,(0,.inl (.inl ()))⟩) z=true → z=seedConeCheck S j := by
  have hi (z : (RawOne S).Z) := rxPresentation_boundary2Matrix_eq
    baseTannerSquarePresentation baseTannerSquareAdmissibleV4 S
      (.inr ⟨seedQ j,(0,.inl (.inl ()))⟩) z
  constructor
  · have ht := hi (seedConeCheck S j)
    change _=(if (RawOne S).qz (.inr ⟨seedQ j,(0,.inl (.inl ()))⟩) (seedConeCheck S j)=true then (1:F) else 0) at ht
    erw [seedCone_matrix,if_pos rfl] at ht
    by_contra hn
    rw [if_neg hn] at ht
    exact one_ne_zero ht
  · intro z hz
    have ht := hi z
    change _=(if (RawOne S).qz (.inr ⟨seedQ j,(0,.inl (.inl ()))⟩) z=true then (1:F) else 0) at ht
    erw [seedCone_matrix,if_pos hz] at ht
    by_contra hn
    rw [if_neg hn] at ht
    exact one_ne_zero ht.symm
def radialNode (S : OddScale) (j : Fin 2) (n : Nat) (hn : n≤S.half) :
    SubdivisionVertex baseTannerSquarePresentation (0 : BaseX) S :=
  if h0 : n=0 then .inl (xStarEdgeStart _ _ (seedRadial j))
  else if hm : n=S.half then .inl (xStarEdgeEnd _ _ (seedRadial j))
  else .inr (.inl (seedRadial j,⟨n-1,by omega⟩))
noncomputable def radialPath (S : OddScale) (j : Fin 2) :
    (n : Nat) → (hn : n≤S.half) →
      UndirectedPath
        (tannerDoubleCylinderEdgeStart baseTannerSquarePresentation (0 : BaseX) S)
        (tannerDoubleCylinderEdgeEnd baseTannerSquarePresentation (0 : BaseX) S)
        (0,.inl (xStarEdgeStart _ _ (seedRadial j))) (0,radialNode S j n hn)
  | 0,_ => .nil
  | n+1,hn => by
    let i : Fin S.half := ⟨n,by omega⟩
    apply UndirectedPath.step (radialPath S j n (by omega))
      (.inl (0,.inl (seedRadial j,i)))
    apply Or.inl
    constructor
    · have hm : n≠S.half := by omega
      simp [tannerDoubleCylinderEdgeStart,subdivisionEdgeStart,
        subdivisionSegmentStart,radialNode,i,hm]
    · simp [tannerDoubleCylinderEdgeEnd,subdivisionEdgeEnd,
        subdivisionSegmentEnd,radialNode,i]
def radialChain (S : OddScale) (j : Fin 2) :
    Word F (DoubleCylinderEdge baseTannerSquarePresentation (0 : BaseX) S) :=
  pathChain (radialPath S j S.half (Nat.le_refl _))
def coordinateMap {I : Type} (i : I) : Word F I →ₗ[F] F where
  toFun w := w i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def rawDualReadout (S : OddScale) : Word F (RawOne S).Q →ₗ[F] F :=
  coordinateMap (.inr ⟨(0 : BaseQubit),(0,.inl (.inl ()))⟩)+
    coordinateMap (.inr ⟨(1 : BaseQubit),(0,.inl (.inl ()))⟩)+
    (wordPairing (radialChain S 0+radialChain S 1)).comp
      (wordPullback (fun e => (.inl ⟨(0 : BaseX),e⟩ : (RawOne S).Q)))
theorem rx_cone_single_incidence (P : TannerSquarePresentation)
    (S : OddScale) (q : P.Q) (x0 : P.X) (v0 : XStarVertex P x0)
    (hv0 : v0.val=Vertex.q q)
    (hxq : ∀ x, P.xq x q=true ↔ x=x0) (v : RX0 P S) :
    rxBoundary1Matrix P S v (.inr ⟨q,(0,.inl (.inl ()))⟩)=
      if v=⟨x0,(0,.inl v0)⟩ then 1 else 0 := by
  classical
  rcases v with ⟨x,c,v⟩
  by_cases hx : x=x0
  · subst x
    by_cases hc : c=0
    · subst c
      rcases v with v | v | v <;>
        simp [rxBoundary1Matrix,qDoubleCylinderVertexXIncidence,
          qSubdivisionVertexXIncidence,(hxq x0).mpr rfl,hv0,
          Subtype.ext_iff,Sigma.mk.injEq]
    · simp [rxBoundary1Matrix,qDoubleCylinderVertexXIncidence,hc,Sigma.mk.injEq]
  · simp [rxBoundary1Matrix,qDoubleCylinderVertexXIncidence,
      qSubdivisionVertexXIncidence,hxq,hx,Ne.symm hx,Sigma.mk.injEq]
theorem seedQ_unique_x : ∀ (j : Fin 2) (x : BaseX),
    baseTannerSquarePresentation.xq x (seedQ j)=true ↔ x=0 := by decide
theorem seed_cone_incidence (S : OddScale) (j : Fin 2)
    (v : RX0 baseTannerSquarePresentation S) :
    rxBoundary1Matrix baseTannerSquarePresentation S v
        (.inr ⟨seedQ j,(0,.inl (.inl ()))⟩)=
      if v=⟨0,(0,.inl (seedQVertex j))⟩ then 1 else 0 := by
  exact rx_cone_single_incidence baseTannerSquarePresentation S (seedQ j)
    (0 : BaseX) (seedQVertex j) rfl (seedQ_unique_x j) v
def dualReadout (S : OddScale) : Word F (RawTwo S).Q →ₗ[F] F :=
  (rawDualReadout S).comp (BDL26LevelTwoDistance.rzQParity (RawOne S) S)
theorem executableLevelOne_eq_raw (S : OddScale) :
    BDL26LevelTwoDecoder.executableLevelOne S=RawOne S := by
  exact (BDL26LevelTwoDecoder.executableLevelOne_eq S).trans rfl
def executableCoordinate (S : OddScale) (q : (levelTwoPresentation S).Q) :
    BDL26LevelTwoDecoder.ExecutableQ S :=
  cast (BDL26LevelTwoDecoder.executableQ_eq S).symm q
theorem cast_xq {P Q : TannerSquarePresentation} (h : P=Q)
    (r : Q.Q) (x : Q.X) (hx : Q.xq x r=true) :
    P.xq (cast (congrArg TannerSquarePresentation.X h).symm x)
      (cast (congrArg TannerSquarePresentation.Q h).symm r)=true := by
  cases h
  exact hx
theorem cast_qz {P Q : TannerSquarePresentation} (h : P=Q)
    (r : Q.Q) (z : Q.Z) (hz : Q.qz r z=true) :
    P.qz (cast (congrArg TannerSquarePresentation.Q h).symm r)
      (cast (congrArg TannerSquarePresentation.Z h).symm z)=true := by
  cases h
  exact hz
def firstQEdge (S : OddScale) (r : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (c : BDL26FiniteTannerSquare.Two) :
    QDoubleCylinderEdge (transposePresentation (RawOne S)) r S :=
  .inl (c,(⟨x,hx⟩,⟨0,S.half_pos⟩))
def firstRadialQ (S : OddScale) : (RawOne S).Q :=
  .inl ⟨(0 : BaseX),.inl (0,.inl (seedRadial 0,⟨0,S.half_pos⟩))⟩
def lastSegment (S : OddScale) : Fin S.half :=
  ⟨S.half-1,by have := S.half_pos; omega⟩
def lastQEdge (S : OddScale) (r : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (c : BDL26FiniteTannerSquare.Two) :
    QDoubleCylinderEdge (transposePresentation (RawOne S)) r S :=
  .inl (c,(⟨x,hx⟩,⟨S.half-1,by have := S.half_pos; omega⟩))
def lastInterior (S : OddScale) (h : 2≤S.half) : Fin (S.half-1) :=
  ⟨S.half-2,by omega⟩
def shiftedOldXPotential (S : OddScale) (x : (RawOne S).X)
    (c : BDL26FiniteTannerSquare.Two) : Word F (RawTwo S).X :=
  canonicalBasisWord (.inr (x,c)) +
    ∑ r : (RawOne S).Q, if hx : (RawOne S).xq x r=true then
      canonicalBasisWord (.inl (.inr ⟨r,lastQEdge S r x hx c⟩)) else 0
def interiorQEdge (S : OddScale) (r : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (c : BDL26FiniteTannerSquare.Two) (i : Fin (S.half-1)) :
    QDoubleCylinderEdge (transposePresentation (RawOne S)) r S :=
  .inl (c,(⟨x,hx⟩,⟨i.val+1,by have := i.isLt; omega⟩))
def closed_word_cocycle (P : TannerSquarePresentation) (w : Word F P.Q)
    (hw : tannerCoboundary1 P w=0) : BDL26RZCohomology.Cocycle P :=
  ⟨w,(BDL26RZCohomology.mem_cocycle_iff P w).mpr hw⟩
def gridAt (S : OddScale) (n : Nat) (h : n≤S.half) : Fin (S.half+1) :=
  ⟨n,by omega⟩
noncomputable def verticalAtColumnPath (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (column : Fin (S.half+1)) :
    (n : Nat) → (hn : n≤S.half) →
      UndirectedPath (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
        (subdivisionGridVertex P x S f column 0)
        (subdivisionGridVertex P x S f column (gridAt S n hn))
  | 0,_ => .nil
  | n+1,hn => by
    let k : Fin S.half := ⟨n,by omega⟩
    apply UndirectedPath.step (verticalAtColumnPath P x S f column n (by omega))
      (subdivisionVerticalEdge P x S f column k)
    apply Or.inl
    constructor
    · exact own_vertical_start P x S f column k
    · exact own_vertical_end P x S f column k
noncomputable def horizontalAtRowPath (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (row : Fin (S.half+1)) :
    (n : Nat) → (hn : n≤S.half) →
      UndirectedPath (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
        (subdivisionGridVertex P x S f 0 row)
        (subdivisionGridVertex P x S f (gridAt S n hn) row)
  | 0,_ => .nil
  | n+1,hn => by
    let k : Fin S.half := ⟨n,by omega⟩
    apply UndirectedPath.step (horizontalAtRowPath P x S f row n (by omega))
      (subdivisionHorizontalEdge P x S f k row)
    apply Or.inl
    constructor
    · exact own_horizontal_start P x S f k row
    · exact own_horizontal_end P x S f k row
theorem verticalAtColumnPath_support (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (column : Fin (S.half+1))
    (n : Nat) (hn : n≤S.half) (e : SubdivisionEdge P x S)
    (he : pathChain (verticalAtColumnPath P x S f column n hn) e≠0) :
    ∃ k : Fin S.half, k.val<n ∧ e=subdivisionVerticalEdge P x S f column k := by
  revert hn
  induction n with
  | zero => intro hn he; simp [verticalAtColumnPath,pathChain] at he
  | succ n ih =>
    intro hn he
    let k : Fin S.half := ⟨n,by omega⟩
    have hs : pathChain (verticalAtColumnPath P x S f column (n+1) hn)=
        pathChain (verticalAtColumnPath P x S f column n (by omega))+
          Pi.single (subdivisionVerticalEdge P x S f column k) (1:F) := rfl
    rw [hs,Pi.add_apply] at he
    by_cases hp : pathChain (verticalAtColumnPath P x S f column n (by omega)) e=0
    · rw [hp,zero_add,Pi.single_apply] at he
      by_cases hq : e=subdivisionVerticalEdge P x S f column k
      · exact ⟨k,by dsimp [k]; omega,hq⟩
      · exact False.elim (he (if_neg hq))
    · obtain ⟨k,hk,hq⟩ := ih (by omega) hp
      exact ⟨k,by omega,hq⟩
theorem horizontalAtRowPath_support (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (row : Fin (S.half+1))
    (n : Nat) (hn : n≤S.half) (e : SubdivisionEdge P x S)
    (he : pathChain (horizontalAtRowPath P x S f row n hn) e≠0) :
    ∃ k : Fin S.half, k.val<n ∧ e=subdivisionHorizontalEdge P x S f k row := by
  revert hn
  induction n with
  | zero => intro hn he; simp [horizontalAtRowPath,pathChain] at he
  | succ n ih =>
    intro hn he
    let k : Fin S.half := ⟨n,by omega⟩
    have hs : pathChain (horizontalAtRowPath P x S f row (n+1) hn)=
        pathChain (horizontalAtRowPath P x S f row n (by omega))+
          Pi.single (subdivisionHorizontalEdge P x S f k row) (1:F) := rfl
    rw [hs,Pi.add_apply] at he
    by_cases hp : pathChain (horizontalAtRowPath P x S f row n (by omega)) e=0
    · rw [hp,zero_add,Pi.single_apply] at he
      by_cases hq : e=subdivisionHorizontalEdge P x S f k row
      · exact ⟨k,by dsimp [k]; omega,hq⟩
      · exact False.elim (he (if_neg hq))
    · obtain ⟨k,hk,hq⟩ := ih (by omega) hp
      exact ⟨k,by omega,hq⟩
def lastGridInterior (S : OddScale) : Fin (S.half+1) :=
  ⟨S.half-1,by omega⟩
noncomputable def shiftedFacePath0 (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (i : Fin (S.half-1)) :
    UndirectedPath (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
      (subdivisionGridVertex P x S f (lastGridInterior S) 0)
      (subdivisionGridVertex P x S f (gridAt S S.half le_rfl)
        (gridAt S (i.val+1) (by have := i.isLt; omega))) := by
  let t := gridAt S (i.val+1) (by have := i.isLt; omega)
  apply UndirectedPath.step
    (verticalAtColumnPath P x S f (lastGridInterior S) (i.val+1)
      (by have := i.isLt; omega))
    (subdivisionHorizontalEdge P x S f (lastSegment S) t)
  apply Or.inl
  constructor
  · have hs : subdivisionEdgeStart P x S
        (subdivisionHorizontalEdge P x S f (lastSegment S) t)=
        subdivisionGridVertex P x S f (finCastGrid (lastSegment S)) t :=
      own_horizontal_start P x S f (lastSegment S) t
    exact hs.trans (congrArg (fun v => subdivisionGridVertex P x S f v t)
      (show finCastGrid (lastSegment S)=lastGridInterior S from rfl))
  · have hs : subdivisionEdgeEnd P x S
        (subdivisionHorizontalEdge P x S f (lastSegment S) t)=
        subdivisionGridVertex P x S f (finSuccGrid (lastSegment S)) t :=
      own_horizontal_end P x S f (lastSegment S) t
    exact hs.trans (congrArg (fun v => subdivisionGridVertex P x S f v t)
      (by apply Fin.ext; dsimp [finSuccGrid,lastSegment,gridAt]; have := S.half_pos; omega))
noncomputable def shiftedFacePath1 (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (i : Fin (S.half-1)) :
    UndirectedPath (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
      (subdivisionGridVertex P x S f 0 (lastGridInterior S))
      (subdivisionGridVertex P x S f
        (gridAt S (i.val+1) (by have := i.isLt; omega)) (gridAt S S.half le_rfl)) := by
  let t := gridAt S (i.val+1) (by have := i.isLt; omega)
  apply UndirectedPath.step
    (horizontalAtRowPath P x S f (lastGridInterior S) (i.val+1)
      (by have := i.isLt; omega))
    (subdivisionVerticalEdge P x S f t (lastSegment S))
  apply Or.inl
  constructor
  · have hs : subdivisionEdgeStart P x S
        (subdivisionVerticalEdge P x S f t (lastSegment S))=
        subdivisionGridVertex P x S f t (finCastGrid (lastSegment S)) :=
      own_vertical_start P x S f t (lastSegment S)
    exact hs.trans (congrArg (fun v => subdivisionGridVertex P x S f t v)
      (show finCastGrid (lastSegment S)=lastGridInterior S from rfl))
  · have hs : subdivisionEdgeEnd P x S
        (subdivisionVerticalEdge P x S f t (lastSegment S))=
        subdivisionGridVertex P x S f t (finSuccGrid (lastSegment S)) :=
      own_vertical_end P x S f t (lastSegment S)
    exact hs.trans (congrArg (fun v => subdivisionGridVertex P x S f t v)
      (by apply Fin.ext; dsimp [finSuccGrid,lastSegment,gridAt]; have := S.half_pos; omega))
theorem qToZ_face_boundary_edge (P : TannerSquarePresentation)
    (z : P.Z) (f : XStarFace (transposePresentation P) z)
    (j : BDL26FiniteTannerSquare.Two)
    (hz : P.qz (P.faceQ f.val j) z=true) :
    xStarBoundaryEdgeToStar (transposePresentation P) z
      ((transposeXStarBoundaryEdgeEquiv P z).symm
        (qToZBoundaryEdge P (P.faceQ f.val j) z hz
          ⟨P.faceX f.val,P.data.faceQ_xq f.val j⟩))=
      xStarFaceQZEdge (transposePresentation P) z f j := by
  apply Subtype.ext
  rfl
theorem qToZ_face_interior0 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (z : P.Z)
    (f : XStarFace (transposePresentation P) z)
    (hz : P.qz (P.faceQ f.val 0) z=true) (S : OddScale) (i : Fin (S.half-1)) :
    qToZSubdivisionVertex P A (P.faceQ f.val 0) z hz S
      (.inr (⟨P.faceX f.val,P.data.faceQ_xq f.val 0⟩,i))=
      subdivisionGridVertex (transposePresentation P) z S f
        (gridAt S S.half le_rfl)
        (gridAt S (i.val+1) (by have := i.isLt; omega)) := by
  rw [show subdivisionGridVertex (transposePresentation P) z S f
      (gridAt S S.half le_rfl)
      (gridAt S (i.val+1) (by have := i.isLt; omega))=
        .inr (.inl (xStarFaceQZEdge (transposePresentation P) z f 0,i)) by
    exact subdivisionGridVertex_edgeInterior_qz0 (transposePresentation P) z S f i]
  change (Sum.inr (Sum.inl (_,i)) :
    SubdivisionVertex (transposePresentation P) z S)=Sum.inr (Sum.inl (_,i))
  rw [qToZ_face_boundary_edge]
theorem qToZ_face_interior1 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (z : P.Z)
    (f : XStarFace (transposePresentation P) z)
    (hz : P.qz (P.faceQ f.val 1) z=true) (S : OddScale) (i : Fin (S.half-1)) :
    qToZSubdivisionVertex P A (P.faceQ f.val 1) z hz S
      (.inr (⟨P.faceX f.val,P.data.faceQ_xq f.val 1⟩,i))=
      subdivisionGridVertex (transposePresentation P) z S f
        (gridAt S (i.val+1) (by have := i.isLt; omega))
        (gridAt S S.half le_rfl) := by
  rw [show subdivisionGridVertex (transposePresentation P) z S f
      (gridAt S (i.val+1) (by have := i.isLt; omega))
      (gridAt S S.half le_rfl)=
        .inr (.inl (xStarFaceQZEdge (transposePresentation P) z f 1,i)) by
    exact subdivisionGridVertex_edgeInterior_qz1 (transposePresentation P) z S f i]
  change (Sum.inr (Sum.inl (_,i)) :
    SubdivisionVertex (transposePresentation P) z S)=Sum.inr (Sum.inl (_,i))
  rw [qToZ_face_boundary_edge]
def twoArmKernel (S : OddScale)
    (r r' : (RawOne S).Q) (z : (RawOne S).Z)
    (hz : (RawOne S).qz r z=true) (hz' : (RawOne S).qz r' z=true)
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
    Word F (RawTwo S).Q :=
  canonicalBasisWord (.inr ⟨r,v⟩)+canonicalBasisWord (.inr ⟨r',v'⟩)+
    extendZEdgeWord (RawOne S) S z (pathChain p+pathChain p')
def stripQ (j : Fin 2) (x : BaseX) : BaseQubit :=
  ⟨j.val+2*x.val,by have := j.isLt; have := x.isLt; omega⟩
def stripMember (j : Fin 2) (x : BaseX) (S : OddScale) :
    SubdivisionVertex baseTannerSquarePresentation x S → Bool
  | .inl node => match node.val with
      | .x _ => false
      | .q q => decide (q=stripQ j x)
      | .z z => decide (z=j)
  | .inr (.inl edgeInterior) => match edgeInterior.1.val with
      | .inl _ => false
      | .inr e => decide (e.val.1=stripQ j x ∧ e.val.2=j)
  | .inr (.inr _) => false
def stripPotential (S : OddScale) (j : Fin 2) : Word F (RawOne S).X :=
  fun ⟨x,(_,v)⟩ => if stripMember j x S v then 1 else 0
def stripSeedCocycle (j : Fin 2) : Word F BaseQubit :=
  if j=0 then ![1,0,1,0,0] else ![0,1,0,1,0]
def rawSeedLift (S : OddScale) (j : Fin 2) : Word F (RawOne S).Q := by
  exact BDL26ReplacementCochainMaps.rxMap1Coord baseTannerSquarePresentation S
    (stripSeedCocycle j)
def terminalOldKernel (S : OddScale) (j : Fin 2) : Word F (RawOne S).Q :=
  rawSeedLift S j+tannerCoboundary0 (RawOne S) (stripPotential S j)
theorem rx_local_gradient (S : OddScale) (p : Word F (RawOne S).X)
    (x : BaseX) (e : DoubleCylinderEdge baseTannerSquarePresentation x S) :
    tannerCoboundary0 (RawOne S) p (.inl ⟨x,e⟩)=
      p ⟨x,tannerDoubleCylinderEdgeStart baseTannerSquarePresentation x S e⟩+
        p ⟨x,tannerDoubleCylinderEdgeEnd baseTannerSquarePresentation x S e⟩ := by
  erw [BDL26RXLocalReplacement.rxPresentation_coboundary0_eq
    baseTannerSquarePresentation baseTannerSquareAdmissibleV4
    baseTannerSquareCellularRegular S]
  erw [BDL26RXDecoderAdapter.raw_delta0_x,
    ← doubleCylinderGraphBoundary_eq_boundary1]
  exact wordLinearMapTranspose_graphBoundary_apply _ _ _ _
theorem old_local_incidence (S : OddScale) (v : (RawOne S).X)
    (x : BaseX) (e : DoubleCylinderEdge baseTannerSquarePresentation x S) :
    (RawOne S).xq v (.inl ⟨x,e⟩)=true ↔
      v=⟨x,tannerDoubleCylinderEdgeStart baseTannerSquarePresentation x S e⟩ ∨
        v=⟨x,tannerDoubleCylinderEdgeEnd baseTannerSquarePresentation x S e⟩ := by
  have h := rx_local_gradient S (canonicalBasisWord (F:=F) v) x e
  erw [tannerCoboundary0_canonicalBasis_apply] at h
  have hn : (⟨x,tannerDoubleCylinderEdgeStart baseTannerSquarePresentation x S e⟩ :
      (RawOne S).X)≠⟨x,tannerDoubleCylinderEdgeEnd baseTannerSquarePresentation x S e⟩ := by
    intro he
    exact tannerDoubleCylinderEdgeStart_ne_end baseTannerSquarePresentation x S e
      (@sigma_same_index_inj baseTannerSquarePresentation.X
        (fun owner => DoubleCylinderVertex baseTannerSquarePresentation owner S) x _ _ he)
  exact scalar_unit_pair v _ _ hn _ h
def stripFace (j : Fin 2) (x : BaseX) :
    XStarFace baseTannerSquarePresentation x :=
  ⟨⟨j.val+2*x.val,by have := j.isLt; have := x.isLt; omega⟩,
    by fin_cases j <;> fin_cases x <;> decide⟩
def stripHorizontal (S : OddScale) (j : Fin 2) (x : BaseX)
    (c : BDL26FiniteTannerSquare.Two) (row : Fin (S.half+1)) : (RawOne S).Q :=
  .inl ⟨x,.inl (c,subdivisionHorizontalEdge baseTannerSquarePresentation x S
    (stripFace j x) (lastSegment S) row)⟩
abbrev PortVertices (S : OddScale) :=
  (r : (RawOne S).Q) → QDoubleCylinderVertex (transposePresentation (RawOne S)) r S
abbrev PortRoots (S : OddScale) :=
  (z : (RawOne S).Z) → ZDoubleCylinderVertex (RawOne S) z S
abbrev PortPaths (S : OddScale) (vertices : PortVertices S)
    (roots : PortRoots S) :=
  (r : (RawOne S).Q) → (z : (RawOne S).Z) →
    (hz : (RawOne S).qz r z=true) →
      UndirectedPath
        (tannerDoubleCylinderEdgeStart (transposePresentation (RawOne S)) z S)
        (tannerDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) z S)
        (roots z) (qToZDoubleCylinderVertex (RawOne S)
          (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S (vertices r))
def portBasis (S : OddScale) (vertices : PortVertices S)
    (roots : PortRoots S) (paths : PortPaths S vertices roots) (r : (RawOne S).Q) :
    Word F (RawTwo S).Q :=
  canonicalBasisWord (.inr ⟨r,vertices r⟩)+
    ∑ z : (RawOne S).Z, if hz : (RawOne S).qz r z=true then
      extendZEdgeWord (RawOne S) S z (pathChain (paths r z hz)) else 0
def portKernel (S : OddScale) (vertices : PortVertices S)
    (roots : PortRoots S) (paths : PortPaths S vertices roots)
    (w : Word F (RawOne S).Q) : Word F (RawTwo S).Q :=
  ∑ r : (RawOne S).Q, w r • portBasis S vertices roots paths r
theorem pathChain_append_eq {V E : Type} [Fintype E] [DecidableEq E]
    {start finish : E → V} {u v w : V}
    (p : UndirectedPath start finish u v) (q : UndirectedPath start finish v w) :
    pathChain (p.append q)=pathChain p+pathChain q := by
  induction q with
  | nil => simp [UndirectedPath.append,pathChain]
  | @step a b q edge connects ih =>
    change pathChain (p.append q)+Pi.single edge (1:F)=
      pathChain p+(pathChain q+Pi.single edge (1:F))
    rw [ih]
    exact add_assoc _ _ _
theorem path_append_support {V E : Type} [Fintype E] [DecidableEq E]
    {start finish : E → V} {u v w : V} (P : E → Prop)
    (p : UndirectedPath start finish u v) (q : UndirectedPath start finish v w)
    (hp : ∀ e, pathChain p e≠0 → P e)
    (hq : ∀ e, pathChain q e≠0 → P e) :
    ∀ e, pathChain (p.append q) e≠0 → P e := by
  intro e he
  rw [pathChain_append_eq,Pi.add_apply] at he
  by_cases h : pathChain p e=0
  · rw [h,zero_add] at he
    exact hq e he
  · exact hp e h
noncomputable def directFacePath0 (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (n : Nat) (hn : n≤S.half) :
    UndirectedPath (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
      (subdivisionGridVertex P x S f 0 0)
      (subdivisionGridVertex P x S f (gridAt S S.half le_rfl) (gridAt S n hn)) :=
  (horizontalAtRowPath P x S f 0 S.half le_rfl).append
    (verticalAtColumnPath P x S f (gridAt S S.half le_rfl) n hn)
noncomputable def directFacePath1 (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (n : Nat) (hn : n≤S.half) :
    UndirectedPath (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
      (subdivisionGridVertex P x S f 0 0)
      (subdivisionGridVertex P x S f (gridAt S n hn) (gridAt S S.half le_rfl)) :=
  (verticalAtColumnPath P x S f 0 S.half le_rfl).append
    (horizontalAtRowPath P x S f (gridAt S S.half le_rfl) n hn)
theorem directFacePath0_support (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (n : Nat) (hn : n≤S.half) :
    ∀ e, pathChain (directFacePath0 P x S f n hn) e≠0 →
      (∃ k : Fin S.half, e=.inl (xStarFaceXQEdge P x f 0,k)) ∨
      (∃ k : Fin S.half, e=.inl (xStarFaceQZEdge P x f 0,k)) := by
  apply path_append_support
  · intro e he
    obtain ⟨k,_,hk⟩ := horizontalAtRowPath_support P x S f 0 S.half le_rfl e he
    left
    refine ⟨k,?_⟩
    simpa [subdivisionHorizontalEdge] using hk
  · intro e he
    obtain ⟨k,_,hk⟩ := verticalAtColumnPath_support P x S f
      (gridAt S S.half le_rfl) n hn e he
    right
    refine ⟨k,?_⟩
    simpa [subdivisionVerticalEdge,gridAt,S.half_pos.ne'] using hk
theorem directFacePath1_support (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (n : Nat) (hn : n≤S.half) :
    ∀ e, pathChain (directFacePath1 P x S f n hn) e≠0 →
      (∃ k : Fin S.half, e=.inl (xStarFaceXQEdge P x f 1,k)) ∨
      (∃ k : Fin S.half, e=.inl (xStarFaceQZEdge P x f 1,k)) := by
  apply path_append_support
  · intro e he
    obtain ⟨k,_,hk⟩ := verticalAtColumnPath_support P x S f 0 S.half le_rfl e he
    left
    refine ⟨k,?_⟩
    simpa [subdivisionVerticalEdge] using hk
  · intro e he
    obtain ⟨k,_,hk⟩ := horizontalAtRowPath_support P x S f
      (gridAt S S.half le_rfl) n hn e he
    right
    refine ⟨k,?_⟩
    simpa [subdivisionHorizontalEdge,gridAt,S.half_pos.ne'] using hk
def baseEdgeCode : Edge baseTannerSquarePresentation → Nat
  | .inl e => 2*Nat.pair e.val.1.val e.val.2.val
  | .inr e => 2*Nat.pair e.val.1.val e.val.2.val+1
def baseVertexCode : Vertex baseTannerSquarePresentation → Nat
  | .x x => 2*x.val
  | .q q => 4*q.val+1
  | .z z => 4*z.val+3
def subVertexCode (x : BaseX) (S : OddScale) :
    SubdivisionVertex baseTannerSquarePresentation x S → Nat
  | .inl v => 2*baseVertexCode v.val
  | .inr (.inl ⟨e,i⟩) => 4*Nat.pair (baseEdgeCode e.val) i.val+1
  | .inr (.inr ⟨f,i,j⟩) => 4*Nat.pair f.val.val (Nat.pair i.val j.val)+3
def subEdgeCode (x : BaseX) (S : OddScale) :
    SubdivisionEdge baseTannerSquarePresentation x S → Nat
  | .inl ⟨e,i⟩ => 2*Nat.pair (baseEdgeCode e.val) i.val
  | .inr (.inl ⟨f,i,j⟩) => 4*Nat.pair f.val.val (Nat.pair i.val j.val)+1
  | .inr (.inr ⟨f,i,j⟩) => 4*Nat.pair f.val.val (Nat.pair i.val j.val)+3
def oldLocalStart (S : OddScale) (x : BaseX)
    (e : DoubleCylinderEdge baseTannerSquarePresentation x S) : (RawOne S).X :=
  ⟨x,tannerDoubleCylinderEdgeStart baseTannerSquarePresentation x S e⟩
def oldLocalEnd (S : OddScale) (x : BaseX)
    (e : DoubleCylinderEdge baseTannerSquarePresentation x S) : (RawOne S).X :=
  ⟨x,tannerDoubleCylinderEdgeEnd baseTannerSquarePresentation x S e⟩
def oldLargestX (S : OddScale) : (r : (RawOne S).Q) → (RawOne S).X
  | .inl ⟨x,e⟩ =>
      if Encodable.encode (oldLocalStart S x e :
          (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
        Encodable.encode (oldLocalEnd S x e :
          (BDL26LevelTwoDecoder.executableLevelOne S).X) then oldLocalEnd S x e
      else oldLocalStart S x e
  | .inr q => ((rxState S baseState).admissible.toTannerSquareAdmissible.xqRoot (.inr q)).val
theorem oldLargestX_incident (S : OddScale) (r : (RawOne S).Q) :
    (RawOne S).xq (oldLargestX S r) r=true := by
  rcases r with ⟨x,e⟩ | q
  · change (RawOne S).xq
      (if Encodable.encode (oldLocalStart S x e : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
        Encodable.encode (oldLocalEnd S x e : (BDL26LevelTwoDecoder.executableLevelOne S).X)
       then oldLocalEnd S x e else oldLocalStart S x e) (.inl ⟨x,e⟩)=true
    split_ifs
    · exact (old_local_incidence S _ x e).2 (Or.inr rfl)
    · exact (old_local_incidence S _ x e).2 (Or.inl rfl)
  · exact ((rxState S baseState).admissible.toTannerSquareAdmissible.xqRoot (.inr q)).property
def largePorts (S : OddScale) (c : BDL26FiniteTannerSquare.Two)
    (depth : Option (Fin (S.half-1))) : PortVertices S := fun r =>
  match depth with
  | none => (c,.inl (.inr ⟨oldLargestX S r,oldLargestX_incident S r⟩))
  | some i => (c,.inr (⟨oldLargestX S r,oldLargestX_incident S r⟩,i))
def gammaRadial (S : OddScale) (j : Fin 2) (n : Fin S.half) : (RawOne S).Q :=
  .inl ⟨(0 : BaseX),.inl (0,.inl (seedRadial j,n))⟩
theorem pathChain_map_eq {V E V' E' : Type}
    [Fintype E] [Fintype E'] [DecidableEq E] [DecidableEq E']
    {start finish : E → V} {start' finish' : E' → V'}
    (f : V → V') (g : E → E')
    (hs : ∀ e, start' (g e)=f (start e)) (ht : ∀ e, finish' (g e)=f (finish e))
    {u v : V} (p : UndirectedPath start finish u v) :
    pathChain (p.map f g hs ht)=wordPushforward g (pathChain p) := by
  induction p with
  | nil => simp [UndirectedPath.map,pathChain]
  | @step a b p edge connects ih =>
    change pathChain (p.map f g hs ht)+Pi.single (g edge) (1:F)=
      wordPushforward g (pathChain p+Pi.single edge (1:F))
    rw [map_add,ih]
    apply congrArg (fun w : Word F E' => wordPushforward g (pathChain p)+w)
    simpa only [basis_eq_single] using (wordPushforward_canonicalBasis g edge).symm
theorem pushforward_support {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (f : I → J) (w : Word F I) (j : J)
    (hj : wordPushforward f w j≠0) :
    ∃ i, w i≠0 ∧ j=f i := by
  rw [wordPushforward_apply] at hj
  obtain ⟨i,_,hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj
  by_cases he : j=f i
  · rw [if_pos he] at hi
    exact ⟨i,hi,he⟩
  · rw [if_neg he] at hi
    exact False.elim (hi rfl)
theorem face_of_qxz (P : TannerSquarePresentation) (x : P.X)
    (q : P.Q) (z : P.Z) (hx : P.xq x q=true) (hz : P.qz q z=true) :
    ∃ (f : XStarFace (transposePresentation P) z)
      (j : BDL26FiniteTannerSquare.Two), P.faceQ f.val j=q ∧ P.faceX f.val=x := by
  let shared : SharedQ P.data x z := ⟨q,by simp [hx,hz]⟩
  obtain ⟨⟨f,j⟩,hf⟩ := (P.perfectPairing x z).2 shared
  refine ⟨⟨f.val,(transposed_face_member P z f.val).mpr f.property.2⟩,j,?_,f.property.1⟩
  exact congrArg Subtype.val hf
theorem qToZ_face_endpoint (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (z : P.Z)
    (f : XStarFace (transposePresentation P) z) (j : BDL26FiniteTannerSquare.Two)
    (hz : P.qz (P.faceQ f.val j) z=true) (S : OddScale) :
    qToZSubdivisionVertex P A (P.faceQ f.val j) z hz S
      (.inl (.inr ⟨P.faceX f.val,P.data.faceQ_xq f.val j⟩))=
      subdivisionGridVertex (transposePresentation P) z S f
        (gridAt S S.half le_rfl) (gridAt S S.half le_rfl) := by
  simp only [qToZSubdivisionVertex,subdivisionGridVertex,gridAt,S.half_pos.ne',
    ↓reduceDIte] <;> congr 1
noncomputable def atCopyPath (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (c : BDL26FiniteTannerSquare.Two)
    {u v : SubdivisionVertex P x S}
    (p : UndirectedPath (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S) u v) :
    UndirectedPath (tannerDoubleCylinderEdgeStart P x S)
      (tannerDoubleCylinderEdgeEnd P x S) (c,u) (c,v) :=
  UndirectedPath.map
    (edgeStart':=tannerDoubleCylinderEdgeStart P x S)
    (edgeEnd':=tannerDoubleCylinderEdgeEnd P x S)
    (fun v : SubdivisionVertex P x S => (c,v))
    (fun e : SubdivisionEdge P x S => (Sum.inl (c,e) : DoubleCylinderEdge P x S))
    (fun _ => rfl) (fun _ => rfl) p
theorem atCopyPath_support (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (c : BDL26FiniteTannerSquare.Two)
    {u v : SubdivisionVertex P x S}
    (p : UndirectedPath (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S) u v)
    (e : DoubleCylinderEdge P x S) (he : pathChain (atCopyPath P x S c p) e≠0) :
    ∃ e', pathChain p e'≠0 ∧ e=.inl (c,e') := by
  erw [atCopyPath,pathChain_map_eq] at he
  exact pushforward_support _ _ _ he
theorem exists_directFaceAtCopy0 (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) (c : BDL26FiniteTannerSquare.Two)
    (n : Nat) (hn : n≤S.half) :
    ∃ p : UndirectedPath (tannerDoubleCylinderEdgeStart P x S)
      (tannerDoubleCylinderEdgeEnd P x S)
      (c,subdivisionGridVertex P x S f 0 0)
      (c,subdivisionGridVertex P x S f (gridAt S S.half le_rfl) (gridAt S n hn)),
      ∀ e, pathChain p e≠0 → ∃ (a : XStarEdge P x) (k : Fin S.half),
        e=.inl (c,.inl (a,k)) ∧
          (a=xStarFaceXQEdge P x f 0 ∨ a=xStarFaceQZEdge P x f 0) := by
  refine ⟨atCopyPath P x S c (directFacePath0 P x S f n hn),?_⟩
  intro e he
  obtain ⟨e',he',rfl⟩ := atCopyPath_support P x S c _ e he
  rcases directFacePath0_support P x S f n hn e' he' with h | h
  · obtain ⟨k,rfl⟩ := h
    exact ⟨_,k,rfl,Or.inl rfl⟩
  · obtain ⟨k,rfl⟩ := h
    exact ⟨_,k,rfl,Or.inr rfl⟩
theorem exists_directFaceAtCopy1 (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) (c : BDL26FiniteTannerSquare.Two)
    (n : Nat) (hn : n≤S.half) :
    ∃ p : UndirectedPath (tannerDoubleCylinderEdgeStart P x S)
      (tannerDoubleCylinderEdgeEnd P x S)
      (c,subdivisionGridVertex P x S f 0 0)
      (c,subdivisionGridVertex P x S f (gridAt S n hn) (gridAt S S.half le_rfl)),
      ∀ e, pathChain p e≠0 → ∃ (a : XStarEdge P x) (k : Fin S.half),
        e=.inl (c,.inl (a,k)) ∧
          (a=xStarFaceXQEdge P x f 1 ∨ a=xStarFaceQZEdge P x f 1) := by
  refine ⟨atCopyPath P x S c (directFacePath1 P x S f n hn),?_⟩
  intro e he
  obtain ⟨e',he',rfl⟩ := atCopyPath_support P x S c _ e he
  rcases directFacePath1_support P x S f n hn e' he' with h | h
  · obtain ⟨k,rfl⟩ := h
    exact ⟨_,k,rfl,Or.inl rfl⟩
  · obtain ⟨k,rfl⟩ := h
    exact ⟨_,k,rfl,Or.inr rfl⟩
def chosenPort (P : TannerSquarePresentation) (S : OddScale)
    (r : P.Q) (x : P.X) (hx : P.xq x r=true) (c : BDL26FiniteTannerSquare.Two)
    (depth : Option (Fin (S.half-1))) : QDoubleCylinderVertex (transposePresentation P) r S :=
  match depth with
  | none => (c,.inl (.inr ⟨x,hx⟩))
  | some i => (c,.inr (⟨x,hx⟩,i))
def zCenter (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (c : BDL26FiniteTannerSquare.Two) : ZDoubleCylinderVertex P z S :=
  (c,.inl ⟨.x z,by change decide (z=z)=true; exact decide_eq_true rfl⟩)
theorem exists_supported_path_congr {V E : Type} [DecidableEq E]
    {start finish : E → V} {u u' v v' : V}
    (hu : u=u') (hv : v=v') (property : E → Prop) :
    (∃ p : UndirectedPath start finish u v, ∀ e, pathChain p e≠0 → property e) ↔
      (∃ p : UndirectedPath start finish u' v', ∀ e, pathChain p e≠0 → property e) := by
  cases hu
  cases hv
  rfl
theorem exists_direct_face_port_path (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (z : P.Z)
    (f : XStarFace (transposePresentation P) z) (j : BDL26FiniteTannerSquare.Two)
    (hz : P.qz (P.faceQ f.val j) z=true) (c : BDL26FiniteTannerSquare.Two)
    (depth : Option (Fin (S.half-1))) :
    ∃ p : UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
      (zCenter P S z c)
      (qToZDoubleCylinderVertex P A (P.faceQ f.val j) z hz S
        (chosenPort P S (P.faceQ f.val j) (P.faceX f.val)
          (P.data.faceQ_xq f.val j) c depth)),
      ∀ e, pathChain p e≠0 →
        ∃ (a : XStarEdge (transposePresentation P) z) (k : Fin S.half),
          e=.inl (c,.inl (a,k)) ∧
            (a=xStarFaceXQEdge (transposePresentation P) z f j ∨
              a=xStarFaceQZEdge (transposePresentation P) z f j) := by
  have hf : P.faceZ f.val=z := (transposed_face_member P z f.val).mp f.property
  have hcenter : (c,subdivisionGridVertex (transposePresentation P) z S f 0 0)=
      zCenter P S z c := by
    simp [subdivisionGridVertex,xStarFaceXVertex,zCenter,hf,Subtype.ext_iff,
      transposePresentation,transposeTannerSquareData,TannerSquarePresentation.faceX]
  fin_cases j
  · cases depth with
    | none =>
      have hend := congrArg (fun v => (c,v)) (qToZ_face_endpoint P A z f 0 hz S)
      apply (exists_supported_path_congr hcenter hend.symm _).mp
      exact exists_directFaceAtCopy0 (transposePresentation P) z S f c S.half le_rfl
    | some i =>
      have hend := congrArg (fun v => (c,v)) (qToZ_face_interior0 P A z f hz S i)
      apply (exists_supported_path_congr hcenter hend.symm _).mp
      exact exists_directFaceAtCopy0 (transposePresentation P) z S f c (i.val+1)
        (by have := i.isLt; omega)
  · cases depth with
    | none =>
      have hend := congrArg (fun v => (c,v)) (qToZ_face_endpoint P A z f 1 hz S)
      apply (exists_supported_path_congr hcenter hend.symm _).mp
      exact exists_directFaceAtCopy1 (transposePresentation P) z S f c S.half le_rfl
    | some i =>
      have hend := congrArg (fun v => (c,v)) (qToZ_face_interior1 P A z f hz S i)
      apply (exists_supported_path_congr hcenter hend.symm _).mp
      exact exists_directFaceAtCopy1 (transposePresentation P) z S f c (i.val+1)
        (by have := i.isLt; omega)
theorem exists_direct_port_path (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (r : P.Q) (x : P.X) (z : P.Z)
    (hx : P.xq x r=true) (hz : P.qz r z=true) (c : BDL26FiniteTannerSquare.Two)
    (depth : Option (Fin (S.half-1))) :
    ∃ p : UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
      (zCenter P S z c)
      (qToZDoubleCylinderVertex P A r z hz S (chosenPort P S r x hx c depth)),
      ∀ e, pathChain p e≠0 →
        ∃ (a : XStarEdge (transposePresentation P) z) (k : Fin S.half),
          e=.inl (c,.inl (a,k)) ∧
            (a.val=Sum.inl ⟨(z,r),hz⟩ ∨ a.val=Sum.inr ⟨(r,x),hx⟩) := by
  obtain ⟨f,j,hq,hx'⟩ := face_of_qxz P x r z hx hz
  cases hq
  cases hx'
  obtain ⟨p,hp⟩ := exists_direct_face_port_path P A S z f j hz c depth
  refine ⟨p,?_⟩
  intro e he
  obtain ⟨a,k,rfl,ha⟩ := hp e he
  refine ⟨a,k,rfl,?_⟩
  rcases ha with rfl | rfl
  · left
    have hf : P.faceZ f.val=z := (transposed_face_member P z f.val).mp f.property
    apply congrArg Sum.inl
    apply Subtype.ext
    exact Prod.ext hf rfl
  · right
    rfl
def directRoots (S : OddScale) (c : BDL26FiniteTannerSquare.Two) : PortRoots S :=
  fun z => zCenter (RawOne S) S z c
def directPaths (S : OddScale) (c : BDL26FiniteTannerSquare.Two)
    (depth : Option (Fin (S.half-1))) :
    PortPaths S (largePorts S c depth) (directRoots S c) := fun r z hz =>
  Classical.choose (exists_direct_port_path (RawOne S)
    (rxState S baseState).admissible.toTannerSquareAdmissible S r (oldLargestX S r) z
    (oldLargestX_incident S r) hz c depth)
theorem cast_root_star_member {P Q : TannerSquarePresentation} (h : P=Q)
    (r : Q.Q) (z : Q.Z) (hz : Q.qz r z=true)
    (hm : xStarEdgeMember (transposePresentation Q) z (Sum.inl ⟨(z,r),hz⟩)=true) :
    xStarEdgeMember (transposePresentation P)
      (cast (congrArg TannerSquarePresentation.Z h).symm z)
      (Sum.inl ⟨(cast (congrArg TannerSquarePresentation.Z h).symm z,
        cast (congrArg TannerSquarePresentation.Q h).symm r),cast_qz h r z hz⟩)=true := by
  cases h
  exact hm
theorem cast_x_star_member {P Q : TannerSquarePresentation} (h : P=Q)
    (r : Q.Q) (x : Q.X) (hx : Q.xq x r=true) (z : Q.Z)
    (hm : xStarEdgeMember (transposePresentation Q) z (Sum.inr ⟨(r,x),hx⟩)=true) :
    xStarEdgeMember (transposePresentation P)
      (cast (congrArg TannerSquarePresentation.Z h).symm z)
      (Sum.inr ⟨(cast (congrArg TannerSquarePresentation.Q h).symm r,
        cast (congrArg TannerSquarePresentation.X h).symm x),cast_xq h r x hx⟩)=true := by
  cases h
  exact hm
def halfOneTinyPotential (S : OddScale) : Word F (RawOne S).X :=
  canonicalBasisWord ⟨(0 : BaseX),(0,.inl seedCenter)⟩+
    canonicalBasisWord ⟨(0 : BaseX),(0,.inl (seedQVertex 0))⟩
def halfOneTinyKernel (S : OddScale) : Word F (RawOne S).Q :=
  tannerCoboundary0 (RawOne S) (halfOneTinyPotential S)
def firstCutMember (x : BaseX) (S : OddScale) :
    SubdivisionVertex baseTannerSquarePresentation x S → Bool
  | .inl node => match node.val with
      | .x _ => false
      | .q q => decide (q=stripQ 1 x)
      | .z z => decide (z=(1 : BaseZ))
  | .inr (.inl edgeInterior) => match edgeInterior.1.val with
      | .inl e => decide (e.val.2=stripQ 1 x)
      | .inr e => decide (e.val.2=(1 : BaseZ))
  | .inr (.inr faceInterior) => decide (faceInterior.1=stripFace 1 x)
def firstCutPotential (S : OddScale) : Word F (RawOne S).X :=
  fun ⟨x,(_,v)⟩ => if firstCutMember x S v then 1 else 0
def firstCutOldKernel (S : OddScale) : Word F (RawOne S).Q :=
  rawSeedLift S 1+tannerCoboundary0 (RawOne S) (firstCutPotential S)
def terminalTag (S : OddScale) (j : Fin 2) : Nat :=
  max (2*(4*j.val+1)) (4*Nat.pair (2*j.val) (S.half-2)+1)
def radialPrevious (S : OddScale) (i : Fin (S.half-1)) : Fin S.half :=
  ⟨i.val,by have := i.isLt; omega⟩
def radialFollowing (S : OddScale) (i : Fin (S.half-1)) : Fin S.half :=
  ⟨i.val+1,by have := i.isLt; omega⟩
def radialInteriorX (S : OddScale) (j : Fin 2) (i : Fin (S.half-1)) : (RawOne S).X :=
  ⟨(0 : BaseX),(0,.inr (.inl (seedRadial j,i)))⟩
def radialPerp (S : OddScale) (j : Fin 2) (i : Fin (S.half-1)) : (RawOne S).Q :=
  .inl ⟨(0 : BaseX),.inl (0,.inr (.inr (seedFace j,i,⟨0,S.half_pos⟩)))⟩
noncomputable def boundarySpokeEdge (P : TannerSquarePresentation)
    (x : P.X) (q : P.Q) (hm : xStarBoundaryVertexMember P x (.q q)=true) :
    XStarEdge P x := by
  have hinc : P.xq x q=true := by
    obtain ⟨f,hf,hq⟩ := of_decide_eq_true hm
    have hfx : P.faceX f=x := by simpa [xStarFaceMember] using hf
    rcases hq with hq | hq
    · simpa only [hfx,← hq] using P.data.faceQ_xq f 0
    · simpa only [hfx,← hq] using P.data.faceQ_xq f 1
  refine ⟨.inl ⟨(x,q),hinc⟩,?_⟩
  change decide (∃ f : P.Face, xStarFaceMember P x f=true ∧
    decide (⟨(x,q),hinc⟩=faceXQEdge P f 0 ∨
      ⟨(x,q),hinc⟩=faceXQEdge P f 1)=true)=true
  rw [decide_eq_true_eq]
  obtain ⟨f,hf,hq⟩ := of_decide_eq_true hm
  refine ⟨f,hf,?_⟩
  have hfx : P.faceX f=x := by simpa [xStarFaceMember] using hf
  change decide (⟨(x,q),hinc⟩=faceXQEdge P f 0 ∨
    ⟨(x,q),hinc⟩=faceXQEdge P f 1)=true
  rw [decide_eq_true_eq]
  rcases hq with hq | hq
  · left
    apply Subtype.ext
    exact Prod.ext hfx.symm hq
  · right
    apply Subtype.ext
    exact Prod.ext hfx.symm hq
noncomputable def raisedBoundaryVertex (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (hh : 2≤S.half) :
    XStarBoundaryVertex P x → SubdivisionVertex P x S
  | ⟨.x _,hm⟩ => False.elim (by simpa [xStarBoundaryVertexMember] using hm)
  | ⟨.q q,hm⟩ => .inr (.inl (boundarySpokeEdge P x q hm,lastInterior S hh))
  | ⟨.z z,hm⟩ => .inl (xStarBoundaryVertexToStar P x ⟨.z z,hm⟩)
def raisedBoundarySupport (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (hh : 2≤S.half) (e : SubdivisionEdge P x S) : Prop :=
  (∃ (f : XStarFace P x) (k : Fin S.half),
    e=.inr (.inr (f,lastInterior S hh,k))) ∨
  (∃ (f : XStarFace P x) (k : Fin S.half),
    e=.inr (.inl (f,k,lastInterior S hh))) ∨
  (∃ a : XStarEdge P x, e=.inl (a,lastSegment S))
noncomputable def raisedBoundaryL0 (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) :
    UndirectedPath (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
      (subdivisionGridVertex P x S f (lastGridInterior S) 0)
      (subdivisionGridVertex P x S f (gridAt S S.half le_rfl)
        (gridAt S S.half le_rfl)) := by
  apply UndirectedPath.step
    (verticalAtColumnPath P x S f (lastGridInterior S) S.half le_rfl)
    (subdivisionHorizontalEdge P x S f (lastSegment S) (gridAt S S.half le_rfl))
  apply Or.inl
  constructor
  · simpa [lastSegment,lastGridInterior,finCastGrid] using
      own_horizontal_start P x S f (lastSegment S)
        (gridAt S S.half le_rfl)
  · simpa [lastSegment,finSuccGrid,gridAt,
      show S.half-1+1=S.half by have := S.half_pos; omega] using
      own_horizontal_end P x S f (lastSegment S)
        (gridAt S S.half le_rfl)
noncomputable def raisedBoundaryL1 (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) :
    UndirectedPath (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
      (subdivisionGridVertex P x S f 0 (lastGridInterior S))
      (subdivisionGridVertex P x S f (gridAt S S.half le_rfl)
        (gridAt S S.half le_rfl)) := by
  apply UndirectedPath.step
    (horizontalAtRowPath P x S f (lastGridInterior S) S.half le_rfl)
    (subdivisionVerticalEdge P x S f (gridAt S S.half le_rfl) (lastSegment S))
  apply Or.inl
  constructor
  · simpa [lastSegment,lastGridInterior,finCastGrid] using
      own_vertical_start P x S f (gridAt S S.half le_rfl)
        (lastSegment S)
  · simpa [lastSegment,finSuccGrid,gridAt,
      show S.half-1+1=S.half by have := S.half_pos; omega] using
      own_vertical_end P x S f (gridAt S S.half le_rfl)
        (lastSegment S)
def faceBoundaryEdge (P : TannerSquarePresentation) (x : P.X)
    (f : XStarFace P x) (j : BDL26FiniteTannerSquare.Two) :
    XStarBoundaryEdge P x :=
  ⟨.inr (faceQZEdge P f.val j),by
    rw [boundary_edge_qz_view,decide_eq_true_eq]
    refine ⟨f.val,f.property,?_⟩
    fin_cases j <;> first | exact Or.inl rfl | exact Or.inr rfl⟩
noncomputable def actualRaisedRoots (S : OddScale) (hh : 2≤S.half)
    (c : BDL26FiniteTannerSquare.Two) : PortRoots S := fun z =>
  let A := transposeTannerSquareAdmissibleV4 (RawOne S) (rxState S baseState).admissible
  (c,raisedBoundaryVertex (transposePresentation (RawOne S)) z S hh
    (A.xBoundaryRoot z))
def raisedPortSupport (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (hh : 2≤S.half) (i : Fin (S.half-1))
    (e : SubdivisionEdge P x S) : Prop :=
  raisedBoundarySupport P x S hh e ∨
    ∃ f : XStarFace P x,
      e=.inr (.inl (f,lastSegment S,i)) ∨ e=.inr (.inr (f,i,lastSegment S))
def castZStarEdge {P Q : TannerSquarePresentation} (h : P=Q)
    (z : Q.Z) (a : XStarEdge (transposePresentation Q) z) :
    XStarEdge (transposePresentation P)
      (cast (congrArg TannerSquarePresentation.Z h).symm z) := by
  cases h
  exact a
def castZStarFace {P Q : TannerSquarePresentation} (h : P=Q)
    (z : Q.Z) (f : XStarFace (transposePresentation Q) z) :
    XStarFace (transposePresentation P)
      (cast (congrArg TannerSquarePresentation.Z h).symm z) := by
  cases h
  exact f
def firstCutHorizontal (S : OddScale) (x : BaseX)
    (c : BDL26FiniteTannerSquare.Two) (row : Fin (S.half+1)) : (RawOne S).Q :=
  .inl ⟨x,.inl (c,subdivisionHorizontalEdge baseTannerSquarePresentation x S
    (stripFace 1 x) ⟨0,S.half_pos⟩ row)⟩
def gammaCone (S : OddScale) (j : Fin 2) : (RawOne S).Q :=
  .inr ⟨seedQ j,(0,.inl (.inl ()))⟩
def seedQNode (S : OddScale) (j : Fin 2) : (RawOne S).X :=
  ⟨(0 : BaseX),(0,.inl (seedQVertex j))⟩
theorem seedQNode_incident (S : OddScale) (j : Fin 2) :
    (RawOne S).xq (seedQNode S j) (gammaCone S j)=true := by
  have h := raw_boundary1_view S (seedQNode S j) (gammaCone S j)
  change rxBoundary1Matrix baseTannerSquarePresentation S (seedQNode S j)
      (.inr ⟨seedQ j,(0,.inl (.inl ()))⟩)=
    (if (RawOne S).xq (seedQNode S j) (gammaCone S j)=true then (1:F) else 0) at h
  erw [seed_cone_incidence,if_pos rfl] at h
  by_contra hn
  simp [hn] at h
theorem seedQNode_shifted_neighbour (S : OddScale) (j : Fin 2)
    (q : BaseQubit) (v : QDoubleCylinderVertex baseTannerSquarePresentation q S)
    (hr : (RawOne S).xq (seedQNode S j) (.inr ⟨q,v⟩)=true) :
    (Sum.inr ⟨q,v⟩ : (RawOne S).Q)=gammaCone S j := by
  have h := raw_boundary1_view S (seedQNode S j) (.inr ⟨q,v⟩)
  change rxBoundary1Matrix baseTannerSquarePresentation S (seedQNode S j)
      (.inr ⟨q,v⟩)=
    (if (RawOne S).xq (seedQNode S j) (.inr ⟨q,v⟩)=true then (1:F) else 0) at h
  rw [if_pos hr] at h
  rcases v with ⟨c,(cone | endpoint) | ⟨edge,i⟩⟩
  · cases cone
    fin_cases j <;> fin_cases q <;> fin_cases c
    all_goals
      simp [rxBoundary1Matrix,qDoubleCylinderVertexXIncidence,qSubdivisionVertexXIncidence,
        seedQNode,seedQVertex,seedQ,gammaCone,xStarBoundaryEdgeToStar,
        qToXBoundaryEdge,TannerSquarePresentation.xq,baseTannerSquarePresentation,
        baseTannerSquareData,baseBoundary1Matrix,Fin.ext_iff] at h ⊢
    all_goals first | rfl | contradiction
  · rcases endpoint with ⟨z,hz⟩
    fin_cases j <;> fin_cases q <;> fin_cases z <;> fin_cases c
    all_goals
      simp [rxBoundary1Matrix,qDoubleCylinderVertexXIncidence,qSubdivisionVertexXIncidence,
        seedQNode,seedQVertex,seedQ,gammaCone,xStarBoundaryEdgeToStar,
        qToXBoundaryEdge,TannerSquarePresentation.xq,baseTannerSquarePresentation,
        baseTannerSquareData,baseBoundary1Matrix,Fin.ext_iff] at h
    all_goals simp_all only [ite_self,dite_eq_ite,zero_ne_one]
  · rcases edge with ⟨z,hz⟩
    fin_cases j <;> fin_cases q <;> fin_cases z <;> fin_cases c
    all_goals
      simp [rxBoundary1Matrix,qDoubleCylinderVertexXIncidence,qSubdivisionVertexXIncidence,
        seedQNode,seedQVertex,seedQ,gammaCone,xStarBoundaryEdgeToStar,
        qToXBoundaryEdge,TannerSquarePresentation.xq,baseTannerSquarePresentation,
        baseTannerSquareData,baseBoundary1Matrix,Fin.ext_iff] at h
    all_goals simp_all only [ite_self,dite_eq_ite,zero_ne_one]
def tinyQZ (S : OddScale) : (RawOne S).Q :=
  .inl ⟨(0 : BaseX),.inl (0,.inl
    (xStarFaceQZEdge baseTannerSquarePresentation 0 (seedFace 0) 0,⟨0,S.half_pos⟩))⟩
def tinyRadial4 (S : OddScale) : (RawOne S).Q :=
  .inl ⟨(0 : BaseX),.inl (0,.inl
    (xStarFaceXQEdge baseTannerSquarePresentation 0 (seedFace 0) 1,⟨0,S.half_pos⟩))⟩
def tinyBoundaryNode (S : OddScale) :
    SubdivisionBoundaryVertex baseTannerSquarePresentation (0 : BaseX) S :=
  ⟨.inl (seedQVertex 0),by
    change xStarBoundaryVertexMember baseTannerSquarePresentation 0
      (seedQVertex 0).val=true
    decide⟩
def tinyVertical (S : OddScale) : (RawOne S).Q :=
  .inl ⟨(0 : BaseX),.inr (tinyBoundaryNode S)⟩
theorem tinyQZ_node_incident (S : OddScale) :
    (RawOne S).xq (seedQNode S 0) (tinyQZ S)=true := by
  apply (old_local_incidence S _ 0 _).2
  left
  rfl
def tinyPortX (S : OddScale) (r : (RawOne S).Q) : (RawOne S).X :=
  if r=tinyQZ S then seedQNode S 0 else oldLargestX S r
theorem tinyPortX_incident (S : OddScale) (r : (RawOne S).Q) :
    (RawOne S).xq (tinyPortX S r) r=true := by
  unfold tinyPortX
  split_ifs with h
  · subst r
    exact tinyQZ_node_incident S
  · exact oldLargestX_incident S r
def tinyPorts (S : OddScale) (c : BDL26FiniteTannerSquare.Two) : PortVertices S :=
  fun r => chosenPort (RawOne S) S r (tinyPortX S r) (tinyPortX_incident S r) c none
def tinyRoot (S : OddScale) (c : BDL26FiniteTannerSquare.Two) :
    ZDoubleCylinderVertex (RawOne S) (seedConeCheck S 0) S :=
  qToZDoubleCylinderVertex (RawOne S)
    (rxState S baseState).admissible.toTannerSquareAdmissible
    (gammaCone S 0) (seedConeCheck S 0) (seedCone_degree_one S 0).1 S
    (c,.inl (.inr ⟨seedQNode S 0,seedQNode_incident S 0⟩))
def tinyRoots (S : OddScale) (c : BDL26FiniteTannerSquare.Two) : PortRoots S :=
  fun z => if h : z=seedConeCheck S 0 then h.symm ▸ tinyRoot S c
    else zCenter (RawOne S) S z c
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint


