-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
-- name    : QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T05:12:36.004476+00:00
-- url     : https://prove2.me/theorems/7199d195-3e55-4ec1-9a99-21a8e3a3b1df
-- title:
--   Equivalence
-- statement:
--   Definitions and structural lemmas for Equivalence, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Equivalence.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Geometry
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_correctionRegion_mem
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_syndromeRegion_mem
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
import Theorems.Thm_QEC_Coding_BDL26RXCohomology_differential0_eq
import Theorems.Thm_QEC_Coding_BDL26RXCohomology_differential1_eq
import Theorems.Thm_QEC_Coding_BDL26RXCohomology_full_gauge_x_zero
import Theorems.Thm_QEC_Coding_BDL26RXCohomology_local_potentials
import Theorems.Thm_QEC_Coding_BDL26RXCohomology_normalized_cocycle
import Theorems.Thm_QEC_Coding_BDL26RXCohomology_normalized_word
import Theorems.Thm_QEC_Coding_BDL26RXCohomology_raw_boundary_iff
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qCorrectionEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qSyndromeEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_transpose_wordEquiv_symm
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xCorrectionEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xLift_other
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xLift_same
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xSyndromeEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_zSyndromeEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalWordPush_single
import Theorems.Thm_QEC_Coding_BDL26RZCohomology_backward_mk
import Theorems.Thm_QEC_Coding_BDL26RZCohomology_forward_mk
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzFace_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzQ_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzX_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzZ_card
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_map2Coord_canonicalBasis
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary0_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary1_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rxMap_commutes_coboundary1
import Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_fiberPart_apply
import Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rxQOutgoing_nonincident
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0DoubleCylinderEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0DoubleCylinderVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0StarEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0StarVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0SubdivisionEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0SubdivisionVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4DoubleCylinderEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4DoubleCylinderVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4StarEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4StarVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4SubdivisionEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4SubdivisionVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_qDoubleCylinderEndRestriction_apply
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_copiedQ_image_copy
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_copiedQ_image_vertical
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_verticalZ_image_copy
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_verticalZ_image_vertical
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_coarseSyndrome_coe
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_historicalZeroSyndromeInput_supportFitsRadiusTwo
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionLength_sym2_mk
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_diag_not_mem_fixedGeneratorInteractions
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorOperator_adjoint_eq_self
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorSupport_eq_support
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_term_adjoint_eq_self
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridCellQubits_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridOccupiedCells_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_qubitsInRectangle_iff
import Theorems.Thm_QEC_Locality_centeredRectangleClippedGrowthRadius_zero
import Theorems.Thm_QEC_Locality_mem_centeredRectangleQubits_iff
import Theorems.Thm_QEC_Locality_mem_longInteractionEndpointQubits_iff
import Theorems.Thm_QEC_Locality_mem_longNeighborsOf_iff
import Theorems.Thm_QEC_Locality_mem_squareQubits_iff
import Theorems.Thm_QEC_Locality_squareGrowthRadius_succ_sub
import Theorems.Thm_QEC_Locality_squareGrowthRadius_zero
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.BDL26DecodingGraph.correctionRegion_mem
attribute [local simp] QEC.Coding.BDL26DecodingGraph.syndromeRegion_mem
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.alternatingCarrier_zero
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_target_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_target_val
attribute [local simp] QEC.Coding.BDL26FiniteTannerSquare.doubleCylinderEndInclusion_apply
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.qCorrectionEquiv_val
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.qSyndromeEquiv_val
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.transpose_wordEquiv_symm
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.xCorrectionEquiv_val
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.xLift_other
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.xLift_same
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.xSyndromeEquiv_val
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.zSyndromeEquiv_val
attribute [local simp] QEC.Coding.BDL26RXLocalReplacement.xLocalWordPush_single
attribute [local simp] QEC.Coding.BDL26RZCohomology.backward_mk
attribute [local simp] QEC.Coding.BDL26RZCohomology.forward_mk
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzFace_card
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzQ_card
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzX_card
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzZ_card
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.map2Coord_canonicalBasis
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary0_canonicalBasis_apply
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1_canonicalBasis_apply
attribute [local simp] QEC.Coding.BDL26ReplacementSupport.fiberPart_apply
attribute [local simp] QEC.Coding.BDL26ReplacementSupport.rxQOutgoing_nonincident
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
attribute [local simp] QEC.Coding.BDL26XLocalConnectingWeight.copiedQ_image_copy
attribute [local simp] QEC.Coding.BDL26XLocalConnectingWeight.copiedQ_image_vertical
attribute [local simp] QEC.Coding.BDL26XLocalConnectingWeight.verticalZ_image_copy
attribute [local simp] QEC.Coding.BDL26XLocalConnectingWeight.verticalZ_image_vertical
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.originalBoundary_single
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.MultiscaleDecoder.RZCoarseGraining.coarseSyndrome_coe
attribute [local simp] QEC.Coding.MultiscaleDecoder.historicalZeroSyndromeInput_supportFitsRadiusTwo
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.interactionLength_sym2_mk
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_diag_not_mem_fixedGeneratorInteractions
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorOperator_adjoint_eq_self
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorSupport_eq_support
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
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
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
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
namespace QEC.Coding.BDL26RXCohomology
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RXDecoderAdapter BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
open scoped Classical BigOperators
def coordinateWord (P : TannerSquarePresentation) (S : OddScale)
    (w : Word Field (rxReplacementPresentation P S).Q) : Word Field (RX1 P S) :=
  fun q => w q
def semanticWord (P : TannerSquarePresentation) (S : OddScale)
    (w : Word Field (RX1 P S)) : Word Field (rxReplacementPresentation P S).Q :=
  fun q => w q
@[simp] theorem semanticWord_coordinateWord (P : TannerSquarePresentation) (S : OddScale)
    (w : Word Field (rxReplacementPresentation P S).Q) :
    semanticWord P S (coordinateWord P S w) = w := rfl
@[simp] theorem coordinateWord_semanticWord (P : TannerSquarePresentation) (S : OddScale)
    (w : Word Field (RX1 P S)) : coordinateWord P S (semanticWord P S w) = w := rfl
theorem semanticWord_sub (P : TannerSquarePresentation) (S : OddScale)
    (u v : Word Field (RX1 P S)) :
    semanticWord P S (u-v) = semanticWord P S u - semanticWord P S v := rfl
theorem semanticWord_delta0 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (f : Word Field (RX0 P S)) :
    tannerCoboundary0 (rxReplacementPresentation P S) f =
      semanticWord P S (rxCoboundary0 P S f) := by
  rw [differential0_eq P A R S]
  rfl
theorem full_gauge_residual (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (w : Cocycle (rxReplacementPresentation P S)) :
    ∃ (v : Cocycle P) (f : Word Field (RX0 P S)),
      rxMap1Coord P S v.1 = coordinateWord P S w.1 - rxCoboundary0 P S f := by
  have hw : rxCoboundary1 P S w.1 = 0 := by
    rw [← differential1_eq P A R S]
    exact (BDL26RZCohomology.mem_cocycle_iff _ _).mp w.2
  obtain ⟨potentials,hp⟩ := local_potentials P A R S w.1 hw
  let f := ∑ x : P.X, xLift P S x (potentials x)
  let residual : Word Field (RX1 P S) := coordinateWord P S w.1 - rxCoboundary0 P S f
  have hb : semanticWord P S (rxCoboundary0 P S f) ∈
      (complex (rxReplacementPresentation P S)).firstCoboundaryCheckCode.carrier := by
    apply (BDL26RZCohomology.mem_boundary_iff _ _).mpr
    exact ⟨f, semanticWord_delta0 P A R S f⟩
  have hr : semanticWord P S residual ∈
      (complex (rxReplacementPresentation P S)).middleCocycleCode.carrier := by
    rw [show semanticWord P S residual =
      w.1 - semanticWord P S (rxCoboundary0 P S f) from
        (semanticWord_sub P S _ _).trans (by rw [semanticWord_coordinateWord])]
    exact Submodule.sub_mem _ w.2
      ((complex (rxReplacementPresentation P S)).firstCoboundaryCheckCode_le_middleCocycleCode hb)
  have hraw : rxCoboundary1 P S residual = 0 := by
    have hsemantic := (BDL26RZCohomology.mem_cocycle_iff _ _).mp hr
    rw [differential1_eq P A R S] at hsemantic
    exact hsemantic
  have hx := full_gauge_x_zero P S w.1 potentials hp
  let v : Cocycle P := ⟨coarseWord P S residual,
    (BDL26RZCohomology.mem_cocycle_iff _ _).mpr
      (normalized_cocycle P A.toTannerSquareAdmissible S residual hraw hx)⟩
  exact ⟨v,f, normalized_word P A.toTannerSquareAdmissible S residual hraw hx⟩
noncomputable def forwardCocycle (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    Cocycle P →ₗ[Field] Cocycle (rxReplacementPresentation P S) where
  toFun v := ⟨rxMap1Coord P S v.1, by
    apply (BDL26RZCohomology.mem_cocycle_iff _ _).mpr
    rw [differential1_eq P A R S]
    have hc := LinearMap.congr_fun (rxMap_commutes_coboundary1 P S) v.1
    change rxCoboundary1 P S (rxMap1Coord P S v.1) =
      rxMap2Coord P S (tannerCoboundary1 P v.1) at hc
    rw [(BDL26RZCohomology.mem_cocycle_iff _ _).mp v.2, map_zero] at hc
    exact hc⟩
  map_add' _ _ := Subtype.ext ((rxMap1Coord P S).map_add _ _)
  map_smul' _ _ := Subtype.ext ((rxMap1Coord P S).map_smul _ _)
theorem boundary_iff (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (v : Word Field P.Q) :
    semanticWord P S (rxMap1Coord P S v) ∈
      (complex (rxReplacementPresentation P S)).firstCoboundaryCheckCode.carrier ↔
      v ∈ (complex P).firstCoboundaryCheckCode.carrier := by
  constructor
  · intro hb
    obtain ⟨f,hf⟩ := (BDL26RZCohomology.mem_boundary_iff
      (rxReplacementPresentation P S) (semanticWord P S (rxMap1Coord P S v))).mp hb
    have hraw : rxCoboundary0 P S f = rxMap1Coord P S v := by
      have hd := LinearMap.congr_fun (differential0_eq P A R S) f
      funext q
      exact (congrFun hd q).symm.trans (congrFun hf q)
    exact (BDL26RZCohomology.mem_boundary_iff P v).mpr
      ((raw_boundary_iff P A.toTannerSquareAdmissible S v).mp ⟨f,hraw⟩)
  · intro hb
    obtain ⟨old,ho⟩ := (BDL26RZCohomology.mem_boundary_iff P v).mp hb
    obtain ⟨f,hf⟩ := (raw_boundary_iff P A.toTannerSquareAdmissible S v).mpr ⟨old,ho⟩
    apply (BDL26RZCohomology.mem_boundary_iff
      (rxReplacementPresentation P S) (semanticWord P S (rxMap1Coord P S v))).mpr
    exact ⟨f, (semanticWord_delta0 P A R S f).trans (congrArg (semanticWord P S) hf)⟩
theorem forward_boundary (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    (complex P).middleCoboundaryInCocycles ≤
      LinearMap.ker ((classOf (rxReplacementPresentation P S)).comp (forwardCocycle P A R S)) := by
  intro v hv
  apply LinearMap.mem_ker.mpr
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact (boundary_iff P A R S v.1).mpr hv
noncomputable def forward (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    H1 P →ₗ[Field] H1 (rxReplacementPresentation P S) :=
  (complex P).middleCoboundaryInCocycles.liftQ
    ((classOf (rxReplacementPresentation P S)).comp (forwardCocycle P A R S))
    (forward_boundary P A R S)
@[simp] theorem forward_mk (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (v : Cocycle P) :
    forward P A R S (classOf P v) =
      classOf (rxReplacementPresentation P S) (forwardCocycle P A R S v) := rfl
theorem gauge_class (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (w : Cocycle (rxReplacementPresentation P S)) (v : Cocycle P)
    (f : Word Field (RX0 P S))
    (hf : rxMap1Coord P S v.1 = coordinateWord P S w.1 - rxCoboundary0 P S f) :
    forward P A R S (classOf P v) = classOf (rxReplacementPresentation P S) w := by
  rw [forward_mk]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change semanticWord P S (rxMap1Coord P S v.1 - coordinateWord P S w.1) ∈
    (complex (rxReplacementPresentation P S)).firstCoboundaryCheckCode.carrier
  apply (BDL26RZCohomology.mem_boundary_iff _ _).mpr
  have hraw : rxCoboundary0 P S (-f) = rxMap1Coord P S v.1 - coordinateWord P S w.1 := by
    rw [map_neg, hf]
    abel
  exact ⟨-f, (semanticWord_delta0 P A R S (-f)).trans (congrArg (semanticWord P S) hraw)⟩
theorem forward_surjective (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    Function.Surjective (forward P A R S) := by
  intro h
  obtain ⟨w,rfl⟩ := (complex (rxReplacementPresentation P S)).middleCoboundaryInCocycles.mkQ_surjective h
  obtain ⟨v,f,hf⟩ := full_gauge_residual P A R S w
  exact ⟨classOf P v, gauge_class P A R S w v f hf⟩
theorem forward_injective (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    Function.Injective (forward P A R S) := by
  intro u v huv
  obtain ⟨a,rfl⟩ := (complex P).middleCoboundaryInCocycles.mkQ_surjective u
  obtain ⟨b,rfl⟩ := (complex P).middleCoboundaryInCocycles.mkQ_surjective v
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply (boundary_iff P A R S (a-b).1).mp
  have hz : forward P A R S (classOf P (a-b)) = 0 := by
    rw [map_sub, map_sub, huv, sub_self]
  rw [forward_mk] at hz
  have hb := (Submodule.Quotient.mk_eq_zero
    (complex (rxReplacementPresentation P S)).middleCoboundaryInCocycles).mp hz
  change semanticWord P S (rxMap1Coord P S (a-b).1) ∈
    (complex (rxReplacementPresentation P S)).firstCoboundaryCheckCode.carrier at hb
  exact hb
noncomputable def equiv (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    H1 P ≃ₗ[Field] H1 (rxReplacementPresentation P S) :=
  LinearEquiv.ofBijective (forward P A R S)
    ⟨forward_injective P A R S, forward_surjective P A R S⟩
end QEC.Coding.BDL26RXCohomology


