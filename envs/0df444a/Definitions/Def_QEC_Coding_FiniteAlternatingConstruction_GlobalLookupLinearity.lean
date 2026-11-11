-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
-- name    : QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T11:00:33.188033+00:00
-- url     : https://prove2.me/theorems/005a49b0-2315-4d61-abca-4a746cb5ef29
-- title:
--   Global Lookup Linearity
-- statement:
--   Definitions and structural lemmas for Global Lookup Linearity, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_correctionRegion_mem
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_syndromeRegion_mem
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_allWords_zero_first
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_mem_allWords
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_mem_coordinates
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_search_complete
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_search_sound
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_presentationOutput_coarse
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_presentationOutput_components
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_presentationOutput_correction
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qCorrectionEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qRepresentative_value
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qSyndromeEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_regionExtension_apply
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_transpose_wordEquiv_symm
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xCorrectionEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xLift_other
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xLift_same
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xSyndromeEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_zPairEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_zSyndromeEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalWordPush_single
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_presentationOutput_coarse
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_presentationOutput_components
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_presentationOutput_correction
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzFace_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzQ_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzX_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzZ_card
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_map2Coord_canonicalBasis
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary0_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary1_canonicalBasis_apply
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
attribute [local simp] QEC.Coding.BDL26RXLocalReplacement.xLocalWordPush_single
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
namespace QEC.Coding.BDL26GlobalLookupLinearity
open BDL26LevelTwoDecoder BDL26FiniteTannerSquare BDL26LevelTwoCode
open BDL26RZMap1CoordinateBridge
open scoped BigOperators
abbrev Bit := ZMod 2
theorem bit_cases (c : Bit) : c=0 ∨ c=1 :=
  (by decide : ∀ a : Bit, a=0 ∨ a=1) c
theorem word_add_self {I : Type} (a : Word Bit I) : a+a=0 := by
  funext i
  have h : ∀ c : Bit, c+c=0 := by decide
  exact h (a i)
def Before {I : Type} : List I → Word Bit I → Word Bit I → Prop
  | [], _, _ => False
  | q::qs, a, b => (a q=0 ∧ b q=1) ∨ (a q=b q ∧ Before qs a b)
theorem before_update {I : Type} [DecidableEq I] (qs : List I)
    (q : I) (hq : q∉qs) (a b : Word Bit I) (x y : Bit) :
    Before qs (Function.update a q x) (Function.update b q y) ↔ Before qs a b := by
  revert hq
  induction qs with
  | nil => intro hq; rfl
  | cons r rs ih =>
      intro hq
      have hr : r≠q := by intro h; subst r; exact hq (by simp)
      have hqr : q∉rs := fun h => hq (List.mem_cons_of_mem r h)
      simp only [Before, Function.update_of_ne hr, ih hqr]
theorem search_map {I J : Type} (accept : J → Bool) (f : I → J)
    (xs : List I) : search accept (xs.map f)=
      (search (fun a => accept (f a)) xs).map f := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      by_cases h : accept (f a)=true <;> simp [search,h,ih]
theorem search_append {I : Type} (accept : I → Bool) (xs ys : List I) :
    search accept (xs++ys)=
      match search accept xs with | some a => some a | none => search accept ys := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      by_cases h : accept a=true <;> simp [search,h,ih]
theorem search_wordsOn_cons {I : Type} [DecidableEq I]
    (accept : Word Bit I → Bool) (q : I) (qs : List I) :
    search accept (wordsOn (q::qs))=
      match search (fun a => accept (Function.update a q 0)) (wordsOn qs) with
      | some a => some (Function.update a q 0)
      | none => (search (fun a => accept (Function.update a q 1)) (wordsOn qs)).map
          (fun a => Function.update a q 1) := by
  rw [wordsOn,search_append,search_map,search_map]
  cases search (fun a => accept (Function.update a q 0)) (wordsOn qs) <;> rfl
theorem rejected_of_search_none {I : Type} (accept : I → Bool)
    (xs : List I) (hn : search accept xs=none) (a : I) (ha : a∈xs) :
    accept a≠true := by
  intro ht
  obtain ⟨b,hb⟩ := search_complete accept xs ⟨a,ha,ht⟩
  rw [hn] at hb
  cases hb
theorem search_wordsOn_minimal {I : Type} [DecidableEq I]
    (qs : List I) (hn : qs.Nodup) (accept : Word Bit I → Bool)
    (r : Word Bit I) (hr : search accept (wordsOn qs)=some r) :
    ∀ a∈wordsOn qs, accept a=true → ¬Before qs a r := by
  revert hr r accept hn
  induction qs with
  | nil => intro hn accept r hr a ha hp hb; exact hb
  | cons q qs ih =>
      intro hn accept r hr
      have hq : q∉qs := (List.nodup_cons.mp hn).1
      have htail : qs.Nodup := (List.nodup_cons.mp hn).2
      rw [search_wordsOn_cons] at hr
      cases hz : search (fun a => accept (Function.update a q 0)) (wordsOn qs) with
      | some z =>
          simp only [hz] at hr
          have er : Function.update z q 0=r := Option.some.inj hr
          subst r
          intro a ha hp hb
          change a∈(wordsOn qs).map (fun b => Function.update b q 0) ++
            (wordsOn qs).map (fun b => Function.update b q 1) at ha
          rcases List.mem_append.mp ha with ha | ha
          · obtain ⟨b,hbmem,rfl⟩ := List.mem_map.mp ha
            have hbefore : Before qs b z := by
              have ht : Before qs (Function.update b q 0) (Function.update z q 0) := by
                simpa only [Before,Function.update_self,eq_self_iff_true,zero_ne_one,and_false,false_and,
                  false_or,true_and] using hb
              exact (before_update qs q hq b z 0 0).mp ht
            exact ih htail _ z hz b hbmem hp hbefore
          · obtain ⟨b,hbmem,rfl⟩ := List.mem_map.mp ha
            simpa only [Before,Function.update_self,one_ne_zero,zero_ne_one,
              false_and,and_false,false_or] using hb
      | none =>
          simp only [hz] at hr
          cases ho : search (fun a => accept (Function.update a q 1)) (wordsOn qs) with
          | none => simp only [ho,Option.map_none] at hr; cases hr
          | some z =>
              simp only [ho,Option.map_some] at hr
              have er : Function.update z q 1=r := Option.some.inj hr
              subst r
              intro a ha hp hb
              change a∈(wordsOn qs).map (fun b => Function.update b q 0) ++
                (wordsOn qs).map (fun b => Function.update b q 1) at ha
              rcases List.mem_append.mp ha with ha | ha
              · obtain ⟨b,hbmem,rfl⟩ := List.mem_map.mp ha
                exact rejected_of_search_none _ _ hz b hbmem hp
              · obtain ⟨b,hbmem,rfl⟩ := List.mem_map.mp ha
                have hbefore : Before qs b z := by
                  have ht : Before qs (Function.update b q 1) (Function.update z q 1) := by
                    simpa only [Before,Function.update_self,eq_self_iff_true,one_ne_zero,false_and,
                      false_or,true_and] using hb
                  exact (before_update qs q hq b z 1 1).mp ht
                exact ih htail _ z ho b hbmem hp hbefore
theorem first_one_or_zero {I : Type} (qs : List I) (k : Word Bit I) :
    (∀ q∈qs, k q=0) ∨
      ∃ q∈qs, k q=1 ∧ ∀ r : Word Bit I, r q=1 → Before qs (r+k) r := by
  induction qs with
  | nil => exact Or.inl (by intro q h; cases h)
  | cons q qs ih =>
      rcases bit_cases (k q) with hk | hk
      · rcases ih with hzero | ⟨p,hp,hkp,hbefore⟩
        · apply Or.inl
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hk
          · exact hzero p hp
        · refine Or.inr ⟨p,List.mem_cons_of_mem q hp,hkp,?_⟩
          intro r hr
          exact Or.inr ⟨by simp only [Pi.add_apply,hk,add_zero],hbefore r hr⟩
      · refine Or.inr ⟨q,List.mem_cons_self,hk,?_⟩
        intro r hr
        exact Or.inl ⟨by change r q+k q=0; rw [hr,hk]; decide,hr⟩
variable {A B : Type} [Fintype A] [Encodable A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]
def G (L : Word Bit A →ₗ[Bit] Word Bit B) (s : Word Bit B) : Word Bit A :=
  (search (fun e => decide (L e=s)) (allWords A)).getD 0
theorem global_search_success (L : Word Bit A →ₗ[Bit] Word Bit B)
    (s : Word Bit B) (hs : s∈LinearMap.range L) :
    ∃ e, search (fun a => decide (L a=s)) (allWords A)=some e := by
  obtain ⟨a,ha⟩ := hs
  exact search_complete _ _ ⟨a,mem_allWords A a,by simpa using ha⟩
theorem global_preimage (L : Word Bit A →ₗ[Bit] Word Bit B)
    (s : Word Bit B) (hs : s∈LinearMap.range L) : L (G L s)=s := by
  obtain ⟨e,he⟩ := global_search_success L s hs
  have hp := (search_sound _ _ _ he).2
  simpa only [G,he,Option.getD_some,decide_eq_true_eq] using hp
theorem global_zero (L : Word Bit A →ₗ[Bit] Word Bit B) : G L 0=0 := by
  obtain ⟨tail,htail⟩ := allWords_zero_first A
  simp [G,htail,search]
theorem global_minimal (L : Word Bit A →ₗ[Bit] Word Bit B)
    (s : Word Bit B) (hs : s∈LinearMap.range L) :
    ∀ a : Word Bit A, L a=s → ¬Before (coordinates A) a (G L s) := by
  obtain ⟨e,he⟩ := global_search_success L s hs
  have hn : (coordinates A).Nodup := by
    letI : LinearOrder A := LinearOrder.lift' Encodable.encode Encodable.encode_injective
    change (Finset.univ.sort : List A).Nodup
    exact Finset.sort_nodup _ _
  have hm := search_wordsOn_minimal (coordinates A) hn
    (fun a => decide (L a=s)) e he
  intro a ha
  simpa only [G,he,Option.getD_some] using
    hm a (mem_allWords A a) (by simpa using ha)
theorem global_add_words (L : Word Bit A →ₗ[Bit] Word Bit B)
    (a b : Word Bit A) : G L (L a+L b)=G L (L a)+G L (L b) := by
  let r := G L (L a)
  let t := G L (L b)
  let u := G L (L a+L b)
  have hr : L r=L a := global_preimage L _ ⟨a,rfl⟩
  have ht : L t=L b := global_preimage L _ ⟨b,rfl⟩
  have hu : L u=L a+L b := global_preimage L _ ⟨a+b,L.map_add a b⟩
  let k := r+t+u
  have hk : L k=0 := by
    change L (r+t+u)=0
    rw [map_add,map_add,hr,ht,hu]
    exact word_add_self (L a+L b)
  have hz : k=0 := by
    rcases first_one_or_zero (coordinates A) k with hz | ⟨q,hq,hkq,hbefore⟩
    · funext q
      exact hz q (mem_coordinates A q)
    · have hone : r q=1 ∨ t q=1 ∨ u q=1 := by
        rcases bit_cases (r q) with h | h
        · rcases bit_cases (t q) with j | j
          · rcases bit_cases (u q) with l | l
            · have hbad : (0 : Bit)=1 := by simpa only [k,Pi.add_apply,h,j,l,zero_add] using hkq
              exact False.elim (zero_ne_one hbad)
            · exact Or.inr (Or.inr l)
          · exact Or.inr (Or.inl j)
        · exact Or.inl h
      rcases hone with h | h | h
      · have he : L (r+k)=L a := by rw [map_add,hk,add_zero,hr]
        exact False.elim (global_minimal L (L a) ⟨a,rfl⟩ (r+k) he (hbefore r h))
      · have he : L (t+k)=L b := by rw [map_add,hk,add_zero,ht]
        exact False.elim (global_minimal L (L b) ⟨b,rfl⟩ (t+k) he (hbefore t h))
      · have he : L (u+k)=L a+L b := by rw [map_add,hk,add_zero,hu]
        exact False.elim (global_minimal L (L a+L b) ⟨a+b,L.map_add a b⟩
          (u+k) he (hbefore u h))
  change u=r+t
  calc
    u=0+u := (zero_add u).symm
    _=(r+t+u)+u := congrArg (fun z => z+u) hz.symm
    _=r+t := by rw [add_assoc,word_add_self,add_zero]
theorem global_add_image (L : Word Bit A →ₗ[Bit] Word Bit B)
    (s t : Word Bit B) (hs : s∈LinearMap.range L) (ht : t∈LinearMap.range L) :
    G L (s+t)=G L s+G L t := by
  obtain ⟨a,rfl⟩ := hs
  obtain ⟨b,rfl⟩ := ht
  exact global_add_words L a b
theorem global_smul_image (L : Word Bit A →ₗ[Bit] Word Bit B)
    (s : Word Bit B) (hs : s∈LinearMap.range L) (c : Bit) :
    G L (c • s)=c • G L s := by
  rcases bit_cases c with rfl | rfl <;> simp [global_zero]
def imageSection (L : Word Bit A →ₗ[Bit] Word Bit B) :
    LinearMap.range L →ₗ[Bit] Word Bit A where
  toFun s := G L s.val
  map_add' s t := global_add_image L s.val t.val s.property t.property
  map_smul' c s := global_smul_image L s.val s.property c
def incidenceLinear {Q Z : Type} (F : Fintype Q) (inc : Q → Z → Bool) :
    Word Bit Q →ₗ[Bit] Word Bit Z where
  toFun := syndromeFromBits F inc
  map_add' a b := by
    funext z
    change (∑ q∈F.elems, if inc q z then a q+b q else 0)=_
    have he : ∀ q, (if inc q z then a q+b q else 0)=
        (if inc q z then a q else 0)+(if inc q z then b q else 0) := by
      intro q
      cases inc q z <;> simp
    simp_rw [he]
    exact Finset.sum_add_distrib
  map_smul' c a := by
    rcases bit_cases c with rfl | rfl
    · funext z
      simp [syndromeFromBits]
    · simp
def executableLinear (S : OddScale) :
    Word Bit (ExecutableQ S) →ₗ[Bit] Word Bit (ExecutableZ S) where
  toFun := executableSyndrome S
  map_add' a b := by
    unfold executableSyndrome rawSyndrome
    exact (incidenceLinear _ _).map_add a b
  map_smul' c a := by
    unfold executableSyndrome rawSyndrome
    exact (incidenceLinear _ _).map_smul c a
def executableGlobal (S : OddScale) (s : Word Bit (ExecutableZ S)) :
    Word Bit (ExecutableQ S) := G (executableLinear S) s
def actualGlobal (S : OddScale) (s : Word Bit (levelTwoPresentation S).Z) :
    Word Bit (levelTwoPresentation S).Q :=
  toActualError S (executableGlobal S (toExecutableSyndrome S s))
end QEC.Coding.BDL26GlobalLookupLinearity


