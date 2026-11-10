-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
-- name    : QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T01:27:31.292995+00:00
-- url     : https://prove2.me/theorems/277321bc-979d-4b23-acb8-760597ccaf2f
-- title:
--   Level Two Decoder
-- statement:
--   Definitions and structural lemmas for Level Two Decoder, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDecoder.lean

import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Encodable.Basic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
import Theorems.Thm_P2M_QEC_Coding_wordLinearMapTranspose_toLin__apply_6aba8976cbc7
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_correctionRegion_mem
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_syndromeRegion_mem
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_xqIncidenceMatrix_mul_qzIncidenceMatrix
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_coboundary0_eq
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_coboundary1_eq
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalWordPush_single
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzFace_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzQ_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzX_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzZ_card
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_map2Coord_canonicalBasis
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary0_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary1_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rxMap_commutes_coboundary0
import Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rxMap_commutes_coboundary1
import Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzMap_commutes_coboundary0
import Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzMap_commutes_coboundary1
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
attribute [local simp] QEC.Coding.BDL26RXLocalReplacement.xLocalWordPush_single
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
namespace QEC.Coding.BDL26LevelTwoDecoder
open BDL26FiniteTannerSquare BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26RXLocalReplacement BDL26TannerLocalRegularity
open BDL26RZMap1CoordinateBridge
local instance presentationXDecEq (P : TannerSquarePresentation) : DecidableEq P.X :=
  P.data.xDecidableEq
local instance presentationQDecEq (P : TannerSquarePresentation) : DecidableEq P.Q :=
  P.data.qDecidableEq
local instance presentationZDecEq (P : TannerSquarePresentation) : DecidableEq P.Z :=
  P.data.zDecidableEq
local instance presentationFaceDecEq (P : TannerSquarePresentation) : DecidableEq P.Face :=
  P.data.faceDecidableEq
local instance edgeDecEq (P : TannerSquarePresentation) :
    DecidableEq (Edge P) := by
  letI : DecidableEq P.X := P.data.xDecidableEq
  letI : DecidableEq P.Q := P.data.qDecidableEq
  letI : DecidableEq P.Z := P.data.zDecidableEq
  letI : DecidableEq P.Face := P.data.faceDecidableEq
  dsimp [Edge, XQEdge, QZEdge]
  infer_instance
local instance xStarVertexDecEq (P : TannerSquarePresentation) (x : P.X) :
    DecidableEq (XStarVertex P x) := by
  dsimp [XStarVertex]
  infer_instance
local instance xStarEdgeDecEq (P : TannerSquarePresentation) (x : P.X) :
    DecidableEq (XStarEdge P x) := by
  letI : DecidableEq (Edge P) := edgeDecEq P
  dsimp [XStarEdge]
  infer_instance
local instance xStarFaceDecEq (P : TannerSquarePresentation) (x : P.X) :
    DecidableEq (XStarFace P x) := by
  letI : DecidableEq P.Face := P.data.faceDecidableEq
  dsimp [XStarFace]
  infer_instance
local instance subdivisionVertexDecEq (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    DecidableEq (SubdivisionVertex P x S) := by
  letI : DecidableEq (XStarVertex P x) := xStarVertexDecEq P x
  letI : DecidableEq (XStarEdge P x) := xStarEdgeDecEq P x
  letI : DecidableEq (XStarFace P x) := xStarFaceDecEq P x
  dsimp [SubdivisionVertex]
  infer_instance
local instance subdivisionEdgeDecEq (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    DecidableEq (SubdivisionEdge P x S) := by
  letI : DecidableEq (XStarVertex P x) := xStarVertexDecEq P x
  letI : DecidableEq (XStarEdge P x) := xStarEdgeDecEq P x
  letI : DecidableEq (XStarFace P x) := xStarFaceDecEq P x
  dsimp [SubdivisionEdge]
  infer_instance
local instance subdivisionFaceDecEq (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    DecidableEq (SubdivisionFace P x S) := by
  letI : DecidableEq (XStarVertex P x) := xStarVertexDecEq P x
  letI : DecidableEq (XStarEdge P x) := xStarEdgeDecEq P x
  letI : DecidableEq (XStarFace P x) := xStarFaceDecEq P x
  dsimp [SubdivisionFace]
  infer_instance
local instance subdivisionBoundaryVertexDecEq (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    DecidableEq (SubdivisionBoundaryVertex P x S) := by
  letI : DecidableEq (SubdivisionVertex P x S) := subdivisionVertexDecEq P x S
  dsimp [SubdivisionBoundaryVertex]
  infer_instance
local instance subdivisionBoundaryEdgeDecEq (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    DecidableEq (SubdivisionBoundaryEdge P x S) := by
  letI : DecidableEq (SubdivisionEdge P x S) := subdivisionEdgeDecEq P x S
  dsimp [SubdivisionBoundaryEdge]
  infer_instance
local instance doubleCylinderVertexDecEq (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    DecidableEq (DoubleCylinderVertex P x S) := by
  letI : DecidableEq (SubdivisionVertex P x S) := subdivisionVertexDecEq P x S
  dsimp [DoubleCylinderVertex]
  infer_instance
local instance doubleCylinderEdgeDecEq (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    DecidableEq (DoubleCylinderEdge P x S) := by
  letI : DecidableEq (SubdivisionEdge P x S) := subdivisionEdgeDecEq P x S
  letI : DecidableEq (SubdivisionBoundaryVertex P x S) := subdivisionBoundaryVertexDecEq P x S
  dsimp [DoubleCylinderEdge]
  infer_instance
local instance doubleCylinderFaceDecEq (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    DecidableEq (DoubleCylinderFace P x S) := by
  letI : DecidableEq (SubdivisionFace P x S) := subdivisionFaceDecEq P x S
  letI : DecidableEq (SubdivisionBoundaryEdge P x S) := subdivisionBoundaryEdgeDecEq P x S
  dsimp [DoubleCylinderFace]
  infer_instance
local instance qStarEdgeDecEq (P : TannerSquarePresentation) (q : P.Q) :
    DecidableEq (QStarEdge P q) := by
  letI : DecidableEq P.Z := P.data.zDecidableEq
  dsimp [QStarEdge]
  infer_instance
local instance qStarVertexDecEq (P : TannerSquarePresentation) (q : P.Q) :
    DecidableEq (QStarVertex P q) := by
  letI : DecidableEq (QStarEdge P q) := qStarEdgeDecEq P q
  dsimp [QStarVertex]
  infer_instance
local instance qSubdivisionVertexDecEq (P : TannerSquarePresentation) (q : P.Q) (S : OddScale) :
    DecidableEq (QSubdivisionVertex P q S) := by
  letI : DecidableEq (QStarEdge P q) := qStarEdgeDecEq P q
  letI : DecidableEq (QStarVertex P q) := qStarVertexDecEq P q
  dsimp [QSubdivisionVertex]
  infer_instance
local instance qSubdivisionEdgeDecEq (P : TannerSquarePresentation) (q : P.Q) (S : OddScale) :
    DecidableEq (QSubdivisionEdge P q S) := by
  letI : DecidableEq (QStarEdge P q) := qStarEdgeDecEq P q
  letI : DecidableEq (QStarVertex P q) := qStarVertexDecEq P q
  dsimp [QSubdivisionEdge]
  infer_instance
local instance qDoubleCylinderVertexDecEq (P : TannerSquarePresentation) (q : P.Q) (S : OddScale) :
    DecidableEq (QDoubleCylinderVertex P q S) := by
  letI : DecidableEq (QSubdivisionVertex P q S) := qSubdivisionVertexDecEq P q S
  dsimp [QDoubleCylinderVertex]
  infer_instance
local instance qDoubleCylinderEdgeDecEq (P : TannerSquarePresentation) (q : P.Q) (S : OddScale) :
    DecidableEq (QDoubleCylinderEdge P q S) := by
  letI : DecidableEq (QSubdivisionEdge P q S) := qSubdivisionEdgeDecEq P q S
  letI : DecidableEq (QStarEdge P q) := qStarEdgeDecEq P q
  dsimp [QDoubleCylinderEdge]
  infer_instance
local instance rx0DecEq (P : TannerSquarePresentation) (S : OddScale) :
    DecidableEq (RX0 P S) := by
  letI : DecidableEq P.X := P.data.xDecidableEq
  letI : DecidableEq P.Q := P.data.qDecidableEq
  letI : DecidableEq P.Z := P.data.zDecidableEq
  letI : DecidableEq P.Face := P.data.faceDecidableEq
  letI : ∀ x : P.X, DecidableEq (DoubleCylinderVertex P x S) := fun x => doubleCylinderVertexDecEq P x S
  letI : ∀ x : P.X, DecidableEq (DoubleCylinderEdge P x S) := fun x => doubleCylinderEdgeDecEq P x S
  letI : ∀ x : P.X, DecidableEq (DoubleCylinderFace P x S) := fun x => doubleCylinderFaceDecEq P x S
  letI : ∀ q : P.Q, DecidableEq (QDoubleCylinderVertex P q S) := fun q => qDoubleCylinderVertexDecEq P q S
  letI : ∀ q : P.Q, DecidableEq (QDoubleCylinderEdge P q S) := fun q => qDoubleCylinderEdgeDecEq P q S
  dsimp [RX0]
  infer_instance
local instance rx1DecEq (P : TannerSquarePresentation) (S : OddScale) :
    DecidableEq (RX1 P S) := by
  letI : DecidableEq P.X := P.data.xDecidableEq
  letI : DecidableEq P.Q := P.data.qDecidableEq
  letI : DecidableEq P.Z := P.data.zDecidableEq
  letI : DecidableEq P.Face := P.data.faceDecidableEq
  letI : ∀ x : P.X, DecidableEq (DoubleCylinderVertex P x S) := fun x => doubleCylinderVertexDecEq P x S
  letI : ∀ x : P.X, DecidableEq (DoubleCylinderEdge P x S) := fun x => doubleCylinderEdgeDecEq P x S
  letI : ∀ x : P.X, DecidableEq (DoubleCylinderFace P x S) := fun x => doubleCylinderFaceDecEq P x S
  letI : ∀ q : P.Q, DecidableEq (QDoubleCylinderVertex P q S) := fun q => qDoubleCylinderVertexDecEq P q S
  letI : ∀ q : P.Q, DecidableEq (QDoubleCylinderEdge P q S) := fun q => qDoubleCylinderEdgeDecEq P q S
  dsimp [RX1]
  infer_instance
local instance rx2DecEq (P : TannerSquarePresentation) (S : OddScale) :
    DecidableEq (RX2 P S) := by
  letI : DecidableEq P.X := P.data.xDecidableEq
  letI : DecidableEq P.Q := P.data.qDecidableEq
  letI : DecidableEq P.Z := P.data.zDecidableEq
  letI : DecidableEq P.Face := P.data.faceDecidableEq
  letI : ∀ x : P.X, DecidableEq (DoubleCylinderVertex P x S) := fun x => doubleCylinderVertexDecEq P x S
  letI : ∀ x : P.X, DecidableEq (DoubleCylinderEdge P x S) := fun x => doubleCylinderEdgeDecEq P x S
  letI : ∀ x : P.X, DecidableEq (DoubleCylinderFace P x S) := fun x => doubleCylinderFaceDecEq P x S
  letI : ∀ q : P.Q, DecidableEq (QDoubleCylinderVertex P q S) := fun q => qDoubleCylinderVertexDecEq P q S
  letI : ∀ q : P.Q, DecidableEq (QDoubleCylinderEdge P q S) := fun q => qDoubleCylinderEdgeDecEq P q S
  dsimp [RX2]
  infer_instance
local instance rxLocalFaceDecEq (P : TannerSquarePresentation) (S : OddScale) :
    DecidableEq (RXLocalFace P S) := by
  letI : DecidableEq P.X := P.data.xDecidableEq
  letI : ∀ x : P.X, DecidableEq (DoubleCylinderFace P x S) :=
    fun x => doubleCylinderFaceDecEq P x S
  dsimp [RXLocalFace]
  infer_instance
local instance rxGlueFaceDecEq (P : TannerSquarePresentation) (S : OddScale) :
    DecidableEq (RXXQGlueFace P S) := by
  letI : DecidableEq (XQEdge P) := by
    letI : DecidableEq P.X := P.data.xDecidableEq
    letI : DecidableEq P.Q := P.data.qDecidableEq
    dsimp [XQEdge]
    infer_instance
  letI : ∀ q : P.Q, DecidableEq (QDoubleCylinderEdge P q S) :=
    fun q => qDoubleCylinderEdgeDecEq P q S
  dsimp [RXXQGlueFace]
  infer_instance
local instance rxFaceDecEq (P : TannerSquarePresentation) (S : OddScale) :
    DecidableEq (RXFace P S) := by
  letI : DecidableEq (RXLocalFace P S) := rxLocalFaceDecEq P S
  letI : DecidableEq (RXXQGlueFace P S) := rxGlueFaceDecEq P S
  letI : DecidableEq (RXOldZFace P) := by
    letI : DecidableEq P.Face := P.data.faceDecidableEq
    dsimp [RXOldZFace]
    infer_instance
  dsimp [RXFace]
  infer_instance
def rxFaceXExecutable (P : TannerSquarePresentation) (S : OddScale) :
    RXFace P S → RX0 P S
  | .inl ⟨x, .inl copyFace, corner⟩ =>
      ⟨x, (copyFace.1, subdivisionGridVertex P x S copyFace.2.1
        (BDL26RXLocalReplacement.gridEndpoint copyFace.2.2.1 corner.1)
        (BDL26RXLocalReplacement.gridEndpoint copyFace.2.2.2 corner.2))⟩
  | .inl ⟨x, .inr rectangle, corner⟩ =>
      ⟨x, doubleCylinderRectangleCorner P x S rectangle corner⟩
  | .inr (.inl face) => BDL26RXLocalReplacement.glueFaceX P S face
  | .inr (.inr face) => oldZFaceX P S face
theorem rxFaceXExecutable_eq (P : TannerSquarePresentation) (S : OddScale) :
    rxFaceXExecutable P S = rxFaceX P S := by
  funext face
  rcases face with ⟨x, cell, corner⟩ | glue | old
  · cases cell <;> rfl
  · rfl
  · rfl
def rxFaceQExecutable (P : TannerSquarePresentation) (S : OddScale) :
    RXFace P S → BDL26FiniteTannerSquare.Two → RX1 P S
  | .inl ⟨x, .inl copyFace, corner⟩, bit =>
      .inl ⟨x, .inl (copyFace.1, subdivisionFaceBoundaryEdge P x S copyFace.2
        (if bit = 0 then (0, corner.2) else (1, corner.1)))⟩
  | .inl ⟨x, .inr rectangle, corner⟩, bit =>
      .inl ⟨x, doubleCylinderRectangleBoundaryEdge P x S rectangle
        (if bit = 0 then (0, corner.1) else (1, corner.2))⟩
  | .inr (.inl face), bit =>
      BDL26RXLocalReplacement.twoSelect
        (BDL26RXLocalReplacement.glueFaceQ0 P S face)
        (BDL26RXLocalReplacement.glueFaceQ1 P S face) bit
  | .inr (.inr face), bit => oldZFaceQ P S bit face
theorem rxFaceQExecutable_eq (P : TannerSquarePresentation) (S : OddScale) :
    rxFaceQExecutable P S = rxFaceQ P S := by
  funext face bit
  rcases face with ⟨x, cell, corner⟩ | glue | old
  · cases cell <;> by_cases h : bit = 0 <;>
      simp [rxFaceQExecutable, rxFaceQ, BDL26RXLocalReplacement.twoSelect,
        BDL26RXLocalReplacement.localFaceQ0, BDL26RXLocalReplacement.localFaceQ1,
        localFaceQ0Edge, localFaceQ1Edge, localFaceQ0EdgeAt, localFaceQ1EdgeAt, h]
  · rfl
  · rfl
theorem decide_congr_explicit (p q : Prop) (dp : Decidable p) (dq : Decidable q)
    (h : p ↔ q) : @decide p dp = @decide q dq := by
  cases dp <;> cases dq <;> simp_all
def rxXQExecutable (P : TannerSquarePresentation) (S : OddScale)
    (x : RX0 P S) (q : RX1 P S) : Bool :=
  decide (∃ f : RXFace P S, ∃ i : BDL26FiniteTannerSquare.Two,
    rxFaceXExecutable P S f = x ∧ rxFaceQExecutable P S f i = q)
def rxQZExecutable (P : TannerSquarePresentation) (S : OddScale)
    (q : RX1 P S) (z : RX2 P S) : Bool :=
  decide (∃ f : RXFace P S, ∃ i : BDL26FiniteTannerSquare.Two,
    rxFaceQExecutable P S f i = q ∧ rxFaceZ P S f = z)
theorem rxXQExecutable_eq (P : TannerSquarePresentation) (S : OddScale) :
    rxXQExecutable P S = rxXQIncidence P S := by
  funext x q
  unfold rxXQExecutable rxXQIncidence
  exact decide_congr_explicit _ _ _ _ (by
    simp only [rxFaceXExecutable_eq, rxFaceQExecutable_eq])
theorem rxQZExecutable_eq (P : TannerSquarePresentation) (S : OddScale) :
    rxQZExecutable P S = rxQZIncidence P S := by
  funext q z
  unfold rxQZExecutable rxQZIncidence
  exact decide_congr_explicit _ _ _ _ (by
    simp only [rxFaceQExecutable_eq])
def rxDataExecutable (P : TannerSquarePresentation) (S : OddScale) :
    TannerSquareData where
  X := RX0 P S
  Q := RX1 P S
  Z := RX2 P S
  Face := RXFace P S
  xFintype := inferInstance
  qFintype := inferInstance
  zFintype := inferInstance
  faceFintype := inferInstance
  xDecidableEq := inferInstance
  qDecidableEq := inferInstance
  zDecidableEq := inferInstance
  faceDecidableEq := inferInstance
  xq := rxXQExecutable P S
  qz := rxQZExecutable P S
  faceX := rxFaceXExecutable P S
  faceQ := rxFaceQExecutable P S
  faceZ := rxFaceZ P S
  faceQ_xq := by
    intro f i
    apply decide_eq_true
    exact ⟨f, i, rfl, rfl⟩
  faceQ_qz := by
    intro f i
    apply decide_eq_true
    exact ⟨f, i, rfl, rfl⟩
theorem rxDataExecutable_eq (P : TannerSquarePresentation) (S : OddScale) :
    rxDataExecutable P S = rxReplacementData P S := by
  unfold rxDataExecutable rxReplacementData
  simp only [rxXQExecutable_eq, rxQZExecutable_eq,
    rxFaceXExecutable_eq, rxFaceQExecutable_eq]
  congr 1 <;> exact Subsingleton.elim _ _
def rxPresentationExecutable (P : TannerSquarePresentation) (S : OddScale) :
    TannerSquarePresentation where
  data := rxDataExecutable P S
  perfectPairing := by
    rw [rxDataExecutable_eq]
    exact rxReplacementPerfectPairing P S
theorem rxPresentationExecutable_eq (P : TannerSquarePresentation) (S : OddScale) :
    rxPresentationExecutable P S = rxReplacementPresentation P S := by
  unfold rxPresentationExecutable rxReplacementPresentation
  congr 1
  exact rxDataExecutable_eq P S
def transposeExecutable (P : TannerSquarePresentation) : TannerSquarePresentation where
  data := transposeTannerSquareData P
  perfectPairing := (transposePresentation P).perfectPairing
def qToZVertexExecutable (P : TannerSquarePresentation)
    (hasA : Nonempty (TannerSquareAdmissible P))
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    QDoubleCylinderVertex (transposePresentation P) q S →
      ZDoubleCylinderVertex P z S
  | (copy, .inl (.inl _)) =>
      (copy, .inl ⟨Vertex.q q, by
        obtain ⟨A⟩ := hasA
        exact (xStarBoundaryVertexToStar (transposePresentation P) z
          ((transposeXStarBoundaryVertexEquiv P z).symm
            (qToZBoundaryVertex P A q z hqz (.inl ())))).property⟩)
  | (copy, .inl (.inr edge)) =>
      (copy, .inl ⟨Vertex.z edge.1, by
        obtain ⟨A⟩ := hasA
        exact (xStarBoundaryVertexToStar (transposePresentation P) z
          ((transposeXStarBoundaryVertexEquiv P z).symm
            (qToZBoundaryVertex P A q z hqz (.inr edge)))).property⟩)
  | (copy, .inr edgeInterior) =>
      (copy, .inr (.inl (⟨.inr ⟨(q, edgeInterior.1.1), edgeInterior.1.2⟩, by
        obtain ⟨A⟩ := hasA
        exact (xStarBoundaryEdgeToStar (transposePresentation P) z
          ((transposeXStarBoundaryEdgeEquiv P z).symm
            (qToZBoundaryEdge P q z hqz edgeInterior.1))).property⟩,
        edgeInterior.2)))
def cylinderVertexMatrixExecutable (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :
    DoubleCylinderVertex P x S → DoubleCylinderEdge P x S → ZMod 2
  | v, .inl e =>
      if v.1 = e.1 then
        (if v.2 = subdivisionEdgeStart P x S e.2 then 1 else 0) +
          (if v.2 = subdivisionEdgeEnd P x S e.2 then 1 else 0)
      else 0
  | v, .inr endpoint => if v.2 = endpoint.1 then 1 else 0
local instance zCylinderVertexDecEq (P : TannerSquarePresentation) (z : P.Z)
    (S : OddScale) : DecidableEq (ZDoubleCylinderVertex P z S) := by
  letI : DecidableEq (SubdivisionVertex (transposePresentation P) z S) :=
    subdivisionVertexDecEq (transposeExecutable P) z S
  change DecidableEq (BDL26FiniteTannerSquare.Two ×
    SubdivisionVertex (transposePresentation P) z S)
  infer_instance
local instance rzQExecutableFintype (P : TannerSquarePresentation) (S : OddScale) :
    Fintype (BDL26RZLocalReplacement.RZQ P S) := by
  dsimp [BDL26RZLocalReplacement.RZQ, ZDoubleCylinderEdge, QDoubleCylinderVertex,
    DoubleCylinderEdge, transposePresentation, transposeTannerSquareData]
  infer_instance
def rzIncidenceExecutable (P : TannerSquarePresentation)
    (hasA : Nonempty (TannerSquareAdmissible P)) (S : OddScale) :
    BDL26RZLocalReplacement.RZQ P S → BDL26RZLocalReplacement.RZZ P S → Bool
  | .inl e, v =>
      if h : v.1 = e.1 then
        decide (cylinderVertexMatrixExecutable (transposeExecutable P) e.1 S
          (h ▸ v.2) e.2 = 1)
      else false
  | .inr q, v =>
      if h : P.qz q.1 v.1 = true then
        decide (qToZVertexExecutable P hasA q.1 v.1 h S q.2 = v.2)
      else false
instance vertexEncodable (P : TannerSquarePresentation)
    [Encodable P.X] [Encodable P.Q] [Encodable P.Z] : Encodable (Vertex P) :=
  Encodable.ofEquiv (P.X ⊕ (P.Q ⊕ P.Z))
    { toFun := fun v => match v with
        | .x x => .inl x
        | .q q => .inr (.inl q)
        | .z z => .inr (.inr z)
      invFun := fun v => match v with
        | .inl x => .x x
        | .inr (.inl q) => .q q
        | .inr (.inr z) => .z z
      left_inv := by intro v; cases v <;> rfl
      right_inv := by rintro (x | q | z) <;> rfl }
def coordinates (α : Type) [Fintype α] [Encodable α] : List α :=
  letI : LinearOrder α := LinearOrder.lift' Encodable.encode Encodable.encode_injective
  Finset.univ.sort
def wordsOn {α : Type} [DecidableEq α] : List α → List (Word (ZMod 2) α)
  | [] => [0]
  | q :: rest =>
      (wordsOn rest).map (fun e => Function.update e q 0) ++
        (wordsOn rest).map (fun e => Function.update e q 1)
def allWords (α : Type) [Fintype α] [Encodable α] [DecidableEq α] :
    List (Word (ZMod 2) α) := wordsOn (coordinates α)
def search {α : Type} (accept : α → Bool) : List α → Option α
  | [] => none
  | a :: rest => if accept a then some a else search accept rest
def lookup {Error Syndrome : Type} [DecidableEq Syndrome]
    (entries : List Error) (syndrome : Error → Syndrome)
    (isLocal : Error → Bool) (fallback : Error) (sigma : Syndrome) : Error :=
  match search (fun e => isLocal e && decide (syndrome e = sigma)) entries with
  | some e => e
  | none => (search (fun e => decide (syndrome e = sigma)) entries).getD fallback
local instance baseXEncodable : Encodable baseTannerSquarePresentation.X :=
  inferInstanceAs (Encodable (Fin 2))
local instance baseQEncodable : Encodable baseTannerSquarePresentation.Q :=
  inferInstanceAs (Encodable (Fin 5))
local instance baseZEncodable : Encodable baseTannerSquarePresentation.Z :=
  inferInstanceAs (Encodable (Fin 2))
local instance baseFaceEncodable : Encodable baseTannerSquarePresentation.Face :=
  inferInstanceAs (Encodable (Fin 4))
local instance subdivisionVertexEncodable (P : TannerSquarePresentation)
    [Encodable P.X] [Encodable P.Q] [Encodable P.Z] [Encodable P.Face]
    (x : P.X) (S : OddScale) : Encodable (SubdivisionVertex P x S) := by
  dsimp [SubdivisionVertex, XStarVertex, XStarEdge, XStarFace, Edge, XQEdge, QZEdge]
  infer_instance
local instance subdivisionEdgeEncodable (P : TannerSquarePresentation)
    [Encodable P.X] [Encodable P.Q] [Encodable P.Z] [Encodable P.Face]
    (x : P.X) (S : OddScale) : Encodable (SubdivisionEdge P x S) := by
  dsimp [SubdivisionEdge, XStarEdge, XStarFace, Edge, XQEdge, QZEdge]
  infer_instance
def executableLevelOne (S : OddScale) : TannerSquarePresentation :=
  rxPresentationExecutable baseTannerSquarePresentation S
theorem executableLevelOne_eq (S : OddScale) :
    executableLevelOne S = levelOnePresentation S :=
  rxPresentationExecutable_eq baseTannerSquarePresentation S
instance executableLevelOneXEncodable (S : OddScale) :
    Encodable (executableLevelOne S).X := by
  change Encodable (RX0 baseTannerSquarePresentation S)
  dsimp [RX0, RXLocalFace, RXXQGlueFace, RXOldZFace,
    DoubleCylinderVertex, DoubleCylinderEdge, DoubleCylinderFace,
    SubdivisionVertex, SubdivisionEdge, SubdivisionFace,
    SubdivisionBoundaryVertex, SubdivisionBoundaryEdge,
    XStarVertex, XStarEdge, XStarFace, Edge, XQEdge, QZEdge,
    QDoubleCylinderVertex, QDoubleCylinderEdge, QSubdivisionVertex,
    QSubdivisionEdge, QStarVertex, QStarEdge]
  infer_instance
instance executableLevelOneQEncodable (S : OddScale) :
    Encodable (executableLevelOne S).Q := by
  change Encodable (RX1 baseTannerSquarePresentation S)
  dsimp [RX1, RXLocalFace, RXXQGlueFace, RXOldZFace,
    DoubleCylinderVertex, DoubleCylinderEdge, DoubleCylinderFace,
    SubdivisionVertex, SubdivisionEdge, SubdivisionFace,
    SubdivisionBoundaryVertex, SubdivisionBoundaryEdge,
    XStarVertex, XStarEdge, XStarFace, Edge, XQEdge, QZEdge,
    QDoubleCylinderVertex, QDoubleCylinderEdge, QSubdivisionVertex,
    QSubdivisionEdge, QStarVertex, QStarEdge]
  infer_instance
instance executableLevelOneZEncodable (S : OddScale) :
    Encodable (executableLevelOne S).Z := by
  change Encodable (RX2 baseTannerSquarePresentation S)
  dsimp [RX2, RXLocalFace, RXXQGlueFace, RXOldZFace,
    DoubleCylinderVertex, DoubleCylinderEdge, DoubleCylinderFace,
    SubdivisionVertex, SubdivisionEdge, SubdivisionFace,
    SubdivisionBoundaryVertex, SubdivisionBoundaryEdge,
    XStarVertex, XStarEdge, XStarFace, Edge, XQEdge, QZEdge,
    QDoubleCylinderVertex, QDoubleCylinderEdge, QSubdivisionVertex,
    QSubdivisionEdge, QStarVertex, QStarEdge]
  infer_instance
instance executableLevelOneFaceEncodable (S : OddScale) :
    Encodable (executableLevelOne S).Face := by
  change Encodable (RXFace baseTannerSquarePresentation S)
  dsimp [RXFace, RXLocalFace, RXXQGlueFace, RXOldZFace,
    DoubleCylinderVertex, DoubleCylinderEdge, DoubleCylinderFace,
    SubdivisionVertex, SubdivisionEdge, SubdivisionFace,
    SubdivisionBoundaryVertex, SubdivisionBoundaryEdge,
    XStarVertex, XStarEdge, XStarFace, Edge, XQEdge, QZEdge,
    QDoubleCylinderVertex, QDoubleCylinderEdge, QSubdivisionVertex,
    QSubdivisionEdge, QStarVertex, QStarEdge]
  infer_instance
abbrev ExecutableQ (S : OddScale) :=
  BDL26RZLocalReplacement.RZQ (executableLevelOne S) S
abbrev ExecutableZ (S : OddScale) :=
  BDL26RZLocalReplacement.RZZ (executableLevelOne S) S
instance executableQFintype (S : OddScale) : Fintype (ExecutableQ S) := by
  dsimp [ExecutableQ, BDL26RZLocalReplacement.RZQ, ZDoubleCylinderEdge,
    DoubleCylinderEdge, QDoubleCylinderVertex, transposePresentation,
    transposeTannerSquareData]
  infer_instance
instance executableZFintype (S : OddScale) : Fintype (ExecutableZ S) := by
  dsimp [ExecutableZ, BDL26RZLocalReplacement.RZZ, ZDoubleCylinderVertex,
    DoubleCylinderVertex, transposePresentation, transposeTannerSquareData]
  infer_instance
instance executableQDecidableEq (S : OddScale) : DecidableEq (ExecutableQ S) := by
  let P := executableLevelOne S
  letI : DecidableEq P.Z := P.data.zDecidableEq
  letI : DecidableEq P.Q := P.data.qDecidableEq
  letI : ∀ z : P.Z, DecidableEq (ZDoubleCylinderEdge P z S) :=
    fun z => doubleCylinderEdgeDecEq (transposeExecutable P) z S
  letI : ∀ q : P.Q, DecidableEq (QDoubleCylinderVertex (transposePresentation P) q S) :=
    fun q => qDoubleCylinderVertexDecEq (transposeExecutable P) q S
  change DecidableEq (((z : P.Z) × ZDoubleCylinderEdge P z S) ⊕
    ((q : P.Q) × QDoubleCylinderVertex (transposePresentation P) q S))
  infer_instance
instance executableZDecidableEq (S : OddScale) : DecidableEq (ExecutableZ S) := by
  let P := executableLevelOne S
  letI : DecidableEq P.Z := P.data.zDecidableEq
  letI : ∀ z : P.Z, DecidableEq (ZDoubleCylinderVertex P z S) :=
    fun z => zCylinderVertexDecEq P z S
  change DecidableEq ((z : P.Z) × ZDoubleCylinderVertex P z S)
  infer_instance
instance executableQEncodable (S : OddScale) : Encodable (ExecutableQ S) := by
  dsimp [ExecutableQ, BDL26RZLocalReplacement.RZQ, ZDoubleCylinderEdge,
    DoubleCylinderEdge, QDoubleCylinderVertex, transposePresentation,
    transposeTannerSquareData]
  infer_instance
theorem executableLevelOne_admissible (S : OddScale) :
    Nonempty (TannerSquareAdmissible (executableLevelOne S)) := by
  rw [executableLevelOne_eq]
  exact ⟨(BDL26DecodingGraph.rxState S BDL26DecodingGraph.baseState).admissible.toTannerSquareAdmissible⟩
open scoped BigOperators
def syndromeFromBits {Q Z : Type} (F : Fintype Q) (incidence : Q → Z → Bool)
    (e : Word (ZMod 2) Q) : Word (ZMod 2) Z := fun z =>
  ∑ q ∈ F.elems, if incidence q z then e q else 0
def rawSyndrome (P : TannerSquarePresentation)
    (hasA : Nonempty (TannerSquareAdmissible P)) (S : OddScale)
    (e : Word (ZMod 2) (BDL26RZLocalReplacement.RZQ P S)) :
    Word (ZMod 2) (BDL26RZLocalReplacement.RZZ P S) :=
  syndromeFromBits (rzQExecutableFintype P S) (rzIncidenceExecutable P hasA S) e
def rawLocal (P : TannerSquarePresentation) (S : OddScale)
    (e : Word (ZMod 2) (BDL26RZLocalReplacement.RZQ P S)) : Bool :=
  decide (∃ center : Vertex P, ∀ q, e q ≠ 0 →
    BDL26ReplacementSupport.rzCorrectionOwner P S q = center)
def executableSyndrome (S : OddScale) (e : Word (ZMod 2) (ExecutableQ S)) :
    Word (ZMod 2) (ExecutableZ S) :=
  rawSyndrome (executableLevelOne S) (executableLevelOne_admissible S) S e
def executableLocal (S : OddScale) (e : Word (ZMod 2) (ExecutableQ S)) : Bool :=
  rawLocal (executableLevelOne S) S e
def executableDecode (S : OddScale) (sigma : Word (ZMod 2) (ExecutableZ S)) :
    Word (ZMod 2) (ExecutableQ S) :=
  lookup (allWords (ExecutableQ S)) (executableSyndrome S)
    (executableLocal S) 0 sigma
theorem executableQ_eq (S : OddScale) :
    ExecutableQ S = (levelTwoPresentation S).Q := by
  change BDL26RZLocalReplacement.RZQ (executableLevelOne S) S =
    BDL26RZLocalReplacement.RZQ (levelOnePresentation S) S
  rw [executableLevelOne_eq]
theorem executableZ_eq (S : OddScale) :
    ExecutableZ S = (levelTwoPresentation S).Z := by
  change BDL26RZLocalReplacement.RZZ (executableLevelOne S) S =
    BDL26RZLocalReplacement.RZZ (levelOnePresentation S) S
  rw [executableLevelOne_eq]
def toExecutableError (S : OddScale)
    (e : Word (ZMod 2) (levelTwoPresentation S).Q) : Word (ZMod 2) (ExecutableQ S) :=
  fun q => e (cast (executableQ_eq S) q)
def toActualError (S : OddScale) (e : Word (ZMod 2) (ExecutableQ S)) :
    Word (ZMod 2) (levelTwoPresentation S).Q :=
  fun q => e (cast (executableQ_eq S).symm q)
def toExecutableSyndrome (S : OddScale)
    (sigma : Word (ZMod 2) (levelTwoPresentation S).Z) :
    Word (ZMod 2) (ExecutableZ S) :=
  fun z => sigma (cast (executableZ_eq S) z)
@[simp] theorem toActualError_toExecutableError (S : OddScale)
    (e : Word (ZMod 2) (levelTwoPresentation S).Q) :
    toActualError S (toExecutableError S e) = e := by
  funext q
  simp [toActualError, toExecutableError]
@[simp] theorem toExecutableError_toActualError (S : OddScale)
    (e : Word (ZMod 2) (ExecutableQ S)) :
    toExecutableError S (toActualError S e) = e := by
  funext q
  simp [toActualError, toExecutableError]
def decode (S : OddScale) (sigma : Word (ZMod 2) (levelTwoPresentation S).Z) :
    Word (ZMod 2) (levelTwoPresentation S).Q :=
  toActualError S (executableDecode S (toExecutableSyndrome S sigma))
open MultiscaleDecoder BDL26DecodingGraph BDL26ReplacementCochainMaps
noncomputable def presentationComplex (P : TannerSquarePresentation) :
    ChainComplexData (ZMod 2) (Word (ZMod 2) P.X)
      (Word (ZMod 2) P.Q) (Word (ZMod 2) P.Z) where
  boundary1 := Matrix.toLin' (xqIncidenceMatrix P)
  boundary2 := Matrix.toLin' (qzIncidenceMatrix P)
  boundary_squared := by
    rw [← Matrix.toLin'_mul, xqIncidenceMatrix_mul_qzIncidenceMatrix]
    simp
abbrev FamilyX (S : OddScale) (i : LevelIndex 2) := (state S i.val).presentation.X
abbrev FamilyQ (S : OddScale) (i : LevelIndex 2) := (state S i.val).presentation.Q
abbrev FamilyZ (S : OddScale) (i : LevelIndex 2) := (state S i.val).presentation.Z
noncomputable def decoderFamily (S : OddScale) :
    BDL26CochainFamily 2 (FamilyX S) (FamilyQ S) (FamilyZ S) where
  complex := fun i => presentationComplex (state S i.val).presentation
theorem decoderFamily_coboundary0 (S : OddScale) (i : LevelIndex 2) :
    (decoderFamily S).coboundary0 i = tannerCoboundary0 (state S i.val).presentation := by
  apply LinearMap.ext
  intro e
  funext q
  exact wordLinearMapTranspose_toLin'_apply _ e q
theorem decoderFamily_coboundary1 (S : OddScale) (i : LevelIndex 2) :
    (decoderFamily S).coboundary1 i = tannerCoboundary1 (state S i.val).presentation := by
  apply LinearMap.ext
  intro e
  funext z
  exact wordLinearMapTranspose_toLin'_apply _ e z
noncomputable def decoderRZEdgeMap (S : OddScale) :
    BDL26CochainMap (decoderFamily S) (1 : StepIndex 2) := by
  let P := levelOnePresentation S
  let A := (rxState S baseState).admissible
  refine
    { map0 := (rzCochainMap P A S).map0
      map1 := (rzCochainMap P A S).map1
      map2 := (rzCochainMap P A S).map2
      commutes_coboundary0 := ?_
      commutes_coboundary1 := ?_ }
  · rw [decoderFamily_coboundary0, decoderFamily_coboundary0]
    exact rzMap_commutes_coboundary0 P A S
  · rw [decoderFamily_coboundary1, decoderFamily_coboundary1]
    exact rzMap_commutes_coboundary1 P A S
noncomputable def decoderEdgeMap (S : OddScale) (i : StepIndex 2) :
    BDL26CochainMap (decoderFamily S) i := by
  rcases i with ⟨n, hn⟩
  rcases n with _ | n
  · refine
      { map0 := (rxMap baseTannerSquarePresentation S).map0
        map1 := (rxMap baseTannerSquarePresentation S).map1
        map2 := (rxMap baseTannerSquarePresentation S).map2
        commutes_coboundary0 := ?_
        commutes_coboundary1 := ?_ }
    · rw [decoderFamily_coboundary0, decoderFamily_coboundary0]
      change (tannerCoboundary0 (rxReplacementPresentation baseTannerSquarePresentation S)).comp _ = _
      rw [rxPresentation_coboundary0_eq baseTannerSquarePresentation
        baseTannerSquareAdmissibleV4 baseTannerSquareCellularRegular S]
      exact rxMap_commutes_coboundary0 baseTannerSquarePresentation
        baseTannerSquareAdmissibleV4.toTannerSquareAdmissible S
    · rw [decoderFamily_coboundary1, decoderFamily_coboundary1]
      change (tannerCoboundary1 (rxReplacementPresentation baseTannerSquarePresentation S)).comp _ = _
      rw [rxPresentation_coboundary1_eq baseTannerSquarePresentation
        baseTannerSquareAdmissibleV4 baseTannerSquareCellularRegular S]
      exact rxMap_commutes_coboundary1 baseTannerSquarePresentation S
  · rcases n with _ | n
    · exact decoderRZEdgeMap S
    · omega
noncomputable def decoderData (S : OddScale) :
    BDL26DecoderData 2 (FamilyX S) (FamilyQ S) (FamilyZ S) where
  family := decoderFamily S
  rxMap := decoderEdgeMap S
  rzMap := decoderEdgeMap S
noncomputable def baseAdapter (S : OddScale) :
    F17LevelTwoBaseAdapterV2 (decoderData S) (decodingGraph S 2) (by decide) where
  decode := fun sigma => decode S sigma.1
end QEC.Coding.BDL26LevelTwoDecoder


