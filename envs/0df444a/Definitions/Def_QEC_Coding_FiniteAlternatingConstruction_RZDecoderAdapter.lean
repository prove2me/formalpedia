-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
-- name    : QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T05:53:40.125278+00:00
-- url     : https://prove2.me/theorems/a1ee6e1a-9378-4c34-91a7-707f53b2c164
-- title:
--   RZDecoder Adapter
-- statement:
--   Definitions and structural lemmas for RZDecoder Adapter, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZDecoderAdapter.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZSupportedBoundary
import Theorems.Thm_P2M_QEC_Coding_wordLinearMapTranspose_toLin__apply_6aba8976cbc7
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_correctionRegion_mem
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_syndromeRegion_mem
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
import Theorems.Thm_QEC_Coding_BDL26IndexedDecoder_indexedDecoderData_selected_rz
import Theorems.Thm_QEC_Coding_BDL26IndexedDecoder_selectedMap_eq
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rzCoboundary1_blockParity
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalWordPush_single
import Theorems.Thm_QEC_Coding_BDL26RZConcreteParity_blockParity_eq_region_sum
import Theorems.Thm_QEC_Coding_BDL26RZConcreteParity_blockParity_map2
import Theorems.Thm_QEC_Coding_BDL26RZConcreteParity_blockRegion_disjoint
import Theorems.Thm_QEC_Coding_BDL26RZConcreteParity_rootLift_support
import Theorems.Thm_QEC_Coding_BDL26RZConcreteParity_sum_rootLift
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzFace_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzQ_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzX_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzZ_card
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_map2Coord_canonicalBasis
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary0_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary1_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26RZSupportedBoundary_quotientEquiv_mkQ
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
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_localComputabilityCertificate
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_rz_exact_relation_selected
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
namespace QEC.Coding.BDL26RZDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementSupport BDL26RZConcreteParity BDL26LevelTwoDistance
open MultiscaleDecoder RZCoarseGraining RZCoarseGrainingData
open BDL26AlternatingCochain BDL26ReplacementCochainMaps
open scoped Classical BigOperators
universe u
noncomputable local instance rzQDecEq (P : TannerSquarePresentation) (S : OddScale) :
    DecidableEq (RZQ P S) := Classical.decEq _
noncomputable local instance rzZDecEq (P : TannerSquarePresentation) (S : OddScale) :
    DecidableEq (RZZ P S) := Classical.decEq _
def blockCorrectionOwner (P : TannerSquarePresentation) (S : OddScale) :
    RZQ P S → Option (Vertex P)
  | .inl ⟨z, _⟩ => some (.z z)
  | .inr _ => none
theorem blockCorrectionOwner_region (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) :
    BDL26RZSupportedBoundary.correctionRegion P S z =
      Finset.univ.filter (fun q => blockCorrectionOwner P S q = some (.z z)) := by
  ext q
  simp only [BDL26RZSupportedBoundary.correctionRegion, fiberRegion,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rcases q with ⟨w,e⟩ | ⟨q,v⟩
  · change (Vertex.z w = Vertex.z z) ↔ (some (Vertex.z w) = some (Vertex.z z))
    simp only [Option.some.injEq]
  · change (Vertex.q q = Vertex.z z) ↔ (none = some (Vertex.z z))
    simp
theorem rootLift_outside (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (z : P.Z)
    (b : BDL26Field) (p : RZZ P S) (hp : p ∉ blockRegion P S z) :
    rootLift P A S z b p = 0 := by
  by_contra hn
  exact hp (rootLift_support P A S z b (by simpa [hammingSupport] using hn))
theorem rootLift_region_parity (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (z : P.Z) (b : BDL26Field) :
    (∑ p ∈ blockRegion P S z, rootLift P A S z b p) = b := by
  rw [← blockParity_eq_region_sum, rootLift, blockParity_map2]
  simp
theorem block_radius (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (p : RZZ P S) (hp : p ∈ blockRegion P S z) :
    DirectedGraph.distance (tannerLevel P).graph (.z p.1) (.z z) = 0 := by
  have hz : p.1 = z := (Finset.mem_filter.mp hp).2
  rw [hz]
  let G := (tannerLevel P).graph
  let v : Vertex P := .z z
  have hreach : ∀ n, DirectedGraph.reachableWithin G n v v = true := by
    intro n
    induction n with
    | zero => simp [DirectedGraph.reachableWithin]
    | succ n ih => simp [DirectedGraph.reachableWithin, ih]
  have haux : ∀ n, DirectedGraph.distanceAux G v v n = some 0 := by
    intro n
    induction n with
    | zero => simp [DirectedGraph.distanceAux, hreach]
    | succ n ih => simp [DirectedGraph.distanceAux, ih, hreach]
  change DirectedGraph.distance G v v = 0
  simp [DirectedGraph.distance, haux]
structure EndpointData (P U : TannerSquarePresentation) where
  topCenter : U.Z → Vertex P
  owner : U.Q → Option (Vertex P)
  region : P.Z → Finset U.Z
  corrections : P.Z → Finset U.Q
  lift : P.Z → BDL26Field → Word BDL26Field U.Z
  map2 : Word BDL26Field P.Z →ₗ[BDL26Field] Word BDL26Field U.Z
  projection : Word BDL26Field U.Q →ₗ[BDL26Field] Word BDL26Field P.Q
  cover : ∀ p, ∃ z, p ∈ region z
  disjoint : ∀ z w, z ≠ w → Disjoint (region z) (region w)
  corrections_disjoint : ∀ z w, z ≠ w → Disjoint (corrections z) (corrections w)
  coherence : ∀ z, corrections z = Finset.univ.filter (fun q => owner q = some (.z z))
  lift_supported : ∀ z b p, p ∉ region z → lift z b p = 0
  lift_parity : ∀ z b, (∑ p ∈ region z, lift z b p) = b
  decomposition : ∀ sigma, map2 sigma = ∑ z, lift z (sigma z)
  boundary_supported : ∀ z (f : Word BDL26Field U.Q),
    (∀ q, q ∉ corrections z → f q = 0) →
      ∀ p, p ∉ region z → tannerCoboundary1 U f p = 0
  radius : ∀ z p, p ∈ region z →
    DirectedGraph.distance (tannerLevel P).graph (topCenter p) (.z z) = 0
theorem blockRegion_cover (P : TannerSquarePresentation) (S : OddScale) :
    ∀ p : RZZ P S, ∃ z : P.Z, p ∈ blockRegion P S z := by
  intro p
  exact ⟨p.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
theorem corrections_disjoint (P : TannerSquarePresentation) (S : OddScale) :
    ∀ z w : P.Z, z ≠ w → Disjoint
      (BDL26RZSupportedBoundary.correctionRegion P S z)
      (BDL26RZSupportedBoundary.correctionRegion P S w) := by
  intro z w h
  apply Finset.disjoint_left.mpr
  intro q hz hw
  exact h (Vertex.z.inj ((Finset.mem_filter.mp hz).2.symm.trans
    (Finset.mem_filter.mp hw).2))
theorem ownerRegionForFintype (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (F : Fintype (RZQ P S))
    (D : DecidablePred (fun q : RZQ P S => blockCorrectionOwner P S q = some (Vertex.z z))) :
    BDL26RZSupportedBoundary.correctionRegion P S z =
      @Finset.filter (RZQ P S) (fun q => blockCorrectionOwner P S q = some (Vertex.z z))
        D (@Finset.univ (RZQ P S) F) := by
  ext q
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
    (Finset.ext_iff.mp (blockCorrectionOwner_region P S z) q)
theorem actualCoherence (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (z : P.Z) :
    BDL26RZSupportedBoundary.correctionRegion P S z =
      (Finset.univ : Finset ((rzReplacementPresentation P A.toTannerSquareAdmissible S).Q)).filter
        (fun q => blockCorrectionOwner P S q = some (Vertex.z z)) :=
  ownerRegionForFintype P S z _ _
noncomputable def actualEndpoint (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) :
    EndpointData P (rzReplacementPresentation P A.toTannerSquareAdmissible S) where
  topCenter := fun p => .z p.1
  owner := blockCorrectionOwner P S
  region := blockRegion P S
  corrections := BDL26RZSupportedBoundary.correctionRegion P S
  lift := rootLift P A S
  map2 := map2Coord P A S
  projection := rzQParity P S
  cover := blockRegion_cover P S
  disjoint := fun _ _ h => blockRegion_disjoint P S h
  corrections_disjoint := corrections_disjoint P S
  coherence := actualCoherence P A S
  lift_supported := rootLift_outside P A S
  lift_parity := rootLift_region_parity P A S
  decomposition := fun sigma => (sum_rootLift P A S sigma).symm
  boundary_supported := fun z f hf =>
    BDL26RZSupportedBoundary.coboundary_supported P A S z ⟨f,hf⟩
  radius := block_radius P S
def transportEndpoint (P U V : TannerSquarePresentation)
    (h : U = V) (G : EndpointData P V) : EndpointData P U := h.symm ▸ G
theorem transportEndpoint_property (P U V : TannerSquarePresentation)
    (h : U = V) (G : EndpointData P V)
    (property : (T : TannerSquarePresentation) → EndpointData P T → Prop)
    (hg : property V G) : property U (transportEndpoint P U V h G) := by
  cases h
  exact hg
theorem transportEndpoint_fields (P U V : TannerSquarePresentation)
    (h : U = V) (G : EndpointData P V) :
    HEq (transportEndpoint P U V h G).region G.region ∧
    HEq (transportEndpoint P U V h G).corrections G.corrections ∧
    HEq (transportEndpoint P U V h G).owner G.owner ∧
    HEq (transportEndpoint P U V h G).projection G.projection ∧
    HEq (transportEndpoint P U V h G).map2 G.map2 := by
  cases h
  exact ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
noncomputable def endpointBoundary {P U : TannerSquarePresentation}
    (G : EndpointData P U) (z : P.Z) :
    supportedSubmodule (G.corrections z) →ₗ[BDL26Field] supportedSubmodule (G.region z) where
  toFun f := ⟨tannerCoboundary1 U f.1, G.boundary_supported z f.1 f.2⟩
  map_add' f g := by apply Subtype.ext; simp
  map_smul' c f := by apply Subtype.ext; simp
def EndpointF07 {P U : TannerSquarePresentation} (G : EndpointData P U) : Prop :=
  ∀ z, ∃ e : ((supportedSubmodule (G.region z)) ⧸ LinearMap.range (endpointBoundary G z))
    ≃ₗ[BDL26Field] BDL26Field,
    ∀ r, e ((LinearMap.range (endpointBoundary G z)).mkQ r) = ∑ p ∈ G.region z, r.1 p
theorem actualEndpoint_F07 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) :
    EndpointF07 (actualEndpoint P A S) := by
  intro z
  exact ⟨BDL26RZSupportedBoundary.quotientEquiv P A S z,
    BDL26RZSupportedBoundary.quotientEquiv_mkQ P A S z⟩
def EndpointF09 {P U : TannerSquarePresentation} (G : EndpointData P U) : Prop :=
  ∀ e, (fun z => ∑ p ∈ G.region z, tannerCoboundary1 U e p) =
    tannerCoboundary1 P (G.projection e)
theorem actualEndpoint_F09 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) :
    EndpointF09 (actualEndpoint P A S) := by
  intro e
  funext z
  exact (blockParity_eq_region_sum P S (rzCoboundary1 P A S e) z).symm.trans
    (rzCoboundary1_blockParity P A S e z)
def EndpointResidualZero {P U : TannerSquarePresentation}
    (G : EndpointData P U) : Prop :=
  ∀ sigma z, maskWord (G.region z) (G.map2 sigma) +
    G.lift z (∑ p ∈ G.region z, G.map2 sigma p) = 0
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
theorem stateSuccRZ (h : ¬i.val % 2 = 0) :
    state S (i.val + 1) = rzState S (state S i.val) := by
  change nextState S i.val (state S i.val) = _
  exact if_neg h
noncomputable def endpointAt (h : ¬i.val % 2 = 0) :
    EndpointData (state S i.val).presentation (state S (i.val + 1)).presentation :=
  transportEndpoint _ _ _ (congrArg ConstructionState.presentation (stateSuccRZ S depth i h))
    (actualEndpoint (state S i.val).presentation (state S i.val).admissible S)
theorem endpointAt_map2 (h : ¬i.val % 2 = 0) :
    (endpointAt S depth i h).map2 = (indexedEdgeMap S depth i).map2 := by
  have hfields := transportEndpoint_fields _ _ _
    (congrArg ConstructionState.presentation (stateSuccRZ S depth i h))
    (actualEndpoint (state S i.val).presentation (state S i.val).admissible S)
  have hm := (indexedDecoderData_selected_rz S depth i h).2.2
  rw [selectedMap_eq] at hm
  exact eq_of_heq (hfields.2.2.2.2.trans hm.symm)
noncomputable def rzData (h : ¬i.val % 2 = 0) :
    RZCoarseGrainingData (indexedDecoderData S depth) i
      (Vertex (state S i.val).presentation) := by
  let G := endpointAt S depth i h
  refine
    { levelGraph := tannerLevel (state S i.val).presentation
      center := Vertex.z
      topCenter := G.topCenter
      correctionOwner := G.owner
      coarseRegion := G.region
      correctionInputRegion := G.region
      correctionRegion := G.corrections
      lift := G.lift
      induced := ⟨G.projection⟩
      coarseRegion_cover := G.cover
      coarseRegion_disjoint := G.disjoint
      correctionInputRegion_subset := fun _ => Finset.Subset.refl _
      correctionRegion_disjoint := G.corrections_disjoint
      correctionRegion_coherence := G.coherence
      lift_supported := G.lift_supported
      lift_parity := G.lift_parity
      induced_syndrome_decomposition := ?_
      local_boundary_supported := ?_
      topRegion_radius_two := ?_
      correctionInput_radius_one := ?_ }
  · intro sigma
    change (indexedEdgeMap S depth i).map2 sigma = _
    rw [← endpointAt_map2 S depth i h]
    exact G.decomposition sigma
  · intro z f hf p hp
    change ((indexedFamily S depth).coboundary1 i.succ) f p = 0
    rw [indexedFamily_coboundary1]
    exact G.boundary_supported z f hf p hp
  · intro z p hp
    rw [G.radius z p hp]
    simp
  · intro z p hp
    rw [G.radius z p hp]
    simp
theorem rzData_localTopCohomology (h : ¬i.val % 2 = 0) :
    LocalTopCohomologyIdentification (rzData S depth i h) := by
  have hg : EndpointF07 (endpointAt S depth i h) :=
    transportEndpoint_property _ _ _
      (congrArg ConstructionState.presentation (stateSuccRZ S depth i h)) _
      (fun _ G => EndpointF07 G)
      (actualEndpoint_F07 (state S i.val).presentation (state S i.val).admissible S)
  have hb (z : (state S i.val).presentation.Z) :
      localBoundaryMap (rzData S depth i h) z = endpointBoundary (endpointAt S depth i h) z := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change ((indexedFamily S depth).coboundary1 i.succ) f.1 =
      tannerCoboundary1 (state S (i.val + 1)).presentation f.1
    rw [indexedFamily_coboundary1]
    rfl
  intro z
  change ∃ e : ((supportedSubmodule ((endpointAt S depth i h).region z)) ⧸
      LinearMap.range (localBoundaryMap (rzData S depth i h) z)) ≃ₗ[BDL26Field] BDL26Field,
    ∀ r, e ((LinearMap.range (localBoundaryMap (rzData S depth i h) z)).mkQ r) =
      ∑ p ∈ (endpointAt S depth i h).region z, r.1 p
  rw [hb z]
  exact hg z
theorem rzData_inducedCoboundaryCompatibility (h : ¬i.val % 2 = 0) :
    InducedCoboundaryCompatibility (rzData S depth i h) := by
  have hg : EndpointF09 (endpointAt S depth i h) :=
    transportEndpoint_property _ _ _
      (congrArg ConstructionState.presentation (stateSuccRZ S depth i h)) _
      (fun _ G => EndpointF09 G)
      (actualEndpoint_F09 (state S i.val).presentation (state S i.val).admissible S)
  intro e
  change (fun z => ∑ p ∈ (endpointAt S depth i h).region z,
    ((indexedFamily S depth).coboundary1 i.succ) e p) =
    ((indexedFamily S depth).coboundary1 i.castSucc) ((endpointAt S depth i h).projection e)
  rw [indexedFamily_coboundary1, indexedFamily_coboundary1]
  exact hg e
theorem upper_even (h : ¬i.val % 2 = 0) : i.succ.val % 2 = 0 := by
  have hm := Nat.mod_lt i.val (by decide : 0 < 2)
  change (i.val + 1) % 2 = 0
  omega
noncomputable def rzStepOutput (h : ¬i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ) :
    AssemblyStepOutput (indexedDecoderData S depth) i :=
  AuditedLeafAdapters.rzOutput (rzData S depth i h)
    (rzData_localTopCohomology S depth i h)
    (rzData_inducedCoboundaryCompatibility S depth i h)
    (upper_even depth i h) sigma
theorem rzStepOutput_localComponents (h : ¬i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ) :
    (rzStepOutput S depth i h sigma).localComponents =
      (Finset.univ : Finset ((state S i.val).presentation.Z)).toList.map
        (fun z => localCorrectionComponent (rzData S depth i h)
          (rzData_localTopCohomology S depth i h) z sigma.val) := rfl
noncomputable def componentOwner (h : ¬i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (j : Fin (rzStepOutput S depth i h sigma).localComponents.length) :
    (state S i.val).presentation.Z :=
  (Finset.univ : Finset ((state S i.val).presentation.Z)).toList.get
    ⟨j.val, by
      simpa (config := { instances := true }) only [rzStepOutput_localComponents,
        List.length_map] using j.isLt⟩
noncomputable def rzStepOutput_ownerLabels (h : ¬i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ) :
    AssemblyOwnerLabels (V := Vertex (state S i.val).presentation)
      (indexedDecoderData S depth) i (rzStepOutput S depth i h sigma) :=
  AssemblyOwnerLabels.ofOwners _
    (fun j => some (.z (componentOwner S depth i h sigma j)))
noncomputable def embeddedSyndrome
    (sigma : (indexedFamily S depth).Syndrome i.castSucc) :
    (indexedFamily S depth).Syndrome i.succ :=
  ((indexedDecoderData S depth).selectedMap i).mapSyndrome sigma
end QEC.Coding.BDL26RZDecoderAdapter
noncomputable section
namespace QEC.Coding.BDL26RZDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementSupport BDL26RZConcreteParity BDL26LevelTwoDistance
open MultiscaleDecoder RZCoarseGraining RZCoarseGrainingData
open BDL26AlternatingCochain BDL26ReplacementCochainMaps
open scoped Classical BigOperators
def presentationAt (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) : LevelIndex 1 → TannerSquarePresentation :=
  Fin.cases P (fun _ => rzReplacementPresentation P A.toTannerSquareAdmissible S)
abbrev PresentationX (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) (i : LevelIndex 1) := (presentationAt P A S i).X
abbrev PresentationQ (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) (i : LevelIndex 1) := (presentationAt P A S i).Q
abbrev PresentationZ (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) (i : LevelIndex 1) := (presentationAt P A S i).Z
def presentationFamily (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) : BDL26CochainFamily 1
      (PresentationX P A S) (PresentationQ P A S) (PresentationZ P A S) where
  complex := fun i => BDL26LevelTwoDecoder.presentationComplex (presentationAt P A S i)
theorem presentationFamily_coboundary0 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (i : LevelIndex 1) :
    (presentationFamily P A S).coboundary0 i = tannerCoboundary0 (presentationAt P A S i) := by
  apply LinearMap.ext
  intro e
  funext q
  exact wordLinearMapTranspose_toLin'_apply _ e q
theorem presentationFamily_coboundary1 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (i : LevelIndex 1) :
    (presentationFamily P A S).coboundary1 i = tannerCoboundary1 (presentationAt P A S i) := by
  apply LinearMap.ext
  intro e
  funext z
  exact wordLinearMapTranspose_toLin'_apply _ e z
def presentationMap (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) : BDL26CochainMap (presentationFamily P A S) (0 : StepIndex 1) where
  map0 := rzMap0Coord P S
  map1 := map1Coord P A S
  map2 := map2Coord P A S
  commutes_coboundary0 := by
    rw [presentationFamily_coboundary0,presentationFamily_coboundary0]
    exact rzMap_commutes_coboundary0 P A S
  commutes_coboundary1 := by
    rw [presentationFamily_coboundary1,presentationFamily_coboundary1]
    exact rzMap_commutes_coboundary1 P A S
def presentationDecoderData (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) : BDL26DecoderData 1
      (PresentationX P A S) (PresentationQ P A S) (PresentationZ P A S) where
  family := presentationFamily P A S
  rxMap := fun i => Fin.cases (presentationMap P A S) (fun j => Fin.elim0 j) i
  rzMap := fun i => Fin.cases (presentationMap P A S) (fun j => Fin.elim0 j) i
@[simp] theorem presentationDecoderData_selectedMap (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) :
    (presentationDecoderData P A S).selectedMap (0 : StepIndex 1) =
      presentationMap P A S := rfl
def presentationData (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) : RZCoarseGrainingData (presentationDecoderData P A S)
      (0 : StepIndex 1) (Vertex P) := by
  let G := actualEndpoint P A S
  refine
    { levelGraph := tannerLevel P
      center := Vertex.z
      topCenter := G.topCenter
      correctionOwner := G.owner
      coarseRegion := G.region
      correctionInputRegion := G.region
      correctionRegion := G.corrections
      lift := G.lift
      induced := ⟨G.projection⟩
      coarseRegion_cover := G.cover
      coarseRegion_disjoint := G.disjoint
      correctionInputRegion_subset := fun _ => Finset.Subset.refl _
      correctionRegion_disjoint := G.corrections_disjoint
      correctionRegion_coherence := G.coherence
      lift_supported := G.lift_supported
      lift_parity := G.lift_parity
      induced_syndrome_decomposition := ?_
      local_boundary_supported := ?_
      topRegion_radius_two := ?_
      correctionInput_radius_one := ?_ }
  · intro sigma
    exact G.decomposition sigma
  · intro z f hf p hp
    change ((presentationFamily P A S).coboundary1 (1 : LevelIndex 1)) f p = 0
    rw [presentationFamily_coboundary1]
    exact G.boundary_supported z f hf p hp
  · intro z p hp
    exact (G.radius z p hp).le.trans (by decide)
  · intro z p hp
    exact (G.radius z p hp).le.trans (by decide)
theorem presentationData_localTopCohomology (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) :
    LocalTopCohomologyIdentification (presentationData P A S) := by
  have hb (z : P.Z) :
      localBoundaryMap (presentationData P A S) z = endpointBoundary (actualEndpoint P A S) z := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change ((presentationFamily P A S).coboundary1 (1 : LevelIndex 1)) f.1 =
      tannerCoboundary1 (rzReplacementPresentation P A.toTannerSquareAdmissible S) f.1
    rw [presentationFamily_coboundary1]
    rfl
  intro z
  change ∃ e : ((supportedSubmodule ((actualEndpoint P A S).region z)) ⧸
      LinearMap.range (localBoundaryMap (presentationData P A S) z)) ≃ₗ[BDL26Field] BDL26Field,
    ∀ r, e ((LinearMap.range (localBoundaryMap (presentationData P A S) z)).mkQ r) =
      ∑ p ∈ (actualEndpoint P A S).region z, r.1 p
  rw [hb z]
  exact actualEndpoint_F07 P A S z
theorem presentationData_inducedCoboundaryCompatibility (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) :
    InducedCoboundaryCompatibility (presentationData P A S) := by
  intro e
  change (fun z => ∑ p ∈ (actualEndpoint P A S).region z,
    ((presentationFamily P A S).coboundary1 (1 : LevelIndex 1)) e p) =
    ((presentationFamily P A S).coboundary1 (0 : LevelIndex 1))
      ((actualEndpoint P A S).projection e)
  rw [presentationFamily_coboundary1,presentationFamily_coboundary1]
  exact actualEndpoint_F09 P A S e
def presentationOutput (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale)
    (sigma : (presentationFamily P A S).Syndrome (1 : LevelIndex 1)) :
    AssemblyStepOutput (presentationDecoderData P A S) (0 : StepIndex 1) := by
  let G := presentationData P A S
  let hc := presentationData_localTopCohomology P A S
  let hi := presentationData_inducedCoboundaryCompatibility P A S
  let coarse := coarseSyndrome G hi sigma
  let correction := correctionFromSyndrome G hc sigma.val
  let pieces := (Finset.univ : Finset P.Z).toList.map
    (fun z => localCorrectionComponent G hc z sigma.val)
  apply AssemblyStepOutput.ofComponents sigma coarse correction pieces
  · exact rz_exact_relation_selected G hc hi rfl sigma
  · exact ((localComputabilityCertificate G hc hi).totalCorrectionDecomposition sigma.val).trans
      (Finset.sum_map_toList (Finset.univ : Finset P.Z)
        (fun z : P.Z => localCorrectionComponent G hc z sigma.val)).symm
end QEC.Coding.BDL26RZDecoderAdapter
end
namespace QEC.Coding.BDL26RZDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity MultiscaleDecoder
open RZCoarseGraining RZCoarseGrainingData
end QEC.Coding.BDL26RZDecoderAdapter


