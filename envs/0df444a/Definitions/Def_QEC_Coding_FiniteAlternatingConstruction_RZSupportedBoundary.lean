-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZSupportedBoundary
-- name    : QEC_Coding_FiniteAlternatingConstruction_RZSupportedBoundary
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T05:06:38.749062+00:00
-- url     : https://prove2.me/theorems/f08806c6-c954-4e7d-b060-2b84802748e1
-- title:
--   RZSupported Boundary
-- statement:
--   Definitions and structural lemmas for RZSupported Boundary, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZSupportedBoundary.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZConcreteParity
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_correctionRegion_mem
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_syndromeRegion_mem
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalWordPush_single
import Theorems.Thm_QEC_Coding_BDL26RZConcreteParity_blockParity_map2
import Theorems.Thm_QEC_Coding_BDL26RZConcreteParity_rootLift_support
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzFace_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzQ_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzX_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzZ_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_rzCzTopCoboundary_range_eq_totalParity_ker
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_map2Coord_canonicalBasis
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_rzCoboundary1_extendZEdgeWord
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
namespace QEC.Coding.BDL26RZSupportedBoundary
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26RZConcreteParity
open MultiscaleDecoder
open MultiscaleDecoder.RZCoarseGraining.RZCoarseGrainingData
open scoped Classical BigOperators
noncomputable def correctionRegion (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) : Finset (RZQ P S) :=
  fiberRegion (rzCorrectionOwner P S) (.z z)
noncomputable abbrev correctionSpace (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) := supportedSubmodule (correctionRegion P S z)
noncomputable abbrev topSpace (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) := supportedSubmodule (blockRegion P S z)
theorem extendEdge_supported (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (e : Word BDL26Field (ZDoubleCylinderEdge P z S)) :
    extendZEdgeWord P S z e ∈ correctionSpace P S z := by
  intro p hp
  rcases p with ⟨w,edge⟩ | ⟨q,v⟩
  · by_cases h : w = z
    · subst w
      apply False.elim
      apply hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    · simp [extendZEdgeWord, h]
  · rfl
theorem extendVertex_supported (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (r : Word BDL26Field (ZDoubleCylinderVertex P z S)) :
    extendZVertexWord P S z r ∈ topSpace P S z := by
  intro p hp
  rcases p with ⟨w,v⟩
  by_cases h : w = z
  · subst w
    exact False.elim (hp (by simp [blockRegion, fiberRegion]))
  · simp [extendZVertexWord, h]
noncomputable def correctionEquiv (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) : correctionSpace P S z ≃ₗ[BDL26Field]
      Word BDL26Field (ZDoubleCylinderEdge P z S) where
  toFun e edge := e.1 (Sum.inl ⟨z,edge⟩)
  invFun e := ⟨extendZEdgeWord P S z e, extendEdge_supported P S z e⟩
  left_inv e := by
    apply Subtype.ext
    funext p
    rcases p with ⟨w,edge⟩ | ⟨q,v⟩
    · change (if h : w = z then e.1 (Sum.inl ⟨z,h ▸ edge⟩) else 0) =
        e.1 (Sum.inl ⟨w,edge⟩)
      by_cases h : w = z
      · subst w
        simp
      · rw [dif_neg h]
        symm
        apply e.2
        intro hm
        have ho := (Finset.mem_filter.mp hm).2
        change Vertex.z w = Vertex.z z at ho
        exact h (Vertex.z.inj ho)
    · change 0 = e.1 (Sum.inr ⟨q,v⟩)
      symm
      apply e.2
      intro hm
      have ho := (Finset.mem_filter.mp hm).2
      change Vertex.q q = Vertex.z z at ho
      cases ho
  right_inv e := by funext edge; simp [extendZEdgeWord]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
noncomputable def topEquiv (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) : topSpace P S z ≃ₗ[BDL26Field]
      Word BDL26Field (ZDoubleCylinderVertex P z S) where
  toFun r v := r.1 ⟨z,v⟩
  invFun r := ⟨extendZVertexWord P S z r, extendVertex_supported P S z r⟩
  left_inv r := by
    apply Subtype.ext
    funext p
    rcases p with ⟨w,v⟩
    by_cases h : w = z
    · subst w
      simp [extendZVertexWord]
    · change (if h : w = z then r.1 ⟨z,h ▸ v⟩ else 0) = r.1 ⟨w,v⟩
      rw [dif_neg h]
      symm
      exact r.2 _ (by simp [blockRegion, fiberRegion, h])
  right_inv r := by funext v; simp [extendZVertexWord]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem correction_extend_restrict (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (e : correctionSpace P S z) :
    extendZEdgeWord P S z (correctionEquiv P S z e) = e.1 :=
  congrArg Subtype.val ((correctionEquiv P S z).symm_apply_apply e)
theorem coboundary_supported (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (z : P.Z)
    (e : correctionSpace P S z) :
    tannerCoboundary1 (rzReplacementPresentation P A.toTannerSquareAdmissible S)
      e.1 ∈ topSpace P S z := by
  rw [← correction_extend_restrict P S z e, rzCoboundary1_extendZEdgeWord]
  exact extendVertex_supported P S z _
noncomputable def boundary (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (z : P.Z) :
    correctionSpace P S z →ₗ[BDL26Field] topSpace P S z where
  toFun e := ⟨tannerCoboundary1
    (rzReplacementPresentation P A.toTannerSquareAdmissible S) e.1,
    coboundary_supported P A S z e⟩
  map_add' _ _ := by apply Subtype.ext; exact map_add _ _ _
  map_smul' _ _ := by apply Subtype.ext; exact map_smul _ _ _
theorem boundary_coordinates (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (z : P.Z)
    (e : correctionSpace P S z) :
    topEquiv P S z (boundary P A S z e) =
      rzCzGraphBoundary P z S (correctionEquiv P S z e) := by
  change (fun v => tannerCoboundary1
    (rzReplacementPresentation P A.toTannerSquareAdmissible S) e.1 ⟨z,v⟩) = _
  rw [← correction_extend_restrict P S z e, rzCoboundary1_extendZEdgeWord]
  funext v
  simp [extendZVertexWord]
noncomputable def parity (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) : topSpace P S z →ₗ[BDL26Field] BDL26Field :=
  totalParity.comp (topEquiv P S z).toLinearMap
theorem boundary_range_eq_parity_ker (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (z : P.Z) :
    LinearMap.range (boundary P A S z) = LinearMap.ker (parity P S z) := by
  have hlocal : LinearMap.range (rzCzGraphBoundary P z S) =
      LinearMap.ker totalParity := by
    simpa only [rzCzTopCoboundary_eq_graphBoundary] using
      rzCzTopCoboundary_range_eq_totalParity_ker P A.toTannerSquareAdmissible z S
  ext r
  constructor
  · rintro ⟨e, rfl⟩
    change totalParity (topEquiv P S z (boundary P A S z e)) = 0
    rw [boundary_coordinates]
    exact LinearMap.mem_ker.mp (hlocal ▸
      (LinearMap.mem_range.mpr ⟨correctionEquiv P S z e, rfl⟩))
  · intro hr
    have hr' : topEquiv P S z r ∈ LinearMap.range (rzCzGraphBoundary P z S) := by
      rw [hlocal]
      exact hr
    obtain ⟨e, he⟩ := hr'
    refine ⟨(correctionEquiv P S z).symm e, ?_⟩
    apply (topEquiv P S z).injective
    rw [boundary_coordinates, LinearEquiv.apply_symm_apply]
    exact he
noncomputable def supportedRootLift (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (z : P.Z)
    (b : BDL26Field) : topSpace P S z :=
  ⟨rootLift P A S z b, by
    intro p hp
    by_contra hn
    exact hp (rootLift_support P A S z b (by simpa [hammingSupport] using hn))⟩
theorem parity_rootLift (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (z : P.Z)
    (b : BDL26Field) : parity P S z (supportedRootLift P A S z b) = b := by
  change blockParity P S (map2Coord P A S (Pi.single z b)) z = b
  rw [blockParity_map2]
  simp
theorem parity_surjective (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (z : P.Z) :
    Function.Surjective (parity P S z) :=
  fun b => ⟨supportedRootLift P A S z b, parity_rootLift P A S z b⟩
abbrev topQuotient (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (z : P.Z) :=
  topSpace P S z ⧸ LinearMap.range (boundary P A S z)
noncomputable def quotientEquiv (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (z : P.Z) :
    topQuotient P A S z ≃ₗ[BDL26Field] BDL26Field :=
  (Submodule.quotEquivOfEq _ _ (boundary_range_eq_parity_ker P A S z)).trans
    ((parity P S z).quotKerEquivOfSurjective (parity_surjective P A S z))
end QEC.Coding.BDL26RZSupportedBoundary


