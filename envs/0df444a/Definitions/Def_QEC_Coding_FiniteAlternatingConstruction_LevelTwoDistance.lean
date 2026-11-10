-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
-- name    : QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T01:25:00.695702+00:00
-- url     : https://prove2.me/theorems/65f3850b-f9ec-49d3-b4ed-3e4e458d9dd7
-- title:
--   Level Two Distance
-- statement:
--   Definitions and structural lemmas for Level Two Distance, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean

import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXSeedSmallSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AlternatingCochain
import Theorems.Thm_P2M_QEC_Coding_wordLinearMapTranspose_toLin__apply_6aba8976cbc7
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_correctionRegion_mem
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_syndromeRegion_mem
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCxCocycle_eq_boundaryRoot_zeroCopy
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_coboundary0_eq
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_coboundary1_eq
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalWordPush_single
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzFace_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzQ_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzX_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzZ_card
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_map2Coord_canonicalBasis
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_rzMap1QEdge_delta0_canonicalBasis
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary0_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary1_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rxMap_commutes_coboundary1
import Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzMap_commutes_coboundary1
import Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzOldX_delta0
import Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_sum_qVertexXIncidence
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
import Theorems.Thm_QEC_Coding_LinearCode_dual_dual_carrier_eq
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
import Theorems.Thm_QEC_Coding_exists_relativeMinimumDistance_of_exists_mem_not_mem
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
namespace QEC.Coding.BDL26LevelTwoDistance
open scoped BigOperators
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps BDL26LevelTwoCode
abbrev Field := BDL26FiniteTannerSquare.Field
noncomputable local instance rzQDecidableEq (P : TannerSquarePresentation) (S : OddScale) :
    DecidableEq (RZQ P S) := Classical.decEq _
theorem linearMap_ext_canonicalBasis
    {Source Target : Type} [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (first second : Word Field Source →ₗ[Field] Word Field Target)
    (hbasis : ∀ source,
      first (canonicalBasisWord source) = second (canonicalBasisWord source)) :
    first = second := by
  classical
  apply LinearMap.ext
  intro word
  have hdecompose : word =
      ∑ source : Source, word source • canonicalBasisWord source := by
    rw [← word_eq_sum_single word]
    apply Finset.sum_congr rfl
    intro source _
    ext target
    rw [Pi.single_apply, Pi.smul_apply]
    by_cases htarget : target = source
    · subst target
      simp [canonicalBasisWord]
    · simp [canonicalBasisWord, htarget]
  rw [hdecompose]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro source _
  rw [hbasis source]
def seedCocycle : Word Field BaseQubit := ![1, 0, 1, 0, 0]
def seedCycle : Word Field BaseQubit := ![1, 1, 0, 0, 0]
theorem seedCocycle_coboundary :
    tannerCoboundary1 baseTannerSquarePresentation seedCocycle = 0 := by
  decide
theorem seedCocycle_not_coboundary :
    ∀ potential : Word Field BaseX,
      tannerCoboundary0 baseTannerSquarePresentation potential ≠ seedCocycle := by
  intro potential heq
  have hc : tannerCoboundary0 baseTannerSquarePresentation potential (0 : BaseQubit) =
      tannerCoboundary0 baseTannerSquarePresentation potential (1 : BaseQubit) := by rfl
  rw [heq] at hc
  norm_num [seedCocycle] at hc
noncomputable def rzQParity (P : TannerSquarePresentation) (S : OddScale) :
    Word Field (RZQ P S) →ₗ[Field] Word Field P.Q where
  toFun := fun word q => ∑ vertex : QDoubleCylinderVertex (transposePresentation P) q S,
    word (Sum.inr ⟨q, vertex⟩)
  map_add' := by intros; ext q; simp [Finset.sum_add_distrib]
  map_smul' := by intros; ext q; simp [Finset.mul_sum]
@[simp] theorem rzQParity_extendZEdgeWord (P : TannerSquarePresentation)
    (S : OddScale) (z : P.Z) (word : Word Field (ZDoubleCylinderEdge P z S)) :
    rzQParity P S (extendZEdgeWord P S z word) = 0 := by
  ext q
  simp [rzQParity, extendZEdgeWord]
@[simp] theorem rzQParity_single (P : TannerSquarePresentation) (S : OddScale)
    (q : P.Q) (vertex : QDoubleCylinderVertex (transposePresentation P) q S)
    (value : Field) :
    rzQParity P S (Pi.single (Sum.inr ⟨q, vertex⟩) value) = Pi.single q value := by
  classical
  ext other
  by_cases h : other = q
  · subst other
    simp [rzQParity, Pi.single_apply]
  · have hcoord : ∀ v : QDoubleCylinderVertex (transposePresentation P) other S,
        (Sum.inr ⟨other, v⟩ : RZQ P S) ≠ Sum.inr ⟨q, vertex⟩ := by
      intro v heq
      exact h (congrArg Sigma.fst (Sum.inr.inj heq))
    simp [rzQParity, Pi.single_apply, h, hcoord]
theorem rzQParity_map1BasisImage (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) (q : P.Q) :
    rzQParity P S (map1BasisImage P A4 S q) = Pi.single q 1 := by
  classical
  unfold map1BasisImage
  rw [map_add, map_sum]
  have hz : (∑ z : P.Z, rzQParity P S
      (if hqz : P.qz q z = true then
        extendZEdgeWord P S z (rzMap1Connector P A4 q z hqz S) else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro z _
    split <;> simp
  rw [hz, add_zero]
  exact rzQParity_single P S q (rzMap1QRoot P q S) 1
theorem rzQParity_map1Coord (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale)
    (word : Word Field P.Q) :
    rzQParity P S (map1Coord P A4 S word) = word := by
  classical
  have hmaps : (rzQParity P S).comp (map1Coord P A4 S) = LinearMap.id := by
    apply linearMap_ext_canonicalBasis
    intro q
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    erw [map1Coord_canonicalBasis]
    refine (rzQParity_map1BasisImage P A4 S q).trans ?_
    funext other
    by_cases h : other = q <;> simp [canonicalBasisWord, Pi.single_apply, h]
  exact LinearMap.congr_fun hmaps word
@[simp] theorem rzQParity_localBasis (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (edge : ZDoubleCylinderEdge P z S) :
    rzQParity P S (canonicalBasisWord (Sum.inl ⟨z, edge⟩ : RZQ P S)) = 0 := by
  classical
  ext q
  simp [rzQParity, canonicalBasisWord]
@[simp] theorem rzQParity_qBasis (P : TannerSquarePresentation) (S : OddScale)
    (q : P.Q) (vertex : QDoubleCylinderVertex (transposePresentation P) q S) :
    rzQParity P S (canonicalBasisWord (Sum.inr ⟨q, vertex⟩ : RZQ P S)) =
      canonicalBasisWord q := by
  classical
  funext other
  by_cases h : other = q
  · subst other
    simp [rzQParity, canonicalBasisWord, Pi.single_apply, Sigma.mk.injEq]
  · have hcoord : ∀ v : QDoubleCylinderVertex (transposePresentation P) other S,
        (Sum.inr ⟨other, v⟩ : RZQ P S) ≠ Sum.inr ⟨q, vertex⟩ := by
      intro v heq
      exact h (congrArg Sigma.fst (Sum.inr.inj heq))
    simp [rzQParity, canonicalBasisWord, Pi.single_apply, h, hcoord]
def rzOldXParity (P : TannerSquarePresentation) (S : OddScale) :
    Word Field (RZX P S) →ₗ[Field] Word Field P.X where
  toFun := fun potential x => potential (Sum.inr (x, 0)) + potential (Sum.inr (x, 1))
  map_add' := by
    intro first second
    funext x
    exact add_add_add_comm _ _ _ _
  map_smul' := by
    intro coefficient potential
    funext x
    change coefficient * potential (Sum.inr (x, 0)) + coefficient * potential (Sum.inr (x, 1)) =
      coefficient * (potential (Sum.inr (x, 0)) + potential (Sum.inr (x, 1)))
    exact (mul_add _ _ _).symm
theorem rzQParity_localFace_coboundary (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale)
    (z : P.Z) (face : ZDoubleCylinderFace P z S) :
    rzQParity P S (rzCoboundary0 P A4 S
      (canonicalBasisWord (Sum.inl (Sum.inl ⟨z, face⟩) : RZX P S))) = 0 := by
  classical
  ext q
  change (∑ vertex : QDoubleCylinderVertex (transposePresentation P) q S,
    tannerCoboundary0 (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
      (canonicalBasisWord (Sum.inl (Sum.inl ⟨z, face⟩) : RZX P S))
      (Sum.inr ⟨q, vertex⟩)) = 0
  apply Finset.sum_eq_zero
  intro vertex _
  erw [tannerCoboundary0_canonicalBasis_apply]
  rfl
theorem rzQParity_qEdge_coboundary (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale)
    (q : P.Q) (edge : QDoubleCylinderEdge (transposePresentation P) q S) :
    rzQParity P S (rzCoboundary0 P A4 S
      (canonicalBasisWord (rzMap1QEdgeX P S q edge))) = 0 := by
  classical
  unfold rzCoboundary0
  erw [rzMap1QEdge_delta0_canonicalBasis]
  unfold rzMap1QEdgeDelta0BasisImage
  rw [map_add, map_add, map_sum, rzQParity_qBasis, rzQParity_qBasis]
  have hz : (∑ z : P.Z, rzQParity P S
      (if hqz : P.qz q z = true then
        canonicalBasisWord (Sum.inl ⟨z, qToZDoubleCylinderEdge P
          A4.toTannerSquareAdmissible q z hqz S edge⟩ : RZQ P S)
      else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro z _
    split <;> simp
  rw [hz, add_zero]
  exact ZModModule.add_self _
theorem rzQParity_oldX_coboundary (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) (x : P.X)
    (copy : BDL26FiniteTannerSquare.Two) :
    rzQParity P S (rzCoboundary0 P A4 S
      (canonicalBasisWord (Sum.inr (x, copy) : RZX P S))) =
      tannerCoboundary0 P (canonicalBasisWord x) := by
  classical
  rw [rzOldX_delta0, map_sum]
  ext target
  rw [Finset.sum_apply, Finset.sum_eq_single target]
  · rw [tannerCoboundary0_canonicalBasis_apply]
    by_cases hx : P.xq x target = true
    · rw [dif_pos hx, rzQParity_qBasis]
      simp [tannerCoboundary0_canonicalBasis_apply, hx, canonicalBasisWord]
    · simp [hx, tannerCoboundary0_canonicalBasis_apply]
  · intro q _ hq
    by_cases hx : P.xq x q = true
    · rw [dif_pos hx, rzQParity_qBasis]
      simp [canonicalBasisWord, hq, Ne.symm hq]
    · simp [hx]
  · simp
theorem rzQParity_coboundary (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale)
    (potential : Word Field (RZX P S)) :
    rzQParity P S (rzCoboundary0 P A4 S potential) =
      tannerCoboundary0 P (rzOldXParity P S potential) := by
  classical
  have hm : (rzQParity P S).comp (rzCoboundary0 P A4 S) =
      (tannerCoboundary0 P).comp (rzOldXParity P S) := by
    apply linearMap_ext_canonicalBasis
    intro coordinate
    simp only [LinearMap.comp_apply]
    rcases coordinate with (⟨z, face⟩ | ⟨q, edge⟩) | ⟨x, copy⟩
    · rw [rzQParity_localFace_coboundary]
      have hzero : rzOldXParity P S
          (canonicalBasisWord (Sum.inl (Sum.inl ⟨z, face⟩) : RZX P S)) = 0 := by
        ext x
        simp [rzOldXParity, canonicalBasisWord]
      rw [hzero, map_zero]
    · change rzQParity P S (rzCoboundary0 P A4 S
          (canonicalBasisWord (rzMap1QEdgeX P S q edge))) = _
      rw [rzQParity_qEdge_coboundary]
      have hzero : rzOldXParity P S
          (canonicalBasisWord (rzMap1QEdgeX P S q edge)) = 0 := by
        ext x
        simp [rzOldXParity, rzMap1QEdgeX, canonicalBasisWord]
      erw [hzero, map_zero]
    · rw [rzQParity_oldX_coboundary]
      have hcopy : rzOldXParity P S
          (canonicalBasisWord (Sum.inr (x, copy) : RZX P S)) = canonicalBasisWord x := by
        ext other
        fin_cases copy <;> simp [rzOldXParity, canonicalBasisWord, Pi.single_apply]
      rw [hcopy]
  exact LinearMap.congr_fun hm potential
theorem rzMap1_preserves_nonboundary (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) (word : Word Field P.Q)
    (hword : ∀ potential, tannerCoboundary0 P potential ≠ word) :
    ∀ potential, rzCoboundary0 P A4 S potential ≠ map1Coord P A4 S word := by
  intro potential heq
  have hparity := congrArg (rzQParity P S) heq
  rw [rzQParity_coboundary, rzQParity_map1Coord] at hparity
  exact hword (rzOldXParity P S potential) hparity
theorem rxCoboundary0_localEdge (P : TannerSquarePresentation) (S : OddScale)
    (potential : Word Field (RX0 P S)) (x : P.X)
    (edge : DoubleCylinderEdge P x S) :
    rxCoboundary0 P S potential (Sum.inl ⟨x, edge⟩) =
      wordLinearMapTranspose (rxCx P x S).boundary1
        (fun vertex => potential ⟨x, vertex⟩) edge := by
  classical
  unfold rxCoboundary0 rxBoundary1
  rw [wordLinearMapTranspose_toLin'_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single x]
  · simp only [rxBoundary1Matrix, dite_true]
    change (∑ vertex : DoubleCylinderVertex P x S,
        potential ⟨x, vertex⟩ * doubleCylinderEdgeVertexMatrix P x S vertex edge) =
      wordLinearMapTranspose (Matrix.toLin' (doubleCylinderEdgeVertexMatrix P x S))
        (fun vertex => potential ⟨x, vertex⟩) edge
    exact (wordLinearMapTranspose_toLin'_apply _ _ _).symm
  · intro other _ hother
    simp [rxBoundary1Matrix, hother]
  · simp
theorem rxPotential_constant_of_boundary_eq_map1 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale)
    (potential : Word Field (RX0 P S)) (word : Word Field P.Q)
    (h : rxCoboundary0 P S potential = rxMap1Coord P S word)
    (x : P.X) (vertex : DoubleCylinderVertex P x S) :
    potential ⟨x, vertex⟩ = potential ⟨x,
      (0, (subdivisionOriginalBoundaryVertex P x S (A.xBoundaryRoot x)).1)⟩ := by
  refine rxCxCocycle_eq_boundaryRoot_zeroCopy P A x S
    (fun vertex => potential ⟨x, vertex⟩) ?_ vertex
  ext edge
  have he := congrFun h (Sum.inl ⟨x, edge⟩)
  rw [rxCoboundary0_localEdge, rxMap1Coord_localEdge] at he
  exact he
theorem rxBoundary_eq_map1_recovers_potential (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale)
    (potential : Word Field (RX0 P S)) (word : Word Field P.Q)
    (h : rxCoboundary0 P S potential = rxMap1Coord P S word) :
    tannerCoboundary0 P (fun x => potential ⟨x,
      (0, (subdivisionOriginalBoundaryVertex P x S (A.xBoundaryRoot x)).1)⟩) = word := by
  classical
  ext q
  let root : QDoubleCylinderVertex P q S := (0, Sum.inl (Sum.inl ()))
  have he := congrFun h (Sum.inr ⟨q, root⟩)
  rw [rxMap1Coord_qVertex] at he
  unfold rxCoboundary0 rxBoundary1 at he
  rw [wordLinearMapTranspose_toLin'_apply, Fintype.sum_sigma] at he
  calc
    _ = ∑ x : P.X, ∑ vertex : DoubleCylinderVertex P x S,
        potential ⟨x, vertex⟩ * qDoubleCylinderVertexXIncidence P q x S vertex root := by
      apply Finset.sum_congr rfl
      intro x _
      simp_rw [rxPotential_constant_of_boundary_eq_map1 P A S potential word h]
      rw [← Finset.mul_sum, sum_qVertexXIncidence P A S x q root]
    _ = word q := he
theorem rxMap1_preserves_nonboundary (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (word : Word Field P.Q)
    (hword : ∀ potential, tannerCoboundary0 P potential ≠ word) :
    ∀ potential, rxCoboundary0 P S potential ≠ rxMap1Coord P S word := by
  intro potential heq
  exact hword _ (rxBoundary_eq_map1_recovers_potential P A S potential word heq)
open BDL26DecodingGraph
noncomputable def levelTwoXLogical (S : OddScale) :
    Word Field (levelTwoPresentation S).Q :=
  map1Coord (levelOnePresentation S) (rxState S baseState).admissible S
    (rxMap1Coord baseTannerSquarePresentation S seedCocycle)
theorem levelTwoXLogical_cocycle (S : OddScale) :
    tannerCoboundary1 (levelTwoPresentation S) (levelTwoXLogical S) = 0 := by
  have hrx := LinearMap.congr_fun
    (rxMap_commutes_coboundary1 baseTannerSquarePresentation S) seedCocycle
  change rxCoboundary1 baseTannerSquarePresentation S
      (rxMap1Coord baseTannerSquarePresentation S seedCocycle) =
    rxMap2Coord baseTannerSquarePresentation S
      (tannerCoboundary1 baseTannerSquarePresentation seedCocycle) at hrx
  rw [seedCocycle_coboundary, map_zero] at hrx
  have hrx' : tannerCoboundary1 (levelOnePresentation S)
      (rxMap1Coord baseTannerSquarePresentation S seedCocycle) = 0 := by
    change tannerCoboundary1 (rxReplacementPresentation baseTannerSquarePresentation S)
      (rxMap1Coord baseTannerSquarePresentation S seedCocycle) = 0
    erw [rxPresentation_coboundary1_eq _ baseTannerSquareAdmissibleV4
      baseTannerSquareCellularRegular S]
    exact hrx
  have hrz := LinearMap.congr_fun
    (rzMap_commutes_coboundary1 (levelOnePresentation S)
      (rxState S baseState).admissible S)
    (rxMap1Coord baseTannerSquarePresentation S seedCocycle)
  change rzCoboundary1 (levelOnePresentation S) (rxState S baseState).admissible S
      (map1Coord (levelOnePresentation S) (rxState S baseState).admissible S
        (rxMap1Coord baseTannerSquarePresentation S seedCocycle)) =
    map2Coord (levelOnePresentation S) (rxState S baseState).admissible S
      (tannerCoboundary1 (levelOnePresentation S)
        (rxMap1Coord baseTannerSquarePresentation S seedCocycle)) at hrz
  rw [hrx', map_zero] at hrz
  exact hrz
theorem levelTwoXLogical_nonboundary (S : OddScale) :
    ∀ potential, tannerCoboundary0 (levelTwoPresentation S) potential ≠
      levelTwoXLogical S := by
  apply rzMap1_preserves_nonboundary (levelOnePresentation S)
    (rxState S baseState).admissible S
  intro potential heq
  have hx := rxMap1_preserves_nonboundary baseTannerSquarePresentation
    baseTannerSquareAdmissibleV4.toTannerSquareAdmissible S seedCocycle
    seedCocycle_not_coboundary potential
  change tannerCoboundary0 (rxReplacementPresentation baseTannerSquarePresentation S)
    potential = rxMap1Coord baseTannerSquarePresentation S seedCocycle at heq
  erw [rxPresentation_coboundary0_eq _ baseTannerSquareAdmissibleV4
    baseTannerSquareCellularRegular S] at heq
  exact hx heq
noncomputable def levelTwoXCode (S : OddScale) :
    LinearCode Field (levelTwoPresentation S).Q :=
  (levelTwoChainComplex S).firstCoboundaryCheckCode
noncomputable def levelTwoZCode (S : OddScale) :
    LinearCode Field (levelTwoPresentation S).Q :=
  (levelTwoChainComplex S).middleBoundaryCode
theorem levelTwo_coboundary0_eq (S : OddScale) :
    wordLinearMapTranspose (levelTwoChainComplex S).boundary1 =
      tannerCoboundary0 (levelTwoPresentation S) := by
  apply LinearMap.ext
  intro word
  funext q
  exact wordLinearMapTranspose_toLin'_apply
    (xqIncidenceMatrix (levelTwoPresentation S)) word q
theorem levelTwo_coboundary1_eq (S : OddScale) :
    wordLinearMapTranspose (levelTwoChainComplex S).boundary2 =
      tannerCoboundary1 (levelTwoPresentation S) := by
  apply LinearMap.ext
  intro word
  funext z
  exact wordLinearMapTranspose_toLin'_apply
    (qzIncidenceMatrix (levelTwoPresentation S)) word z
theorem levelTwoXLogical_sector (S : OddScale) :
    levelTwoXLogical S ∈ (levelTwoZCode S).dual.carrier ∧
      levelTwoXLogical S ∉ (levelTwoXCode S).carrier := by
  constructor
  · rw [levelTwoZCode,
      ChainComplexData.middleBoundaryCode_dual_carrier_eq_middleCocycleCode,
      ChainComplexData.mem_middleCocycleCode_iff, levelTwo_coboundary1_eq]
    exact levelTwoXLogical_cocycle S
  · intro hm
    obtain ⟨potential, hp⟩ :=
      ((levelTwoChainComplex S).mem_firstCoboundaryCheckCode_iff _).1 hm
    rw [levelTwo_coboundary0_eq] at hp
    exact levelTwoXLogical_nonboundary S potential hp
theorem levelTwo_exists_separating_cycle (S : OddScale) :
    ∃ cycle : Word Field (levelTwoPresentation S).Q,
      cycle ∈ (levelTwoXCode S).dual.carrier ∧
        wordPairing (levelTwoXLogical S) cycle ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hm : levelTwoXLogical S ∈ (levelTwoXCode S).dual.dual.carrier :=
    ((levelTwoXCode S).dual.mem_dual _).2 h
  rw [LinearCode.dual_dual_carrier_eq] at hm
  exact (levelTwoXLogical_sector S).2 hm
noncomputable def levelTwoZLogical (S : OddScale) :
    Word Field (levelTwoPresentation S).Q :=
  Classical.choose (levelTwo_exists_separating_cycle S)
theorem levelTwoZLogical_sector (S : OddScale) :
    levelTwoZLogical S ∈ (levelTwoXCode S).dual.carrier ∧
      levelTwoZLogical S ∉ (levelTwoZCode S).carrier := by
  have hs := Classical.choose_spec (levelTwo_exists_separating_cycle S)
  refine ⟨hs.1, ?_⟩
  intro hz
  exact hs.2 ((levelTwoZCode S).orthogonal_of_mem_dual
    (levelTwoXLogical_sector S).1 hz)
theorem levelTwo_exists_pureXMinimum (S : OddScale) :
    ∃ d, PureXLogicalMinimumDistance (levelTwoXCode S) (levelTwoZCode S) d := by
  exact exists_relativeMinimumDistance_of_exists_mem_not_mem _ _
    (levelTwoChainComplex S).firstCoboundaryCheckCode_le_middleBoundaryCode_dual
    ⟨levelTwoXLogical S, levelTwoXLogical_sector S⟩
theorem levelTwo_exists_pureZMinimum (S : OddScale) :
    ∃ d, PureZLogicalMinimumDistance (levelTwoXCode S) (levelTwoZCode S) d := by
  exact exists_relativeMinimumDistance_of_exists_mem_not_mem _ _
    (levelTwoChainComplex S).middleBoundaryCode_le_firstCoboundaryCheckCode_dual
    ⟨levelTwoZLogical S, levelTwoZLogical_sector S⟩
noncomputable def levelTwoXDistance (S : OddScale) : Nat :=
  Classical.choose (levelTwo_exists_pureXMinimum S)
noncomputable def levelTwoZDistance (S : OddScale) : Nat :=
  Classical.choose (levelTwo_exists_pureZMinimum S)
noncomputable def levelTwoLocalComplex (S : OddScale) :
    MultiscaleDecoder.LocalComplexData (Vertex (levelOnePresentation S))
      (levelTwoPresentation S).Z (levelTwoPresentation S).Q := by
  classical
  exact
    { syndromeRegion := fun center => BDL26ReplacementSupport.fiberRegion
        (fun coordinate : RZZ (levelOnePresentation S) S => Vertex.z coordinate.1) center
      correctionRegion := BDL26ReplacementSupport.fiberRegion
        (BDL26ReplacementSupport.rzCorrectionOwner (levelOnePresentation S) S) }
noncomputable def levelTwoLocalError (S : OddScale)
    (error : Word Field (levelTwoPresentation S).Q) : Prop :=
  ∃ center : Vertex (levelOnePresentation S),
    hammingSupport error ⊆ (levelTwoLocalComplex S).correctionRegion center
def qCoordinateOfOwner (P : TannerSquarePresentation) (defaultQ : P.Q) : Vertex P → P.Q
  | .q q => q
  | .x _ => defaultQ
  | .z _ => defaultQ
def levelOneQDefault (S : OddScale) : (levelOnePresentation S).Q :=
  Sum.inr ⟨(0 : BaseQubit), (0, Sum.inl (Sum.inl ()))⟩
noncomputable def coordinatePreimageOr {Q I : Type} (embed : I → Q)
    (fallback : I) (q : Q) : I := by
  classical
  exact if h : ∃ i, embed i = q then Classical.choose h else fallback
end QEC.Coding.BDL26LevelTwoDistance


