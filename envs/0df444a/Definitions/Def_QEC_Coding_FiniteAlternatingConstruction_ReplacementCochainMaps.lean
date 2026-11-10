-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
-- name    : QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T00:09:15.327346+00:00
-- url     : https://prove2.me/theorems/72cb0401-b960-4e9b-b734-273c4ea27165
-- title:
--   Replacement Cochain Maps
-- statement:
--   Definitions and structural lemmas for Replacement Cochain Maps, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzFace_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzQ_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzX_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzZ_card
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_map2Coord_canonicalBasis
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary0_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary1_canonicalBasis_apply
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
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
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
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.alternatingCarrier_zero
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_target_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_target_val
attribute [local simp] QEC.Coding.BDL26FiniteTannerSquare.doubleCylinderEndInclusion_apply
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzFace_card
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzQ_card
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzX_card
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzZ_card
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.map2Coord_canonicalBasis
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary0_canonicalBasis_apply
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1_canonicalBasis_apply
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
namespace QEC.Coding.BDL26ReplacementCochainMaps
open scoped BigOperators Classical
open QEC.Coding
open QEC.Coding.BDL26FiniteTannerSquare
open QEC.Coding.BDL26TannerLocalRegularity
open QEC.Coding.BDL26RXLocalReplacement
open QEC.Coding.BDL26RZLocalReplacement
open QEC.Coding.BDL26RZMap1CoordinateBridge
open QEC.Coding.MultiscaleDecoder
abbrev Field := BDL26Field
abbrev Two := BDL26FiniteTannerSquare.Two
def rxMap1Coord (P : TannerSquarePresentation) (S : OddScale) :
    Word Field P.Q →ₗ[Field] Word Field (RX1 P S) where
  toFun := fun word target => match target with
    | Sum.inl _ => 0
    | Sum.inr qVertex => word qVertex.1
  map_add' := by
    intro first second
    funext target
    rcases target with _ | _ <;> rfl
  map_smul' := by
    intro coefficient word
    funext target
    rcases target with _ | _ <;> rfl
def rxMap0Coord (P : TannerSquarePresentation) (S : OddScale) :
    Word Field P.X →ₗ[Field] Word Field (RX0 P S) :=
  rxAggregateDegreeZero P S
def rxMap2Coord (P : TannerSquarePresentation) (S : OddScale) :
    Word Field P.Z →ₗ[Field] Word Field (RX2 P S) :=
  rxAggregateDegreeTwo P S
structure RXMapData (P : TannerSquarePresentation) (S : OddScale) where
  map0 : Word Field P.X →ₗ[Field] Word Field (RX0 P S)
  map1 : Word Field P.Q →ₗ[Field] Word Field (RX1 P S)
  map2 : Word Field P.Z →ₗ[Field] Word Field (RX2 P S)
def rxMap (P : TannerSquarePresentation) (S : OddScale) : RXMapData P S where
  map0 := rxMap0Coord P S
  map1 := rxMap1Coord P S
  map2 := rxMap2Coord P S
@[simp] theorem rxMap1Coord_localEdge
    (P : TannerSquarePresentation) (S : OddScale) (word : Word Field P.Q)
    (edge : Σ x : P.X, DoubleCylinderEdge P x S) :
    rxMap1Coord P S word (Sum.inl edge) = 0 := rfl
@[simp] theorem rxMap1Coord_qVertex
    (P : TannerSquarePresentation) (S : OddScale) (word : Word Field P.Q)
    (vertex : Σ q : P.Q, QDoubleCylinderVertex P q S) :
    rxMap1Coord P S word (Sum.inr vertex) = word vertex.1 := rfl
def rxMap1BasisImage (P : TannerSquarePresentation) (S : OddScale)
    (q : P.Q) : Word Field (RX1 P S) := fun target => match target with
  | Sum.inl _ => 0
  | Sum.inr qVertex => if qVertex.1 = q then 1 else 0
@[simp] theorem rxMap1Coord_canonicalBasis
    (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    rxMap1Coord P S (canonicalBasisWord q) = rxMap1BasisImage P S q := by
  classical
  ext target
  rcases target with localEdge | qVertex
  · rfl
  · unfold rxMap1Coord rxMap1BasisImage canonicalBasisWord
    dsimp
    by_cases h : qVertex.1 = q
    · subst q
      simp
    · simp [h]
noncomputable def rxMap1ParentRegion
    (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    Finset (RX1 P S) := by
  classical
  exact Finset.univ.filter fun target => match target with
    | Sum.inl _ => False
    | Sum.inr qVertex => qVertex.1 = q
theorem rxMap1BasisImage_ne_zero_iff_mem_parentRegion
    (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (target : RX1 P S) :
    rxMap1BasisImage P S q target ≠ 0 ↔
      target ∈ rxMap1ParentRegion P S q := by
  classical
  rcases target with localEdge | qVertex
  · unfold rxMap1BasisImage rxMap1ParentRegion
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (0 : Field) ≠ 0 ↔ False
    simp
  · unfold rxMap1BasisImage rxMap1ParentRegion
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (if qVertex.1 = q then (1 : Field) else 0) ≠ 0 ↔
      qVertex.1 = q
    by_cases h : qVertex.1 = q <;> simp [h]
noncomputable def rxMap1FiniteBasisAction
    (P : TannerSquarePresentation) (S : OddScale) :
    TypedFiniteBasisAction (rxMap P S).map1 where
  basisImage := rxMap1BasisImage P S
  basis_action := rxMap1Coord_canonicalBasis P S
noncomputable def rxMap1ExtensionZeroLocalSupportImage
    (P : TannerSquarePresentation) (S : OddScale) :
    @ExtensionZeroLocalSupportImage P.Q P.Q (RX1 P S)
      inferInstance inferInstance inferInstance
      (Classical.decEq P.Q) (Classical.decEq (RX1 P S))
      (rxMap P S).map1 := by
  classical
  letI : DecidableEq P.Q := Classical.decEq _
  letI : DecidableEq (RX1 P S) := Classical.decEq _
  exact {
    sourceRegion := fun q => {q}
    targetRegion := rxMap1ParentRegion P S
    extensionByZero := fun q => zeroExtendWord ({q} : Finset P.Q)
    extension_zero := by
      intro q localWord source hsource
      change (if h : source ∈ ({q} : Finset P.Q) then
        localWord ⟨source, h⟩ else 0) = 0
      rw [dif_neg hsource]
    extension_on_region := by
      intro q localWord source
      change (if h : source.1 ∈ ({q} : Finset P.Q) then
        localWord ⟨source.1, h⟩ else 0) = localWord source
      simp
    selectedMapBasisImage := rxMap1BasisImage P S
    selectedMap_basis_action := rxMap1Coord_canonicalBasis P S
    selectedMap_basis_support := by
      intro owner source target hsource htarget
      have hsourceEq : source = owner := by simpa using hsource
      subst source
      by_contra hnonzero
      exact htarget ((rxMap1BasisImage_ne_zero_iff_mem_parentRegion
        P S owner target).1 hnonzero)
    selectedMap_basis_image := by
      intro owner source target hsource hnonzero
      have hsourceEq : source = owner := by simpa using hsource
      subst source
      exact (rxMap1BasisImage_ne_zero_iff_mem_parentRegion
        P S owner target).1 hnonzero }
def rxMap2BasisImage (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) : Word Field (RX2 P S) := fun target => match target with
  | Sum.inl _ => 0
  | Sum.inr zPoint => if zPoint.1 = z then 1 else 0
@[simp] theorem rxMap2Coord_canonicalBasis
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z) :
    rxMap2Coord P S (canonicalBasisWord z) = rxMap2BasisImage P S z := by
  classical
  ext target
  rcases target with auxiliary | zPoint
  · rcases auxiliary with xFace | qEdge <;> rfl
  · unfold rxMap2Coord rxAggregateDegreeTwo rxMap2BasisImage
    dsimp
    unfold canonicalBasisWord
    by_cases h : zPoint.1 = z
    · subst z
      simp
    · simp [h]
noncomputable def rxMap2ParentRegion
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z) :
    Finset (RX2 P S) := by
  classical
  exact Finset.univ.filter fun target => match target with
    | Sum.inl _ => False
    | Sum.inr zPoint => zPoint.1 = z
theorem rxMap2BasisImage_ne_zero_iff_mem_parentRegion
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (target : RX2 P S) :
    rxMap2BasisImage P S z target ≠ 0 ↔
      target ∈ rxMap2ParentRegion P S z := by
  classical
  rcases target with auxiliary | zPoint
  · unfold rxMap2BasisImage rxMap2ParentRegion
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp
  · unfold rxMap2BasisImage rxMap2ParentRegion
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : zPoint.1 = z <;> simp [h]
noncomputable def rxMap2FiniteBasisAction
    (P : TannerSquarePresentation) (S : OddScale) :
    TypedFiniteBasisAction (rxMap P S).map2 where
  basisImage := rxMap2BasisImage P S
  basis_action := rxMap2Coord_canonicalBasis P S
noncomputable def rxMap2ExtensionZeroLocalSupportImage
    (P : TannerSquarePresentation) (S : OddScale) :
    @ExtensionZeroLocalSupportImage P.Z P.Z (RX2 P S)
      inferInstance inferInstance inferInstance
      (Classical.decEq P.Z) (Classical.decEq (RX2 P S))
      (rxMap P S).map2 := by
  classical
  letI : DecidableEq P.Z := Classical.decEq _
  letI : DecidableEq (RX2 P S) := Classical.decEq _
  exact {
    sourceRegion := fun z => {z}
    targetRegion := rxMap2ParentRegion P S
    extensionByZero := fun z => zeroExtendWord ({z} : Finset P.Z)
    extension_zero := by
      intro z localWord source hsource
      change (if h : source ∈ ({z} : Finset P.Z) then
        localWord ⟨source, h⟩ else 0) = 0
      rw [dif_neg hsource]
    extension_on_region := by
      intro z localWord source
      change (if h : source.1 ∈ ({z} : Finset P.Z) then
        localWord ⟨source.1, h⟩ else 0) = localWord source
      simp
    selectedMapBasisImage := rxMap2BasisImage P S
    selectedMap_basis_action := rxMap2Coord_canonicalBasis P S
    selectedMap_basis_support := by
      intro owner source target hsource htarget
      have hsourceEq : source = owner := by simpa using hsource
      subst source
      by_contra hnonzero
      exact htarget ((rxMap2BasisImage_ne_zero_iff_mem_parentRegion
        P S owner target).1 hnonzero)
    selectedMap_basis_image := by
      intro owner source target hsource hnonzero
      have hsourceEq : source = owner := by simpa using hsource
      subst source
      exact (rxMap2BasisImage_ne_zero_iff_mem_parentRegion
        P S owner target).1 hnonzero }
noncomputable def vertexIndicator {Vertex : Type}
    (first second : Vertex) : Field := by
  classical
  exact if first = second then 1 else 0
noncomputable def rxCoboundary0
    (P : TannerSquarePresentation) (S : OddScale) :
    Word Field (RX0 P S) →ₗ[Field] Word Field (RX1 P S) :=
  wordLinearMapTranspose (rxBoundary1 P S)
noncomputable def rxCoboundary1
    (P : TannerSquarePresentation) (S : OddScale) :
    Word Field (RX1 P S) →ₗ[Field] Word Field (RX2 P S) :=
  wordLinearMapTranspose (rxBoundary2 P S)
noncomputable def rzCoboundary0
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) : Word Field (RZX P S) →ₗ[Field] Word Field (RZQ P S) :=
  tannerCoboundary0
    (rzReplacementPresentation P
      A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissible S)
noncomputable def extendRZQEdgeWord
    (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    Word Field (QDoubleCylinderEdge (transposePresentation P) q S) →ₗ[Field]
      Word Field (RZX P S) := by
  classical
  exact wordPushforward (rzMap1QEdgeX P S q)
noncomputable def extendRZQVertexWord
    (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    Word Field (QDoubleCylinderVertex (transposePresentation P) q S) →ₗ[Field]
      Word Field (RZQ P S) := by
  classical
  exact wordPushforward (fun vertex => Sum.inr ⟨q, vertex⟩)
noncomputable def extendRZLocalEdgeWord
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z) :
    Word Field (ZDoubleCylinderEdge P z S) →ₗ[Field]
      Word Field (RZQ P S) := by
  classical
  exact wordPushforward (fun edge => Sum.inl ⟨z, edge⟩)
noncomputable def rzMap0QPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (q : P.Q) (hxq : P.xq x q = true) :
    Word Field (QDoubleCylinderEdge (transposePresentation P) q S) :=
  pathChain
    (qDoubleCylinderPath (transposePresentation P)
      (transposeTannerSquareAdmissible P
        A4.toTannerSquareAdmissible) q S
      (rzXQVertex P q x hxq S 0))
def rzGridZero (S : OddScale) : Fin (S.half + 1) :=
  ⟨0, by omega⟩
def rzGridLast (S : OddScale) : Fin (S.half + 1) :=
  ⟨S.half, by omega⟩
def qArmChainVertex (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (edge : QStarEdge P q) (i : Fin (S.half + 1)) :
    QSubdivisionVertex P q S :=
  if hzero : i.1 = 0 then Sum.inl (Sum.inl ())
  else if hlast : i.1 = S.half then Sum.inl (Sum.inr edge)
  else Sum.inr (edge, ⟨i.1 - 1, by have := i.2; omega⟩)
noncomputable def rzMap0QRay
    (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (q : P.Q) (hxq : P.xq x q = true) :
    Word Field (QDoubleCylinderEdge (transposePresentation P) q S) := by
  classical
  exact ∑ i : Fin S.half,
    canonicalBasisWord (Sum.inl (0, (⟨x, hxq⟩, i)))
noncomputable def subdivisionWholeFaceChain
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) : Word Field (SubdivisionFace P x S) :=
  ∑ i : Fin S.half, ∑ j : Fin S.half,
    canonicalBasisWord (⟨face, i, j⟩ : SubdivisionFace P x S)
noncomputable def extendCopyZeroSubdivisionFaceWord
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Word Field (SubdivisionFace P x S) →ₗ[Field]
      Word Field (DoubleCylinderFace P x S) where
  toFun word target := match target with
    | Sum.inl (copy, face) => if copy = 0 then word face else 0
    | Sum.inr _ => 0
  map_add' := by
    intro first second
    funext target
    rcases target with ⟨copy, face⟩ | rectangle
    · by_cases hcopy : copy = 0 <;> simp [hcopy]
    · rfl
  map_smul' := by
    intro coefficient word
    funext target
    rcases target with ⟨copy, face⟩ | rectangle
    · by_cases hcopy : copy = 0 <;> simp [hcopy]
    · rfl
noncomputable def extendCopyZeroSubdivisionEdgeWord
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Word Field (SubdivisionEdge P x S) →ₗ[Field]
      Word Field (DoubleCylinderEdge P x S) where
  toFun word target := match target with
    | Sum.inl (copy, edge) => if copy = 0 then word edge else 0
    | Sum.inr _ => 0
  map_add' := by
    intro first second
    funext target
    rcases target with ⟨copy, edge⟩ | boundary
    · by_cases hcopy : copy = 0 <;> simp [hcopy]
    · rfl
  map_smul' := by
    intro coefficient word
    funext target
    rcases target with ⟨copy, edge⟩ | boundary
    · by_cases hcopy : copy = 0 <;> simp [hcopy]
    · rfl
noncomputable def extendRZFaceWord
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z) :
    Word Field (ZDoubleCylinderFace P z S) →ₗ[Field]
      Word Field (RZX P S) := by
  classical
  exact wordPushforward (fun face => Sum.inl (Sum.inl ⟨z, face⟩))
abbrev RZOldFaceOver (P : TannerSquarePresentation) (x : P.X) (z : P.Z) :=
  { face : P.Face // P.faceX face = x ∧ P.faceZ face = z }
def rzOldFaceOverZStarFace
    (P : TannerSquarePresentation) (x : P.X) (z : P.Z)
    (owner : RZOldFaceOver P x z) : XStarFace (transposePresentation P) z :=
  ⟨owner.1, by
    change decide (P.faceZ owner.1 = z) = true
    exact decide_eq_true owner.2.2⟩
@[simp] theorem extendCopyZeroSubdivisionEdgeWord_canonicalBasis
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : SubdivisionEdge P x S) :
    extendCopyZeroSubdivisionEdgeWord P x S (canonicalBasisWord edge) =
      canonicalBasisWord (Sum.inl (0, edge) : DoubleCylinderEdge P x S) := by
  classical
  ext target
  rcases target with ⟨copy, other⟩ | vertical
  · fin_cases copy <;> simp [extendCopyZeroSubdivisionEdgeWord, canonicalBasisWord, Pi.single_apply]
  · simp [extendCopyZeroSubdivisionEdgeWord, canonicalBasisWord, Pi.single_apply]
noncomputable def rzMap0LocalFaceFill
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (z : P.Z) :
    Word Field (RZX P S) :=
  ∑ owner : RZOldFaceOver P x z,
    extendRZFaceWord P S z
      (extendCopyZeroSubdivisionFaceWord (transposePresentation P) z S
        (subdivisionWholeFaceChain (transposePresentation P) z S
          (rzOldFaceOverZStarFace P x z owner)))
noncomputable def rzMap0BasisImage
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) :
    Word Field (RZX P S) :=
  canonicalBasisWord (Sum.inr (x, 0)) +
    (∑ q : P.Q, if hxq : P.xq x q = true then
      extendRZQEdgeWord P S q (rzMap0QRay P S x q hxq) else 0) +
    ∑ z : P.Z, rzMap0LocalFaceFill P S x z
noncomputable def rzMap0Coord
    (P : TannerSquarePresentation) (S : OddScale) :
    Word Field P.X →ₗ[Field] Word Field (RZX P S) := by
  classical
  exact ClassicalWeightReduction.linearMapOfBasisImages
    (F := Field) (rzMap0BasisImage P S)
@[simp] theorem rzMap0Coord_canonicalBasis
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) :
    rzMap0Coord P S (canonicalBasisWord x) = rzMap0BasisImage P S x := by
  classical
  have hbasis : canonicalBasisWord (F := Field) x = Pi.single x 1 := by
    ext coordinate
    simp [canonicalBasisWord, Pi.single_apply]
  rw [hbasis]
  exact ClassicalWeightReduction.linearMapOfBasisImages_single
    (F := Field) (rzMap0BasisImage P S) x
structure RZCochainMapData (P : TannerSquarePresentation) (S : OddScale) where
  map0 : Word Field P.X →ₗ[Field] Word Field (RZX P S)
  map1 : Word Field P.Q →ₗ[Field] Word Field (RZQ P S)
  map2 : Word Field P.Z →ₗ[Field] Word Field (RZZ P S)
noncomputable def rzCochainMap
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) : RZCochainMapData P S where
  map0 := rzMap0Coord P S
  map1 := map1Coord P A4 S
  map2 := map2Coord P A4 S
noncomputable def rzCoboundary1
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) : Word Field (RZQ P S) →ₗ[Field] Word Field (RZZ P S) :=
  tannerCoboundary1
    (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
noncomputable def rzMap2BasisImage
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) : Word Field (RZZ P S) :=
  canonicalBasisWord ⟨z, rzMap1ZRoot P A4 z S⟩
@[simp] theorem rzMap2BasisImage_eq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) :
    map2Coord P A4 S (canonicalBasisWord z) =
      rzMap2BasisImage P A4 S z :=
  map2Coord_canonicalBasis P A4 S z
noncomputable def rzMap2ParentRegion
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) : Finset (RZZ P S) := by
  classical
  exact Finset.univ.filter fun target =>
    target = ⟨z, rzMap1ZRoot P A4 z S⟩
theorem rzMap2BasisImage_ne_zero_iff_mem_parentRegion
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (target : RZZ P S) :
    rzMap2BasisImage P A4 S z target ≠ 0 ↔
      target ∈ rzMap2ParentRegion P A4 S z := by
  classical
  unfold rzMap2BasisImage rzMap2ParentRegion canonicalBasisWord
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.single_apply]
  by_cases h : target = ⟨z, rzMap1ZRoot P A4 z S⟩ <;> simp [h]
noncomputable def rzMap2FiniteBasisAction
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) : TypedFiniteBasisAction (map2Coord P A4 S) where
  basisImage := rzMap2BasisImage P A4 S
  basis_action := rzMap2BasisImage_eq P A4 S
noncomputable def rzMap2ExtensionZeroLocalSupportImage
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) :
    @ExtensionZeroLocalSupportImage P.Z P.Z (RZZ P S)
      inferInstance inferInstance inferInstance
      (Classical.decEq P.Z) (Classical.decEq (RZZ P S))
      (map2Coord P A4 S) := by
  classical
  letI : DecidableEq P.Z := Classical.decEq _
  letI : DecidableEq (RZZ P S) := Classical.decEq _
  exact {
    sourceRegion := fun z => {z}
    targetRegion := rzMap2ParentRegion P A4 S
    extensionByZero := fun z => zeroExtendWord ({z} : Finset P.Z)
    extension_zero := by
      intro z localWord source hsource
      change (if h : source ∈ ({z} : Finset P.Z) then
        localWord ⟨source, h⟩ else 0) = 0
      rw [dif_neg hsource]
    extension_on_region := by
      intro z localWord source
      change (if h : source.1 ∈ ({z} : Finset P.Z) then
        localWord ⟨source.1, h⟩ else 0) = localWord source
      simp
    selectedMapBasisImage := rzMap2BasisImage P A4 S
    selectedMap_basis_action := rzMap2BasisImage_eq P A4 S
    selectedMap_basis_support := by
      intro owner source target hsource htarget
      have hsourceEq : source = owner := by simpa using hsource
      subst source
      by_contra hnonzero
      exact htarget ((rzMap2BasisImage_ne_zero_iff_mem_parentRegion
        P A4 S owner target).1 hnonzero)
    selectedMap_basis_image := by
      intro owner source target hsource hnonzero
      have hsourceEq : source = owner := by simpa using hsource
      subst source
      exact (rzMap2BasisImage_ne_zero_iff_mem_parentRegion
        P A4 S owner target).1 hnonzero }
def finiteCoordinateComposite {Coordinate : Nat → Type}
    (step : ∀ n, Word Field (Coordinate n) →ₗ[Field] Word Field (Coordinate (n + 1))) :
    ∀ n, Word Field (Coordinate 0) →ₗ[Field] Word Field (Coordinate n)
  | 0 => LinearMap.id
  | n + 1 => (step n).comp (finiteCoordinateComposite step n)
end QEC.Coding.BDL26ReplacementCochainMaps


