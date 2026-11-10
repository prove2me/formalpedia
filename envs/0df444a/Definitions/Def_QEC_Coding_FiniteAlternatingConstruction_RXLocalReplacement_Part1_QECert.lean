-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement_Part1_QECert
-- name    : QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement_Part1_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T23:55:25.373453+00:00
-- url     : https://prove2.me/theorems/133dd860-ce88-4ac9-88cd-e5469ba15506
-- title:
--   RXLocal Replacement: first literal declaration block
-- statement:
--   Definitions and structural lemmas for RXLocal Replacement, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValence
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_TannerSquarePresentation_faceQ_injective
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderRectangleBoundaryEdge_injective
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderRectangleCorner_injective
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinder_rectangle_vertical_end
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinder_rectangle_vertical_start
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_sharedQ_indicator_sum_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_subdivisionBoundaryEdgeStart_ne_end
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_subdivisionEdgeStart_ne_end
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_subdivisionFaceBoundaryEdge_injective
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_subdivisionFaceEdgeMatrix_eq_one_iff
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_subdivisionGridVertex_eq_edgeInterior_coordinates
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_subdivisionGridVertex_eq_faceInterior_coordinates
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_subdivisionGridVertex_fixedFace_injective
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
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_qToXDoubleCylinderEdge_end
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_qToXDoubleCylinderEdge_start
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_subdivisionBoundaryIncidentEdge_original_one
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_subdivisionBoundaryIncidentEdge_original_zero
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
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
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.alternatingCarrier_zero
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_target_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_target_val
attribute [local simp] QEC.Coding.BDL26FiniteTannerSquare.doubleCylinderEndInclusion_apply
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
namespace QEC
namespace Coding
namespace BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
universe u
abbrev Field := BDL26FiniteTannerSquare.Field
abbrev Two := BDL26FiniteTannerSquare.Two
abbrev RX0 (P : TannerSquarePresentation) (S : OddScale) :=
  Σ x : P.X, DoubleCylinderVertex P x S
abbrev RX1 (P : TannerSquarePresentation) (S : OddScale) :=
  (Σ x : P.X, DoubleCylinderEdge P x S) ⊕
    (Σ q : P.Q, QDoubleCylinderVertex P q S)
abbrev RX2 (P : TannerSquarePresentation) (S : OddScale) :=
  ((Σ x : P.X, DoubleCylinderFace P x S) ⊕
    (Σ q : P.Q, QDoubleCylinderEdge P q S)) ⊕ (P.Z × Two)
def rxCarrier (P : TannerSquarePresentation) (S : OddScale) :
    FiniteCochainCarrier where
  C0 := RX0 P S
  C1 := RX1 P S
  C2 := RX2 P S
  fintypeC0 := inferInstance
  fintypeC1 := inferInstance
  fintypeC2 := inferInstance
abbrev RXLocalFace (P : TannerSquarePresentation) (S : OddScale) :=
  Σ x : P.X, DoubleCylinderFace P x S × (Two × Two)
abbrev RXXQGlueFace (P : TannerSquarePresentation) (S : OddScale) :=
  Σ a : XQEdge P, QDoubleCylinderEdge P a.1.2 S × Two
abbrev RXOldZFace (P : TannerSquarePresentation) := P.Face × Two
abbrev RXFace (P : TannerSquarePresentation) (S : OddScale) :=
  RXLocalFace P S ⊕ (RXXQGlueFace P S ⊕ RXOldZFace P)
def lowerGridIndex {n : Nat} (i : Fin n) : Fin (n + 1) :=
  ⟨i.1, Nat.lt_succ_of_lt i.2⟩
def upperGridIndex {n : Nat} (i : Fin n) : Fin (n + 1) :=
  ⟨i.1 + 1, by omega⟩
def twoSelect {Value : Type} (first second : Value) (endpoint : Two) : Value :=
  if endpoint = 0 then first else second
def gridEndpoint {n : Nat} (i : Fin n) (endpoint : Two) : Fin (n + 1) :=
  twoSelect (lowerGridIndex i) (upperGridIndex i) endpoint
def edgeEndpoint {Vertex Edge : Type} (start finish : Edge → Vertex)
    (edge : Edge) (endpoint : Two) : Vertex :=
  twoSelect (start edge) (finish edge) endpoint
@[simp] theorem twoSelect_zero {Value : Type} (first second : Value) :
    twoSelect first second 0 = first := by
  simp [twoSelect]
@[simp] theorem twoSelect_one {Value : Type} (first second : Value) :
    twoSelect first second 1 = second := by
  simp [twoSelect]
theorem twoSelect_injective {Value : Type} {first second : Value}
    (hne : first ≠ second) :
    Function.Injective (twoSelect first second) := by
  intro left right h
  fin_cases left <;> fin_cases right <;>
    simp [twoSelect, hne, Ne.symm hne] at h ⊢
theorem gridEndpoint_injective {n : Nat} (i : Fin n) :
    Function.Injective (gridEndpoint i) := by
  apply twoSelect_injective
  intro h
  have hvalue := congrArg Fin.val h
  simp [lowerGridIndex, upperGridIndex] at hvalue
theorem tannerDoubleCylinderEdgeStart_ne_end
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : DoubleCylinderEdge P x S) :
    tannerDoubleCylinderEdgeStart P x S edge ≠
      tannerDoubleCylinderEdgeEnd P x S edge := by
  rcases edge with edge | vertex
  · intro h
    exact subdivisionEdgeStart_ne_end P x S edge.2
      (congrArg Prod.snd h)
  · intro h
    have hcopy := congrArg Prod.fst h
    change (0 : Two) = 1 at hcopy
    norm_num at hcopy
def rxTwoElim {motive : Fin 2 → Sort u}
    (zero : motive 0) (one : motive 1) (i : Fin 2) : motive i := by
  rcases i with ⟨i, hi⟩
  rcases i with _ | i
  · exact zero
  · rcases i with _ | i
    · exact one
    · omega
@[simp] theorem rxTwoElim_zero {motive : Fin 2 → Sort u}
    (zero : motive 0) (one : motive 1) :
    rxTwoElim zero one 0 = zero := rfl
@[simp] theorem rxTwoElim_one {motive : Fin 2 → Sort u}
    (zero : motive 0) (one : motive 1) :
    rxTwoElim zero one 1 = one := rfl
structure RXRadialLocalEdge (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) where
  edge : XQEdge P
  member : xStarEdgeMember P x (Sum.inl edge) = true
  copy : Two
  segment : Fin S.half
def rxRadialGridZero (S : OddScale) : Fin S.half :=
  ⟨0, S.half_pos⟩
def rxRadialDoubleCylinderEdge
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (radial : RXRadialLocalEdge P S x) : DoubleCylinderEdge P x S :=
  Sum.inl (radial.copy,
    Sum.inl (⟨Sum.inl radial.edge, radial.member⟩, radial.segment))
def rxRadialSubdivisionFace
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (x : P.X) (radial : RXRadialLocalEdge P S x) :
    SubdivisionFace P x S :=
  let owner := A3.xRadialFaceOwner x radial.edge radial.member
  rxTwoElim (motive := fun _ => SubdivisionFace P x S)
    (owner.1.1, radial.segment, rxRadialGridZero S)
    (owner.1.1, rxRadialGridZero S, radial.segment) owner.1.2
def rxRadialDoubleCylinderFace
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (x : P.X) (radial : RXRadialLocalEdge P S x) :
    DoubleCylinderFace P x S :=
  Sum.inl (radial.copy, rxRadialSubdivisionFace P A3 S x radial)
theorem rxRadialDoubleCylinderFace_incidence
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (x : P.X) (radial : RXRadialLocalEdge P S x) :
    doubleCylinderFaceEdgeMatrix P x S
      (rxRadialDoubleCylinderEdge P S x radial)
      (rxRadialDoubleCylinderFace P A3 S x radial) = 1 := by
  simp only [rxRadialDoubleCylinderEdge, rxRadialDoubleCylinderFace]
  rw [doubleCylinder_end_face_boundary]
  apply (subdivisionFaceEdgeMatrix_eq_one_iff P x S _ _).2
  let owner := A3.xRadialFaceOwner x radial.edge radial.member
  have hedge := owner.2
  refine rxTwoElim (motive := fun corner => owner.1.2 = corner →
      ∃ slot : Two × Two,
        subdivisionFaceBoundaryEdge P x S
          (rxRadialSubdivisionFace P A3 S x radial) slot =
            Sum.inl (⟨Sum.inl radial.edge, radial.member⟩,
              radial.segment)) ?_ ?_ owner.1.2 rfl
  · intro hcorner
    refine ⟨(0, 0), ?_⟩
    rw [hcorner] at hedge
    have hface : rxRadialSubdivisionFace P A3 S x radial =
        (owner.1.1, radial.segment, rxRadialGridZero S) := by
      simp only [rxRadialSubdivisionFace, owner]
      rw [hcorner]
      rfl
    rw [hface, subdivisionFaceBoundaryEdge_zero_zero]
    change Sum.inl (xStarFaceXQEdge P x owner.1.1 0, radial.segment) =
      Sum.inl (⟨Sum.inl radial.edge, radial.member⟩, radial.segment)
    exact congrArg (fun starEdge : XStarEdge P x =>
      (Sum.inl (starEdge, radial.segment) : SubdivisionEdge P x S)) hedge
  · intro hcorner
    refine ⟨(1, 0), ?_⟩
    rw [hcorner] at hedge
    have hface : rxRadialSubdivisionFace P A3 S x radial =
        (owner.1.1, rxRadialGridZero S, radial.segment) := by
      simp only [rxRadialSubdivisionFace, owner]
      rw [hcorner]
      rfl
    rw [hface, subdivisionFaceBoundaryEdge_one_zero]
    change Sum.inl (xStarFaceXQEdge P x owner.1.1 1, radial.segment) =
      Sum.inl (⟨Sum.inl radial.edge, radial.member⟩, radial.segment)
    exact congrArg (fun starEdge : XStarEdge P x =>
      (Sum.inl (starEdge, radial.segment) : SubdivisionEdge P x S)) hedge
def rxInteriorFaceIndex (S : OddScale) (i : Fin (S.half - 1)) :
    Fin S.half :=
  ⟨i.1, by have := i.2; omega⟩
noncomputable def rxLocalEdgeFaceOwner
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (x : P.X) (edge : DoubleCylinderEdge P x S) :
    {face : DoubleCylinderFace P x S //
      doubleCylinderFaceEdgeMatrix P x S edge face = 1} := by
  rcases edge with endEdge | boundaryVertex
  · rcases endEdge with ⟨copy, subdivisionEdge⟩
    rcases subdivisionEdge with original | interior
    · rcases original with ⟨starEdge, segment⟩
      rcases starEdge with ⟨rawEdge, hstar⟩
      rcases rawEdge with xqEdge | qzEdge
      · let radial : RXRadialLocalEdge P S x :=
          ⟨xqEdge, hstar, copy, segment⟩
        exact ⟨rxRadialDoubleCylinderFace P A3 S x radial,
          rxRadialDoubleCylinderFace_incidence P A3 S x radial⟩
      · let boundaryEdge : XStarBoundaryEdge P x :=
          ⟨Sum.inr qzEdge, by
            simpa [xStarBoundaryEdgeMember, xStarEdgeMember] using hstar⟩
        let rectangle := subdivisionOriginalBoundaryEdge
          P x S boundaryEdge segment
        refine ⟨Sum.inr rectangle, ?_⟩
        exact doubleCylinder_rectangle_end_boundary P x S copy rectangle
    · rcases interior with horizontal | vertical
      · let face : SubdivisionFace P x S :=
          (horizontal.1, horizontal.2.1,
            rxInteriorFaceIndex S horizontal.2.2)
        refine ⟨Sum.inl (copy, face), ?_⟩
        rw [doubleCylinder_end_face_boundary]
        apply (subdivisionFaceEdgeMatrix_eq_one_iff P x S _ _).2
        refine ⟨(0, 1), ?_⟩
        rw [subdivisionFaceBoundaryEdge_zero_one]
        change subdivisionHorizontalEdge P x S horizontal.1 horizontal.2.1
            ⟨horizontal.2.2.1 + 1, by
              have := horizontal.2.2.2
              omega⟩ =
          Sum.inr (Sum.inl horizontal)
        simp only [subdivisionHorizontalEdge]
        split <;> rename_i hzero
        · omega
        · split <;> rename_i hlast
          · have := horizontal.2.2.2
            omega
          · congr 3
      · let face : SubdivisionFace P x S :=
          (vertical.1, rxInteriorFaceIndex S vertical.2.1,
            vertical.2.2)
        refine ⟨Sum.inl (copy, face), ?_⟩
        rw [doubleCylinder_end_face_boundary]
        apply (subdivisionFaceEdgeMatrix_eq_one_iff P x S _ _).2
        refine ⟨(1, 1), ?_⟩
        rw [subdivisionFaceBoundaryEdge_one_one]
        change subdivisionVerticalEdge P x S vertical.1
            ⟨vertical.2.1.1 + 1, by
              have := vertical.2.1.2
              omega⟩ vertical.2.2 =
          Sum.inr (Sum.inr vertical)
        simp only [subdivisionVerticalEdge]
        split <;> rename_i hzero
        · omega
        · split <;> rename_i hlast
          · have := vertical.2.1.2
            omega
          · congr 3
  · obtain ⟨⟨boundaryEdge, endpoint⟩, hendpoint⟩ :=
      subdivisionBoundaryIncidentEdge P
        A3.toTannerSquareAdmissibleV2 x S boundaryVertex
    refine ⟨Sum.inr boundaryEdge, ?_⟩
    fin_cases endpoint
    · change BDL26TannerLocalRegularity.edgeEndpoint
        (subdivisionBoundaryEdgeStart P x S)
        (subdivisionBoundaryEdgeEnd P x S) boundaryEdge 0 =
          boundaryVertex at hendpoint
      rw [BDL26TannerLocalRegularity.edgeEndpoint_zero] at hendpoint
      simpa [hendpoint] using doubleCylinder_rectangle_vertical_start
        P x S boundaryEdge (subdivisionBoundaryEdgeStart_ne_end P x S boundaryEdge)
    · change BDL26TannerLocalRegularity.edgeEndpoint
        (subdivisionBoundaryEdgeStart P x S)
        (subdivisionBoundaryEdgeEnd P x S) boundaryEdge 1 =
          boundaryVertex at hendpoint
      rw [BDL26TannerLocalRegularity.edgeEndpoint_one] at hendpoint
      simpa [hendpoint] using doubleCylinder_rectangle_vertical_end
        P x S boundaryEdge (subdivisionBoundaryEdgeStart_ne_end P x S boundaryEdge)
def oldFaceInXStar (P : TannerSquarePresentation) (face : P.Face) :
    XStarFace P (P.faceX face) :=
  ⟨face, by simp [xStarFaceMember]⟩
noncomputable def localFaceX (P : TannerSquarePresentation) (S : OddScale) :
    RXLocalFace P S → RX0 P S
  | ⟨x, Sum.inl copyFace, corner⟩ =>
      ⟨x, (copyFace.1,
        subdivisionGridVertex P x S copyFace.2.1
          (gridEndpoint copyFace.2.2.1 corner.1)
          (gridEndpoint copyFace.2.2.2 corner.2))⟩
  | ⟨x, Sum.inr rectangle, corner⟩ =>
      ⟨x, doubleCylinderRectangleCorner P x S rectangle corner⟩
def localFaceZ (P : TannerSquarePresentation) (S : OddScale) :
    RXLocalFace P S → RX2 P S
  | ⟨x, face, _⟩ => Sum.inl (Sum.inl ⟨x, face⟩)
noncomputable def localFaceQ0EdgeAt
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    DoubleCylinderFace P x S → Two × Two → DoubleCylinderEdge P x S
  | Sum.inl copyFace, corner =>
      Sum.inl (copyFace.1,
        subdivisionFaceBoundaryEdge P x S copyFace.2 (0, corner.2))
  | Sum.inr rectangle, corner =>
      doubleCylinderRectangleBoundaryEdge P x S rectangle (0, corner.1)
noncomputable def localFaceQ0Edge
    (P : TannerSquarePresentation) (S : OddScale) :
    RXLocalFace P S → (Σ x : P.X, DoubleCylinderEdge P x S)
  | ⟨x, face, corner⟩ => ⟨x, localFaceQ0EdgeAt P x S face corner⟩
noncomputable def localFaceQ0 (P : TannerSquarePresentation) (S : OddScale) :
    RXLocalFace P S → RX1 P S := fun face =>
  Sum.inl (localFaceQ0Edge P S face)
noncomputable def localFaceQ1EdgeAt
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    DoubleCylinderFace P x S → Two × Two → DoubleCylinderEdge P x S
  | Sum.inl copyFace, corner =>
      Sum.inl (copyFace.1,
        subdivisionFaceBoundaryEdge P x S copyFace.2 (1, corner.1))
  | Sum.inr rectangle, corner =>
      doubleCylinderRectangleBoundaryEdge P x S rectangle (1, corner.2)
noncomputable def localFaceQ1Edge
    (P : TannerSquarePresentation) (S : OddScale) :
    RXLocalFace P S → (Σ x : P.X, DoubleCylinderEdge P x S)
  | ⟨x, face, corner⟩ => ⟨x, localFaceQ1EdgeAt P x S face corner⟩
noncomputable def localFaceQ1 (P : TannerSquarePresentation) (S : OddScale) :
    RXLocalFace P S → RX1 P S := fun face =>
  Sum.inl (localFaceQ1Edge P S face)
noncomputable def localFaceQAt (P : TannerSquarePresentation) (S : OddScale)
    (face : RXLocalFace P S) (corner : Two) : RX1 P S :=
  twoSelect (localFaceQ0 P S face) (localFaceQ1 P S face) corner
noncomputable def rxLocalEdgeCornerOwner
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (x : P.X) (edge : DoubleCylinderEdge P x S) :
    {owned : RXLocalFace P S × Two //
      localFaceQAt P S owned.1 owned.2 = Sum.inl ⟨x, edge⟩} := by
  rcases edge with endEdge | boundaryVertex
  · rcases endEdge with ⟨copy, subdivisionEdge⟩
    rcases subdivisionEdge with original | interior
    · rcases original with ⟨starEdge, segment⟩
      rcases starEdge with ⟨rawEdge, hstar⟩
      rcases rawEdge with xqEdge | qzEdge
      · let radial : RXRadialLocalEdge P S x :=
          ⟨xqEdge, hstar, copy, segment⟩
        let owner := A3.xRadialFaceOwner x xqEdge hstar
        refine rxTwoElim (motive := fun ownerCorner => owner.1.2 = ownerCorner →
            {owned : RXLocalFace P S × Two //
              localFaceQAt P S owned.1 owned.2 =
                Sum.inl ⟨x, rxRadialDoubleCylinderEdge P S x radial⟩}) ?_ ?_
          owner.1.2 rfl
        · intro hcorner
          refine ⟨(⟨x, rxRadialDoubleCylinderFace P A3 S x radial,
            (0, 0)⟩, 0), ?_⟩
          simp only [localFaceQAt, twoSelect_zero, localFaceQ0,
            localFaceQ0Edge, localFaceQ0EdgeAt,
            rxRadialDoubleCylinderFace, rxRadialDoubleCylinderEdge]
          congr 3
          apply congrArg (fun selected : SubdivisionEdge P x S =>
            (copy, selected))
          have hface : rxRadialSubdivisionFace P A3 S x radial =
              (owner.1.1, segment, rxRadialGridZero S) := by
            simp only [rxRadialSubdivisionFace, owner]
            rw [hcorner]
            rfl
          rw [hface, subdivisionFaceBoundaryEdge_zero_zero]
          have hedge := (A3.xRadialFaceOwner x xqEdge hstar).2
          rw [hcorner] at hedge
          change Sum.inl (xStarFaceXQEdge P x owner.1.1 0, segment) = _
          exact congrArg (fun selected : XStarEdge P x =>
            (Sum.inl (selected, segment) : SubdivisionEdge P x S)) hedge
        · intro hcorner
          refine ⟨(⟨x, rxRadialDoubleCylinderFace P A3 S x radial,
            (0, 0)⟩, 1), ?_⟩
          simp only [localFaceQAt, twoSelect_one, localFaceQ1,
            localFaceQ1Edge, localFaceQ1EdgeAt,
            rxRadialDoubleCylinderFace, rxRadialDoubleCylinderEdge]
          congr 3
          apply congrArg (fun selected : SubdivisionEdge P x S =>
            (copy, selected))
          have hface : rxRadialSubdivisionFace P A3 S x radial =
              (owner.1.1, rxRadialGridZero S, segment) := by
            simp only [rxRadialSubdivisionFace, owner]
            rw [hcorner]
            rfl
          rw [hface, subdivisionFaceBoundaryEdge_one_zero]
          have hedge := (A3.xRadialFaceOwner x xqEdge hstar).2
          rw [hcorner] at hedge
          change Sum.inl (xStarFaceXQEdge P x owner.1.1 1, segment) = _
          exact congrArg (fun selected : XStarEdge P x =>
            (Sum.inl (selected, segment) : SubdivisionEdge P x S)) hedge
      · let boundaryEdge : XStarBoundaryEdge P x :=
          ⟨Sum.inr qzEdge, by
            simpa [xStarBoundaryEdgeMember, xStarEdgeMember] using hstar⟩
        let rectangle := subdivisionOriginalBoundaryEdge
          P x S boundaryEdge segment
        refine ⟨(⟨x, Sum.inr rectangle, (copy, 0)⟩, 0), ?_⟩
        simp [localFaceQAt, localFaceQ0, localFaceQ0Edge,
          localFaceQ0EdgeAt, rectangle, subdivisionOriginalBoundaryEdge,
          boundaryEdge]
        apply Subtype.ext
        rfl
    · rcases interior with horizontal | vertical
      · let face : SubdivisionFace P x S :=
          (horizontal.1, horizontal.2.1,
            rxInteriorFaceIndex S horizontal.2.2)
        refine ⟨(⟨x, Sum.inl (copy, face), (0, 1)⟩, 0), ?_⟩
        simp only [localFaceQAt, twoSelect_zero, localFaceQ0,
          localFaceQ0Edge, localFaceQ0EdgeAt]
        congr 3
        apply congrArg (fun selected : SubdivisionEdge P x S =>
          (copy, selected))
        rw [subdivisionFaceBoundaryEdge_zero_one]
        change subdivisionHorizontalEdge P x S horizontal.1 horizontal.2.1
            ⟨horizontal.2.2.1 + 1, by
              have := horizontal.2.2.2
              omega⟩ = Sum.inr (Sum.inl horizontal)
        simp only [subdivisionHorizontalEdge]
        split <;> rename_i hzero
        · omega
        · split <;> rename_i hlast
          · have := horizontal.2.2.2
            omega
          · congr 3
      · let face : SubdivisionFace P x S :=
          (vertical.1, rxInteriorFaceIndex S vertical.2.1,
            vertical.2.2)
        refine ⟨(⟨x, Sum.inl (copy, face), (1, 0)⟩, 1), ?_⟩
        simp only [localFaceQAt, twoSelect_one, localFaceQ1,
          localFaceQ1Edge, localFaceQ1EdgeAt]
        congr 3
        apply congrArg (fun selected : SubdivisionEdge P x S =>
          (copy, selected))
        rw [subdivisionFaceBoundaryEdge_one_one]
        change subdivisionVerticalEdge P x S vertical.1
            ⟨vertical.2.1.1 + 1, by
              have := vertical.2.1.2
              omega⟩ vertical.2.2 = Sum.inr (Sum.inr vertical)
        simp only [subdivisionVerticalEdge]
        split <;> rename_i hzero
        · omega
        · split <;> rename_i hlast
          · have := vertical.2.1.2
            omega
          · congr 3
  · obtain ⟨⟨boundaryEdge, endpoint⟩, hendpoint⟩ :=
      subdivisionBoundaryIncidentEdge P
        A3.toTannerSquareAdmissibleV2 x S boundaryVertex
    refine ⟨(⟨x, Sum.inr boundaryEdge, (0, endpoint)⟩, 1), ?_⟩
    simp only [localFaceQAt, twoSelect_one, localFaceQ1,
      localFaceQ1Edge, localFaceQ1EdgeAt]
    congr 3
    fin_cases endpoint
    · change BDL26TannerLocalRegularity.edgeEndpoint
        (subdivisionBoundaryEdgeStart P x S)
        (subdivisionBoundaryEdgeEnd P x S) boundaryEdge 0 =
          boundaryVertex at hendpoint
      rw [BDL26TannerLocalRegularity.edgeEndpoint_zero] at hendpoint
      simpa [hendpoint] using doubleCylinderRectangleBoundaryEdge_one_zero
        P x S boundaryEdge
    · change BDL26TannerLocalRegularity.edgeEndpoint
        (subdivisionBoundaryEdgeStart P x S)
        (subdivisionBoundaryEdgeEnd P x S) boundaryEdge 1 =
          boundaryVertex at hendpoint
      rw [BDL26TannerLocalRegularity.edgeEndpoint_one] at hendpoint
      simpa [hendpoint] using doubleCylinderRectangleBoundaryEdge_one_one
        P x S boundaryEdge
theorem localFaceX_fixedCell_injective
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : DoubleCylinderFace P x S) :
    Function.Injective (fun corner : Two × Two =>
      localFaceX P S ⟨x, face, corner⟩) := by
  intro first second h
  rcases face with copyFace | rectangle
  · rcases copyFace with ⟨copy, smallFace⟩
    change (⟨x, (copy,
      subdivisionGridVertex P x S smallFace.1
        (gridEndpoint smallFace.2.1 first.1)
        (gridEndpoint smallFace.2.2 first.2))⟩ : RX0 P S) = _ at h
    injection h with _ hvertex
    have hgrid := congrArg Prod.snd hvertex
    change subdivisionGridVertex P x S smallFace.1
        (gridEndpoint smallFace.2.1 first.1)
        (gridEndpoint smallFace.2.2 first.2) =
      subdivisionGridVertex P x S smallFace.1
        (gridEndpoint smallFace.2.1 second.1)
        (gridEndpoint smallFace.2.2 second.2) at hgrid
    have hcoordinates := subdivisionGridVertex_fixedFace_injective
      P x S smallFace.1
      (show (fun ij => subdivisionGridVertex P x S smallFace.1 ij.1 ij.2)
          (gridEndpoint smallFace.2.1 first.1,
            gridEndpoint smallFace.2.2 first.2) =
        (fun ij => subdivisionGridVertex P x S smallFace.1 ij.1 ij.2)
          (gridEndpoint smallFace.2.1 second.1,
            gridEndpoint smallFace.2.2 second.2) from hgrid)
    have hcoordinatePair := Prod.mk.inj hcoordinates
    apply Prod.ext
    · exact gridEndpoint_injective smallFace.2.1 hcoordinatePair.1
    · exact gridEndpoint_injective smallFace.2.2 hcoordinatePair.2
  · change (⟨x, doubleCylinderRectangleCorner P x S rectangle first⟩ :
      RX0 P S) = _ at h
    injection h with _ hcorner
    exact doubleCylinderRectangleCorner_injective P x S rectangle hcorner
theorem localFaceQ_fixedFace_injective
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : DoubleCylinderFace P x S) (corner : Two × Two) :
    Function.Injective (fun bit : Two =>
      twoSelect
        (localFaceQ0 P S ⟨x, face, corner⟩)
        (localFaceQ1 P S ⟨x, face, corner⟩) bit) := by
  apply twoSelect_injective
  rcases face with copyFace | rectangle
  · intro h
    injection h with hsigma
    injection hsigma with _ hedge
    have hedge' := congrArg Prod.snd (Sum.inl.inj hedge)
    change subdivisionFaceBoundaryEdge P x S copyFace.2 (0, corner.2) =
      subdivisionFaceBoundaryEdge P x S copyFace.2 (1, corner.1) at hedge'
    have hslot := subdivisionFaceBoundaryEdge_injective P x S copyFace.2
      hedge'
    have : (0, corner.2) = ((1, corner.1) : Two × Two) := hslot
    exact (by norm_num at this)
  · intro h
    injection h with hsigma
    injection hsigma with _ hedge
    have hslot := doubleCylinderRectangleBoundaryEdge_injective P x S rectangle
      hedge
    have : (0, corner.1) = ((1, corner.2) : Two × Two) := hslot
    exact (by norm_num at this)
theorem localFaceX_eq_q0_endpoint
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : DoubleCylinderFace P x S) (corner : Two × Two) :
    ∃ endpoint : Two,
      localFaceX P S ⟨x, face, corner⟩ =
        ⟨x, edgeEndpoint (tannerDoubleCylinderEdgeStart P x S)
          (tannerDoubleCylinderEdgeEnd P x S)
          (localFaceQ0EdgeAt P x S face corner) endpoint⟩ := by
  rcases face with copyFace | rectangle
  · rcases copyFace with ⟨copy, smallFace⟩
    refine ⟨corner.1, ?_⟩
    rcases corner with ⟨first, second⟩
    fin_cases first <;> fin_cases second <;>
      simp [localFaceX, localFaceQ0EdgeAt, edgeEndpoint, gridEndpoint,
        tannerDoubleCylinderEdgeStart, tannerDoubleCylinderEdgeEnd,
        subdivisionHorizontalEdge_start, subdivisionHorizontalEdge_end]
    all_goals congr 3 <;> apply Fin.ext <;> rfl
  · refine ⟨corner.2, ?_⟩
    rcases corner with ⟨first, second⟩
    fin_cases first <;> fin_cases second <;>
      simp [localFaceX, localFaceQ0EdgeAt, edgeEndpoint,
        tannerDoubleCylinderEdgeStart, tannerDoubleCylinderEdgeEnd,
        doubleCylinderRectangleCorner]
theorem localFaceX_eq_q1_endpoint
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : DoubleCylinderFace P x S) (corner : Two × Two) :
    ∃ endpoint : Two,
      localFaceX P S ⟨x, face, corner⟩ =
        ⟨x, edgeEndpoint (tannerDoubleCylinderEdgeStart P x S)
          (tannerDoubleCylinderEdgeEnd P x S)
          (localFaceQ1EdgeAt P x S face corner) endpoint⟩ := by
  rcases face with copyFace | rectangle
  · rcases copyFace with ⟨copy, smallFace⟩
    refine ⟨corner.2, ?_⟩
    rcases corner with ⟨first, second⟩
    fin_cases first <;> fin_cases second <;>
      simp [localFaceX, localFaceQ1EdgeAt, edgeEndpoint, gridEndpoint,
        tannerDoubleCylinderEdgeStart, tannerDoubleCylinderEdgeEnd,
        subdivisionVerticalEdge_start, subdivisionVerticalEdge_end]
    all_goals congr 3 <;> apply Fin.ext <;> rfl
  · refine ⟨corner.1, ?_⟩
    rcases corner with ⟨first, second⟩
    fin_cases first <;> fin_cases second <;>
      simp [localFaceX, localFaceQ1EdgeAt, edgeEndpoint,
        tannerDoubleCylinderEdgeStart, tannerDoubleCylinderEdgeEnd,
        doubleCylinderRectangleCorner]
def localMaterialCornerAtEndpoint
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : DoubleCylinderFace P x S) (corner : Two × Two)
    (qCorner endpoint : Two) : Two × Two :=
  match face with
  | Sum.inl _ =>
      if qCorner = 0 then (endpoint, corner.2) else (corner.1, endpoint)
  | Sum.inr _ =>
      if qCorner = 0 then (corner.1, endpoint) else (endpoint, corner.2)
theorem localFaceQ_atEndpoint
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : DoubleCylinderFace P x S) (corner : Two × Two)
    (qCorner endpoint : Two) :
    twoSelect
        (localFaceQ0 P S ⟨x, face,
          localMaterialCornerAtEndpoint P x S face corner qCorner endpoint⟩)
        (localFaceQ1 P S ⟨x, face,
          localMaterialCornerAtEndpoint P x S face corner qCorner endpoint⟩)
        qCorner =
      twoSelect (localFaceQ0 P S ⟨x, face, corner⟩)
        (localFaceQ1 P S ⟨x, face, corner⟩) qCorner := by
  rcases face with copyFace | rectangle <;>
    fin_cases qCorner <;> fin_cases endpoint <;>
    simp [localMaterialCornerAtEndpoint, localFaceQ0,
      localFaceQ1, localFaceQ0Edge, localFaceQ1Edge,
      localFaceQ0EdgeAt, localFaceQ1EdgeAt]
theorem localFaceX_atEndpoint
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : DoubleCylinderFace P x S) (corner : Two × Two)
    (qCorner endpoint : Two) :
    localFaceX P S ⟨x, face,
      localMaterialCornerAtEndpoint P x S face corner qCorner endpoint⟩ =
      ⟨x, edgeEndpoint (tannerDoubleCylinderEdgeStart P x S)
        (tannerDoubleCylinderEdgeEnd P x S)
        (if qCorner = 0 then localFaceQ0EdgeAt P x S face corner
          else localFaceQ1EdgeAt P x S face corner) endpoint⟩ := by
  rcases face with copyFace | rectangle
  · rcases copyFace with ⟨copy, smallFace⟩
    rcases corner with ⟨first, second⟩
    fin_cases qCorner <;> fin_cases endpoint <;> fin_cases first <;>
      fin_cases second <;>
      simp [localFaceX, localMaterialCornerAtEndpoint,
        localFaceQ0EdgeAt, localFaceQ1EdgeAt, edgeEndpoint, gridEndpoint,
        tannerDoubleCylinderEdgeStart, tannerDoubleCylinderEdgeEnd,
        subdivisionHorizontalEdge_start, subdivisionHorizontalEdge_end,
        subdivisionVerticalEdge_start, subdivisionVerticalEdge_end]
    all_goals congr 3 <;> apply Fin.ext <;> rfl
  · rcases corner with ⟨first, second⟩
    fin_cases qCorner <;> fin_cases endpoint <;> fin_cases first <;>
      fin_cases second <;>
      simp [localFaceX, localMaterialCornerAtEndpoint,
        localFaceQ0EdgeAt, localFaceQ1EdgeAt, edgeEndpoint,
        tannerDoubleCylinderEdgeStart, tannerDoubleCylinderEdgeEnd,
        doubleCylinderRectangleCorner]
def qToXDoubleCylinderEdgeRaw
    (P : TannerSquarePresentation) (q : P.Q) (x : P.X)
    (hxq : P.xq x q = true) (S : OddScale) :
    QDoubleCylinderEdge P q S → DoubleCylinderEdge P x S
  | Sum.inl edge =>
      Sum.inl (edge.1, (qToXSubdivisionBoundaryEdge P q x hxq S edge.2).1)
  | Sum.inr endpoint =>
      Sum.inr (subdivisionOriginalBoundaryVertex P x S
        (xBoundaryEdgeEnd P x (qToXBoundaryEdge P q x hxq endpoint)))
def qToXBoundaryVertexAtRoot
    (P : TannerSquarePresentation) (q : P.Q) (x : P.X)
    (hxq : P.xq x q = true) (root : QStarEdge P q) :
    QStarVertex P q → XStarBoundaryVertex P x
  | Sum.inl _ => xBoundaryEdgeStart P x (qToXBoundaryEdge P q x hxq root)
  | Sum.inr edge => xBoundaryEdgeEnd P x (qToXBoundaryEdge P q x hxq edge)
def qToXSubdivisionVertexAtRoot
    (P : TannerSquarePresentation) (q : P.Q) (x : P.X)
    (hxq : P.xq x q = true) (S : OddScale) (root : QStarEdge P q) :
    QSubdivisionVertex P q S → SubdivisionVertex P x S
  | Sum.inl vertex =>
      Sum.inl (xStarBoundaryVertexToStar P x
        (qToXBoundaryVertexAtRoot P q x hxq root vertex))
  | Sum.inr edgeInterior =>
      Sum.inr (Sum.inl
        (xStarBoundaryEdgeToStar P x
          (qToXBoundaryEdge P q x hxq edgeInterior.1), edgeInterior.2))
theorem qToXSubdivisionEdgeAtRoot_start
    (P : TannerSquarePresentation) (q : P.Q) (x : P.X)
    (hxq : P.xq x q = true) (S : OddScale) (root : QStarEdge P q)
    (edge : QSubdivisionEdge P q S) :
    qToXSubdivisionVertexAtRoot P q x hxq S root
        (qSubdivisionEdgeStart P q S edge) =
      subdivisionEdgeStart P x S
        (qToXSubdivisionBoundaryEdge P q x hxq S edge).1 := by
  rcases edge with ⟨edge, index⟩
  by_cases hindex : index.1 = 0
  · simp [qSubdivisionEdgeStart, qToXSubdivisionVertexAtRoot,
      qToXSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge,
      subdivisionEdgeStart, subdivisionSegmentStart, hindex,
      qToXBoundaryVertexAtRoot]
    apply Subtype.ext
    rfl
  · simp [qSubdivisionEdgeStart, qToXSubdivisionVertexAtRoot,
      qToXSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge,
      subdivisionEdgeStart, subdivisionSegmentStart, hindex]
theorem qToXSubdivisionEdgeAtRoot_end
    (P : TannerSquarePresentation) (q : P.Q) (x : P.X)
    (hxq : P.xq x q = true) (S : OddScale) (root : QStarEdge P q)
    (edge : QSubdivisionEdge P q S) :
    qToXSubdivisionVertexAtRoot P q x hxq S root
        (qSubdivisionEdgeEnd P q S edge) =
      subdivisionEdgeEnd P x S
        (qToXSubdivisionBoundaryEdge P q x hxq S edge).1 := by
  rcases edge with ⟨edge, index⟩
  by_cases hindex : index.1 + 1 = S.half
  · simp [qSubdivisionEdgeEnd, qToXSubdivisionVertexAtRoot,
      qToXSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge,
      subdivisionEdgeEnd, subdivisionSegmentEnd, hindex,
      qToXBoundaryVertexAtRoot]
    apply Subtype.ext
    rfl
  · simp [qSubdivisionEdgeEnd, qToXSubdivisionVertexAtRoot,
      qToXSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge,
      subdivisionEdgeEnd, subdivisionSegmentEnd, hindex]
def qToXDoubleCylinderVertexAtRoot
    (P : TannerSquarePresentation) (q : P.Q) (x : P.X)
    (hxq : P.xq x q = true) (S : OddScale) (root : QStarEdge P q) :
    QDoubleCylinderVertex P q S → DoubleCylinderVertex P x S :=
  fun vertex =>
    (vertex.1, qToXSubdivisionVertexAtRoot P q x hxq S root vertex.2)
theorem qToXDoubleCylinderEdgeRaw_start
    (P : TannerSquarePresentation) (q : P.Q) (x : P.X)
    (hxq : P.xq x q = true) (S : OddScale) (root : QStarEdge P q)
    (edge : QDoubleCylinderEdge P q S) :
    qToXDoubleCylinderVertexAtRoot P q x hxq S root
        (qDoubleCylinderEdgeStart P q S edge) =
      tannerDoubleCylinderEdgeStart P x S
        (qToXDoubleCylinderEdgeRaw P q x hxq S edge) := by
  rcases edge with edge | endpoint
  · rcases edge with ⟨copy, edge⟩
    simp [qDoubleCylinderEdgeStart, qToXDoubleCylinderVertexAtRoot,
      qToXDoubleCylinderEdgeRaw, tannerDoubleCylinderEdgeStart,
      qToXSubdivisionEdgeAtRoot_start]
  · rfl
theorem qToXDoubleCylinderEdgeRaw_end
    (P : TannerSquarePresentation) (q : P.Q) (x : P.X)
    (hxq : P.xq x q = true) (S : OddScale) (root : QStarEdge P q)
    (edge : QDoubleCylinderEdge P q S) :
    qToXDoubleCylinderVertexAtRoot P q x hxq S root
        (qDoubleCylinderEdgeEnd P q S edge) =
      tannerDoubleCylinderEdgeEnd P x S
        (qToXDoubleCylinderEdgeRaw P q x hxq S edge) := by
  rcases edge with edge | endpoint
  · rcases edge with ⟨copy, edge⟩
    simp [qDoubleCylinderEdgeEnd, qToXDoubleCylinderVertexAtRoot,
      qToXDoubleCylinderEdgeRaw, tannerDoubleCylinderEdgeEnd,
      qToXSubdivisionEdgeAtRoot_end]
  · rfl
def qDoubleCylinderUnderlyingStarEdge
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale) :
    QDoubleCylinderEdge P q S → QStarEdge P q
  | Sum.inl edge => edge.2.1
  | Sum.inr edge => edge
theorem qToXDoubleCylinderEdgeRaw_endpoint_congr
    (P : TannerSquarePresentation) (q : P.Q) (x : P.X)
    (hxq : P.xq x q = true) (S : OddScale)
    (firstEdge secondEdge : QDoubleCylinderEdge P q S)
    (firstEndpoint secondEndpoint : Two)
    (hendpoint :
      edgeEndpoint (qDoubleCylinderEdgeStart P q S)
          (qDoubleCylinderEdgeEnd P q S) firstEdge firstEndpoint =
        edgeEndpoint (qDoubleCylinderEdgeStart P q S)
          (qDoubleCylinderEdgeEnd P q S) secondEdge secondEndpoint) :
    edgeEndpoint (tannerDoubleCylinderEdgeStart P x S)
        (tannerDoubleCylinderEdgeEnd P x S)
        (qToXDoubleCylinderEdgeRaw P q x hxq S firstEdge) firstEndpoint =
      edgeEndpoint (tannerDoubleCylinderEdgeStart P x S)
        (tannerDoubleCylinderEdgeEnd P x S)
        (qToXDoubleCylinderEdgeRaw P q x hxq S secondEdge) secondEndpoint := by
  let root := qDoubleCylinderUnderlyingStarEdge P q S firstEdge
  fin_cases firstEndpoint <;> fin_cases secondEndpoint
  · simpa [edgeEndpoint, twoSelect,
        ← qToXDoubleCylinderEdgeRaw_start P q x hxq S root firstEdge,
        ← qToXDoubleCylinderEdgeRaw_start P q x hxq S root secondEdge] using
      congrArg (qToXDoubleCylinderVertexAtRoot P q x hxq S root) hendpoint
  · simpa [edgeEndpoint, twoSelect,
        ← qToXDoubleCylinderEdgeRaw_start P q x hxq S root firstEdge,
        ← qToXDoubleCylinderEdgeRaw_end P q x hxq S root secondEdge] using
      congrArg (qToXDoubleCylinderVertexAtRoot P q x hxq S root) hendpoint
  · simpa [edgeEndpoint, twoSelect,
        ← qToXDoubleCylinderEdgeRaw_end P q x hxq S root firstEdge,
        ← qToXDoubleCylinderEdgeRaw_start P q x hxq S root secondEdge] using
      congrArg (qToXDoubleCylinderVertexAtRoot P q x hxq S root) hendpoint
  · simpa [edgeEndpoint, twoSelect,
        ← qToXDoubleCylinderEdgeRaw_end P q x hxq S root firstEdge,
        ← qToXDoubleCylinderEdgeRaw_end P q x hxq S root secondEdge] using
      congrArg (qToXDoubleCylinderVertexAtRoot P q x hxq S root) hendpoint
theorem qToXDoubleCylinderVertexAtRoot_oldZFace
    (P : TannerSquarePresentation) (S : OddScale)
    (face : P.Face) (corner copy : Two) (root : QStarEdge P (P.faceQ face corner)) :
    qToXDoubleCylinderVertexAtRoot P (P.faceQ face corner) (P.faceX face)
        (P.data.faceQ_xq face corner) S root
        (copy, Sum.inl (Sum.inr
          (⟨P.faceZ face, P.data.faceQ_qz face corner⟩ :
            QStarEdge P (P.faceQ face corner)))) =
      (copy, Sum.inl
        (xStarFaceZVertex P (P.faceX face) (oldFaceInXStar P face))) := by
  rfl
def glueFaceX (P : TannerSquarePresentation) (S : OddScale) :
    RXXQGlueFace P S → RX0 P S
  | ⟨a, edge, endpoint⟩ =>
      ⟨a.1.1,
        edgeEndpoint
          (tannerDoubleCylinderEdgeStart P a.1.1 S)
          (tannerDoubleCylinderEdgeEnd P a.1.1 S)
          (qToXDoubleCylinderEdgeRaw P a.1.2 a.1.1 a.2 S edge) endpoint⟩
def glueFaceQ0 (P : TannerSquarePresentation) (S : OddScale) :
    RXXQGlueFace P S → RX1 P S
  | ⟨a, edge, _⟩ =>
      Sum.inl ⟨a.1.1,
        qToXDoubleCylinderEdgeRaw P a.1.2 a.1.1 a.2 S edge⟩
def glueFaceQ1 (P : TannerSquarePresentation) (S : OddScale) :
    RXXQGlueFace P S → RX1 P S
  | ⟨a, edge, endpoint⟩ =>
      Sum.inr ⟨a.1.2,
        edgeEndpoint (qDoubleCylinderEdgeStart P a.1.2 S)
          (qDoubleCylinderEdgeEnd P a.1.2 S) edge endpoint⟩
def glueFaceZ (P : TannerSquarePresentation) (S : OddScale) :
    RXXQGlueFace P S → RX2 P S
  | ⟨a, edge, _⟩ => Sum.inl (Sum.inr ⟨a.1.2, edge⟩)
def oldZFaceX (P : TannerSquarePresentation) (S : OddScale) :
    RXOldZFace P → RX0 P S
  | (face, copy) =>
      ⟨P.faceX face,
        (copy, Sum.inl
          (xStarFaceZVertex P (P.faceX face) (oldFaceInXStar P face)))⟩
theorem qToXDoubleCylinderEdgeRaw_endpoint_eq_oldZFaceX
    (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (q : P.Q) (z : P.Z)
    (hxq : P.xq x q = true) (hqz : P.qz q z = true)
    (edge : QDoubleCylinderEdge P q S) (endpoint : Two)
    (face : P.Face) (corner copy : Two)
    (hfaceX : P.faceX face = x) (hfaceZ : P.faceZ face = z)
    (hfaceQ : P.faceQ face corner = q)
    (hvertex :
      edgeEndpoint (qDoubleCylinderEdgeStart P q S)
          (qDoubleCylinderEdgeEnd P q S) edge endpoint =
        (copy, Sum.inl (Sum.inr (⟨z, hqz⟩ : QStarEdge P q)))) :
    (⟨x, edgeEndpoint (tannerDoubleCylinderEdgeStart P x S)
        (tannerDoubleCylinderEdgeEnd P x S)
        (qToXDoubleCylinderEdgeRaw P q x hxq S edge) endpoint⟩ : RX0 P S) =
      oldZFaceX P S (face, copy) := by
  subst x
  subst z
  subst q
  let root := qDoubleCylinderUnderlyingStarEdge P (P.faceQ face corner) S edge
  have himage :
      edgeEndpoint (tannerDoubleCylinderEdgeStart P (P.faceX face) S)
          (tannerDoubleCylinderEdgeEnd P (P.faceX face) S)
          (qToXDoubleCylinderEdgeRaw P (P.faceQ face corner)
            (P.faceX face) hxq S edge) endpoint =
        (copy, Sum.inl (xStarFaceZVertex P (P.faceX face)
          (oldFaceInXStar P face))) := by
    fin_cases endpoint
    · simpa [edgeEndpoint, twoSelect,
          ← qToXDoubleCylinderEdgeRaw_start P (P.faceQ face corner)
            (P.faceX face) hxq S root edge,
          qToXDoubleCylinderVertexAtRoot_oldZFace] using
        congrArg (qToXDoubleCylinderVertexAtRoot P
          (P.faceQ face corner) (P.faceX face) hxq S root) hvertex
    · simpa [edgeEndpoint, twoSelect,
          ← qToXDoubleCylinderEdgeRaw_end P (P.faceQ face corner)
            (P.faceX face) hxq S root edge,
          qToXDoubleCylinderVertexAtRoot_oldZFace] using
        congrArg (qToXDoubleCylinderVertexAtRoot P
          (P.faceQ face corner) (P.faceX face) hxq S root) hvertex
  exact congrArg (fun target => (⟨P.faceX face, target⟩ : RX0 P S)) himage
def oldZFaceZ (P : TannerSquarePresentation) (S : OddScale) :
    RXOldZFace P → RX2 P S
  | (face, copy) => Sum.inr (P.faceZ face, copy)
def oldZFaceQ (P : TannerSquarePresentation) (S : OddScale)
    (corner : Two) : RXOldZFace P → RX1 P S
  | (face, copy) =>
      Sum.inr ⟨P.faceQ face corner,
        (copy, Sum.inl (Sum.inr
          (⟨P.faceZ face, P.data.faceQ_qz face corner⟩ :
            QStarEdge P (P.faceQ face corner))))⟩
theorem oldZFaceX_congr (P : TannerSquarePresentation) (S : OddScale)
    (firstFace secondFace : P.Face) (copy : Two)
    (hx : P.faceX firstFace = P.faceX secondFace)
    (hz : P.faceZ firstFace = P.faceZ secondFace) :
    oldZFaceX P S (firstFace, copy) = oldZFaceX P S (secondFace, copy) := by
  simp only [oldZFaceX, xStarFaceZVertex, oldFaceInXStar]
  rw [Sigma.ext_iff]
  refine ⟨hx, ?_⟩
  congr 5
  · exact congrArg (fun x => XStarEdge P x × Fin (S.half - 1)) hx
  · exact congrArg (fun x =>
      XStarFace P x × Fin (S.half - 1) × Fin (S.half - 1)) hx
  · exact congrArg (fun x => fun v => xStarVertexMember P x v = true) hx
  · exact congrArg Vertex.z hz
  · exact proof_irrel_heq _ _
theorem oldZFaceQ_congr (P : TannerSquarePresentation) (S : OddScale)
    (firstFace secondFace : P.Face) (firstCorner secondCorner copy : Two)
    (hq : P.faceQ firstFace firstCorner = P.faceQ secondFace secondCorner)
    (hz : P.faceZ firstFace = P.faceZ secondFace) :
    oldZFaceQ P S firstCorner (firstFace, copy) =
      oldZFaceQ P S secondCorner (secondFace, copy) := by
  simp only [oldZFaceQ]
  apply congrArg Sum.inr
  rw [Sigma.ext_iff]
  refine ⟨hq, ?_⟩
  congr 6
  · exact congrArg (fun q => fun z => P.qz q z = true) hq
  · exact congrArg (fun q => fun z => P.qz q z = true) hq
  · exact proof_irrel_heq _ _
noncomputable def rxFaceX (P : TannerSquarePresentation) (S : OddScale) :
    RXFace P S → RX0 P S
  | Sum.inl face => localFaceX P S face
  | Sum.inr (Sum.inl face) => glueFaceX P S face
  | Sum.inr (Sum.inr face) => oldZFaceX P S face
def rxFaceZ (P : TannerSquarePresentation) (S : OddScale) :
    RXFace P S → RX2 P S
  | Sum.inl face => localFaceZ P S face
  | Sum.inr (Sum.inl face) => glueFaceZ P S face
  | Sum.inr (Sum.inr face) => oldZFaceZ P S face
noncomputable def rxFaceQ (P : TannerSquarePresentation) (S : OddScale) :
    RXFace P S → Two → RX1 P S
  | Sum.inl face => fun corner =>
      twoSelect (localFaceQ0 P S face) (localFaceQ1 P S face) corner
  | Sum.inr (Sum.inl face) => fun corner =>
      twoSelect (glueFaceQ0 P S face) (glueFaceQ1 P S face) corner
  | Sum.inr (Sum.inr face) => fun corner => oldZFaceQ P S corner face
theorem rxFaceQ_injective (P : TannerSquarePresentation) (S : OddScale)
    (face : RXFace P S) :
    Function.Injective (rxFaceQ P S face) := by
  rcases face with localFace | glue | old
  · rcases localFace with ⟨x, face, corner⟩
    exact localFaceQ_fixedFace_injective P x S face corner
  · apply twoSelect_injective
    intro h
    cases h
  · intro first second h
    rcases old with ⟨face, copy⟩
    have hq : P.faceQ face first = P.faceQ face second := by
      exact congrArg (fun coordinate : RX1 P S =>
        match coordinate with
        | Sum.inl _ => P.faceQ face first
        | Sum.inr qVertex => qVertex.1) h
    exact P.faceQ_injective face hq
theorem rxFaceX_eq_endpoint_of_faceQ_eq_xEdge
    (P : TannerSquarePresentation) (S : OddScale)
    (face : RXFace P S) (corner : Two)
    (x : P.X) (edge : DoubleCylinderEdge P x S)
    (hq : rxFaceQ P S face corner = Sum.inl ⟨x, edge⟩) :
    ∃ endpoint : Two,
      rxFaceX P S face =
        ⟨x, edgeEndpoint (tannerDoubleCylinderEdgeStart P x S)
          (tannerDoubleCylinderEdgeEnd P x S) edge endpoint⟩ := by
  rcases face with localFace | glue | old
  · rcases localFace with ⟨localX, localCell, materialCorner⟩
    fin_cases corner
    · have hedge : localFaceQ0Edge P S
          ⟨localX, localCell, materialCorner⟩ = ⟨x, edge⟩ :=
        Sum.inl.inj hq
      rcases localFaceX_eq_q0_endpoint P localX S localCell materialCorner with
        ⟨endpoint, hendpoint⟩
      cases hedge
      exact ⟨endpoint, hendpoint⟩
    · have hedge : localFaceQ1Edge P S
          ⟨localX, localCell, materialCorner⟩ = ⟨x, edge⟩ :=
        Sum.inl.inj hq
      rcases localFaceX_eq_q1_endpoint P localX S localCell materialCorner with
        ⟨endpoint, hendpoint⟩
      cases hedge
      exact ⟨endpoint, hendpoint⟩
  · rcases glue with ⟨a, qEdge, endpoint⟩
    fin_cases corner
    · have hedge : (⟨a.1.1,
          qToXDoubleCylinderEdgeRaw P a.1.2 a.1.1 a.2 S qEdge⟩ :
            Σ x : P.X, DoubleCylinderEdge P x S) = ⟨x, edge⟩ :=
        Sum.inl.inj hq
      cases hedge
      exact ⟨endpoint, rfl⟩
    · cases hq
  · cases hq
theorem exists_rxFaceCorner_of_xEdge_witnesses
    (P : TannerSquarePresentation) (S : OddScale)
    (xCoordinate : RX0 P S) (zCoordinate : RX2 P S)
    (x : P.X) (edge : DoubleCylinderEdge P x S)
    (firstFace secondFace : RXFace P S)
    (firstCorner secondCorner : Two)
    (hfirstX : rxFaceX P S firstFace = xCoordinate)
    (hfirstQ : rxFaceQ P S firstFace firstCorner = Sum.inl ⟨x, edge⟩)
    (hsecondQ : rxFaceQ P S secondFace secondCorner = Sum.inl ⟨x, edge⟩)
    (hsecondZ : rxFaceZ P S secondFace = zCoordinate) :
    ∃ face : RXFace P S, ∃ corner : Two,
      rxFaceX P S face = xCoordinate ∧
        rxFaceQ P S face corner = Sum.inl ⟨x, edge⟩ ∧
          rxFaceZ P S face = zCoordinate := by
  rcases rxFaceX_eq_endpoint_of_faceQ_eq_xEdge P S firstFace firstCorner
      x edge hfirstQ with ⟨endpoint, hfirstEndpoint⟩
  rcases secondFace with localFace | glue | old
  · rcases localFace with ⟨localX, localCell, materialCorner⟩
    fin_cases secondCorner
    · have hedge : localFaceQ0Edge P S
          ⟨localX, localCell, materialCorner⟩ = ⟨x, edge⟩ := by
        simpa [rxFaceQ] using Sum.inl.inj hsecondQ
      cases hedge
      let newMaterial := localMaterialCornerAtEndpoint P x S localCell
        materialCorner 0 endpoint
      let newFace : RXFace P S :=
        Sum.inl ⟨x, localCell, newMaterial⟩
      refine ⟨newFace, 0, ?_, ?_, ?_⟩
      · rw [hfirstX.symm, hfirstEndpoint]
        simpa [newFace, newMaterial, rxFaceX] using
          localFaceX_atEndpoint P x S localCell materialCorner 0 endpoint
      · calc
          rxFaceQ P S newFace 0 =
              rxFaceQ P S (Sum.inl ⟨x, localCell, materialCorner⟩) 0 := by
            simpa [rxFaceQ, newFace, newMaterial] using
              localFaceQ_atEndpoint P x S localCell materialCorner 0 endpoint
          _ = Sum.inl ⟨x, localFaceQ0EdgeAt P x S localCell
                materialCorner⟩ := hsecondQ
      · simpa [newFace, rxFaceZ, localFaceZ] using hsecondZ
    · have hedge : localFaceQ1Edge P S
          ⟨localX, localCell, materialCorner⟩ = ⟨x, edge⟩ := by
        simpa [rxFaceQ] using Sum.inl.inj hsecondQ
      cases hedge
      let newMaterial := localMaterialCornerAtEndpoint P x S localCell
        materialCorner 1 endpoint
      let newFace : RXFace P S :=
        Sum.inl ⟨x, localCell, newMaterial⟩
      refine ⟨newFace, 1, ?_, ?_, ?_⟩
      · rw [hfirstX.symm, hfirstEndpoint]
        simpa [newFace, newMaterial, rxFaceX] using
          localFaceX_atEndpoint P x S localCell materialCorner 1 endpoint
      · calc
          rxFaceQ P S newFace 1 =
              rxFaceQ P S (Sum.inl ⟨x, localCell, materialCorner⟩) 1 := by
            simpa [rxFaceQ, newFace, newMaterial] using
              localFaceQ_atEndpoint P x S localCell materialCorner 1 endpoint
          _ = Sum.inl ⟨x, localFaceQ1EdgeAt P x S localCell
                materialCorner⟩ := hsecondQ
      · simpa [newFace, rxFaceZ, localFaceZ] using hsecondZ
  · rcases glue with ⟨a, qEdge, secondEndpoint⟩
    fin_cases secondCorner
    · have hedge : (⟨a.1.1,
          qToXDoubleCylinderEdgeRaw P a.1.2 a.1.1 a.2 S qEdge⟩ :
            Σ x : P.X, DoubleCylinderEdge P x S) = ⟨x, edge⟩ :=
        Sum.inl.inj hsecondQ
      have hax : a.1.1 = x := congrArg Sigma.fst hedge
      subst x
      have hedge' :
          qToXDoubleCylinderEdgeRaw P a.1.2 a.1.1 a.2 S qEdge = edge :=
        eq_of_heq (Sigma.mk.inj_iff.mp hedge).2
      subst edge
      refine ⟨Sum.inr (Sum.inl ⟨a, qEdge, endpoint⟩), 0, ?_, rfl, ?_⟩
      · simpa [rxFaceX, glueFaceX] using
          hfirstEndpoint.symm.trans hfirstX
      · exact hsecondZ
    · cases hsecondQ
  · cases hsecondQ
theorem exists_rxFaceCorner_of_glue_glue_witnesses
    (P : TannerSquarePresentation) (S : OddScale)
    (xCoordinate : RX0 P S) (zCoordinate : RX2 P S)
    (q : P.Q) (vertex : QDoubleCylinderVertex P q S)
    (firstGlue secondGlue : RXXQGlueFace P S)
    (firstCorner secondCorner : Two)
    (hfirstX : rxFaceX P S (Sum.inr (Sum.inl firstGlue)) = xCoordinate)
    (hfirstQ : rxFaceQ P S (Sum.inr (Sum.inl firstGlue)) firstCorner =
      Sum.inr ⟨q, vertex⟩)
    (hsecondQ : rxFaceQ P S (Sum.inr (Sum.inl secondGlue)) secondCorner =
      Sum.inr ⟨q, vertex⟩)
    (hsecondZ : rxFaceZ P S (Sum.inr (Sum.inl secondGlue)) = zCoordinate) :
    ∃ face : RXFace P S, ∃ corner : Two,
      rxFaceX P S face = xCoordinate ∧
        rxFaceQ P S face corner = Sum.inr ⟨q, vertex⟩ ∧
          rxFaceZ P S face = zCoordinate := by
  rcases firstGlue with ⟨⟨⟨firstX, firstQ⟩, firstHXQ⟩,
    firstEdge, firstEndpoint⟩
  rcases secondGlue with ⟨⟨⟨secondX, secondQ⟩, secondHXQ⟩,
    secondEdge, secondEndpoint⟩
  fin_cases firstCorner
  · cases hfirstQ
  fin_cases secondCorner
  · cases hsecondQ
  have hfirstTag :
      (⟨firstQ, edgeEndpoint (qDoubleCylinderEdgeStart P firstQ S)
        (qDoubleCylinderEdgeEnd P firstQ S) firstEdge firstEndpoint⟩ :
          Σ q : P.Q, QDoubleCylinderVertex P q S) = ⟨q, vertex⟩ :=
    Sum.inr.inj hfirstQ
  have hsecondTag :
      (⟨secondQ, edgeEndpoint (qDoubleCylinderEdgeStart P secondQ S)
        (qDoubleCylinderEdgeEnd P secondQ S) secondEdge secondEndpoint⟩ :
          Σ q : P.Q, QDoubleCylinderVertex P q S) = ⟨q, vertex⟩ :=
    Sum.inr.inj hsecondQ
  have hfirstBase : firstQ = q := congrArg Sigma.fst hfirstTag
  have hsecondBase : secondQ = q := congrArg Sigma.fst hsecondTag
  subst firstQ
  subst secondQ
  have hfirstVertex :
      edgeEndpoint (qDoubleCylinderEdgeStart P q S)
        (qDoubleCylinderEdgeEnd P q S) firstEdge firstEndpoint = vertex :=
    eq_of_heq (Sigma.mk.inj_iff.mp hfirstTag).2
  have hsecondVertex :
      edgeEndpoint (qDoubleCylinderEdgeStart P q S)
        (qDoubleCylinderEdgeEnd P q S) secondEdge secondEndpoint = vertex :=
    eq_of_heq (Sigma.mk.inj_iff.mp hsecondTag).2
  let owner : XQEdge P := ⟨(firstX, q), firstHXQ⟩
  let candidate : RXFace P S :=
    Sum.inr (Sum.inl ⟨owner, secondEdge, secondEndpoint⟩)
  refine ⟨candidate, 1, ?_, ?_, ?_⟩
  · rw [hfirstX.symm]
    have hendpoint := qToXDoubleCylinderEdgeRaw_endpoint_congr P q firstX
      firstHXQ S secondEdge firstEdge secondEndpoint firstEndpoint
      (hsecondVertex.trans hfirstVertex.symm)
    simpa [candidate, owner, rxFaceX, glueFaceX] using
      congrArg (fun target => (⟨firstX, target⟩ : RX0 P S)) hendpoint
  · exact hsecondQ
  · exact hsecondZ
theorem exists_rxFaceCorner_of_qVertex_witnesses
    (P : TannerSquarePresentation) (S : OddScale)
    (xCoordinate : RX0 P S) (zCoordinate : RX2 P S)
    (q : P.Q) (vertex : QDoubleCylinderVertex P q S)
    (firstFace secondFace : RXFace P S)
    (firstCorner secondCorner : Two)
    (hfirstX : rxFaceX P S firstFace = xCoordinate)
    (hfirstQ : rxFaceQ P S firstFace firstCorner = Sum.inr ⟨q, vertex⟩)
    (hsecondQ : rxFaceQ P S secondFace secondCorner = Sum.inr ⟨q, vertex⟩)
    (hsecondZ : rxFaceZ P S secondFace = zCoordinate) :
    ∃ face : RXFace P S, ∃ corner : Two,
      rxFaceX P S face = xCoordinate ∧
        rxFaceQ P S face corner = Sum.inr ⟨q, vertex⟩ ∧
          rxFaceZ P S face = zCoordinate := by
  rcases firstFace with firstLocal | firstGlue | firstOld
  · fin_cases firstCorner <;> cases hfirstQ
  · rcases secondFace with secondLocal | secondGlue | secondOld
    · fin_cases secondCorner <;> cases hsecondQ
    · exact exists_rxFaceCorner_of_glue_glue_witnesses P S
        xCoordinate zCoordinate q vertex firstGlue secondGlue
        firstCorner secondCorner hfirstX hfirstQ hsecondQ hsecondZ
    · rcases firstGlue with ⟨⟨⟨firstX, firstQ⟩, firstHXQ⟩,
        firstEdge, firstEndpoint⟩
      rcases secondOld with ⟨secondOldFace, secondCopy⟩
      fin_cases firstCorner
      · cases hfirstQ
      have hfirstTag :
          (⟨firstQ, edgeEndpoint (qDoubleCylinderEdgeStart P firstQ S)
            (qDoubleCylinderEdgeEnd P firstQ S) firstEdge firstEndpoint⟩ :
              Σ q : P.Q, QDoubleCylinderVertex P q S) = ⟨q, vertex⟩ :=
        Sum.inr.inj hfirstQ
      have hsecondTag :
          (⟨P.faceQ secondOldFace secondCorner,
            (secondCopy, Sum.inl (Sum.inr
              (⟨P.faceZ secondOldFace,
                P.data.faceQ_qz secondOldFace secondCorner⟩ :
                  QStarEdge P (P.faceQ secondOldFace secondCorner))))⟩ :
              Σ q : P.Q, QDoubleCylinderVertex P q S) = ⟨q, vertex⟩ :=
        Sum.inr.inj hsecondQ
      have hfirstBase : firstQ = q := congrArg Sigma.fst hfirstTag
      have hsecondBase : P.faceQ secondOldFace secondCorner = q :=
        congrArg Sigma.fst hsecondTag
      subst firstQ
      let sharedOld : SharedQ P.data firstX (P.faceZ secondOldFace) :=
        ⟨q, by
          simpa [firstHXQ, hsecondBase] using
            And.intro firstHXQ (P.data.faceQ_qz secondOldFace secondCorner)⟩
      obtain ⟨newCorner, hnewCorner⟩ :=
        (P.perfectPairing firstX (P.faceZ secondOldFace)).2 sharedOld
      rcases newCorner with ⟨newFace, newBit⟩
      have hnewQ : P.faceQ newFace.1 newBit = q :=
        congrArg Subtype.val hnewCorner
      let candidate : RXFace P S :=
        Sum.inr (Sum.inr (newFace.1, secondCopy))
      refine ⟨candidate, newBit, ?_, ?_, ?_⟩
      · rw [hfirstX.symm]
        have hvertices := (Sigma.mk.inj_iff.mp
          (hfirstTag.trans hsecondTag.symm)).2
        have hbridge := qToXDoubleCylinderEdgeRaw_endpoint_eq_oldZFaceX P S
          firstX q (P.faceZ secondOldFace) firstHXQ
          (by simpa [hsecondBase] using
            P.data.faceQ_qz secondOldFace secondCorner)
          firstEdge firstEndpoint newFace.1 newBit secondCopy
          newFace.2.1 newFace.2.2 hnewQ
          (by
            cases hsecondBase
            exact eq_of_heq hvertices)
        simpa [candidate, rxFaceX, glueFaceX] using hbridge.symm
      · exact (oldZFaceQ_congr P S newFace.1 secondOldFace
          newBit secondCorner secondCopy (hnewQ.trans hsecondBase.symm)
          newFace.2.2).trans hsecondQ
      · simpa [candidate, rxFaceZ, oldZFaceZ, newFace.2.2] using hsecondZ
  · rcases firstOld with ⟨firstOldFace, firstCopy⟩
    rcases secondFace with secondLocal | secondGlue | secondOld
    · fin_cases secondCorner <;> cases hsecondQ
    · rcases secondGlue with ⟨⟨⟨secondX, secondQ⟩, secondHXQ⟩,
          secondEdge, secondEndpoint⟩
      fin_cases secondCorner
      · cases hsecondQ
      have hfirstTag :
          (⟨P.faceQ firstOldFace firstCorner,
            (firstCopy, Sum.inl (Sum.inr
              (⟨P.faceZ firstOldFace,
                P.data.faceQ_qz firstOldFace firstCorner⟩ :
                  QStarEdge P (P.faceQ firstOldFace firstCorner))))⟩ :
              Σ q : P.Q, QDoubleCylinderVertex P q S) = ⟨q, vertex⟩ :=
        Sum.inr.inj hfirstQ
      have hsecondTag :
          (⟨secondQ, edgeEndpoint (qDoubleCylinderEdgeStart P secondQ S)
            (qDoubleCylinderEdgeEnd P secondQ S) secondEdge secondEndpoint⟩ :
              Σ q : P.Q, QDoubleCylinderVertex P q S) = ⟨q, vertex⟩ :=
        Sum.inr.inj hsecondQ
      have hfirstBase : P.faceQ firstOldFace firstCorner = q :=
        congrArg Sigma.fst hfirstTag
      have hsecondBase : secondQ = q := congrArg Sigma.fst hsecondTag
      subst secondQ
      let owner : XQEdge P := ⟨(P.faceX firstOldFace, q), by
        simpa [hfirstBase] using P.data.faceQ_xq firstOldFace firstCorner⟩
      let candidate : RXFace P S :=
        Sum.inr (Sum.inl ⟨owner, secondEdge, secondEndpoint⟩)
      refine ⟨candidate, 1, ?_, ?_, ?_⟩
      · rw [hfirstX.symm]
        have hvertices := (Sigma.mk.inj_iff.mp
          (hsecondTag.trans hfirstTag.symm)).2
        have hbridge := qToXDoubleCylinderEdgeRaw_endpoint_eq_oldZFaceX P S
          (P.faceX firstOldFace) q (P.faceZ firstOldFace)
          owner.2 (by simpa [hfirstBase] using
            P.data.faceQ_qz firstOldFace firstCorner)
          secondEdge secondEndpoint firstOldFace firstCorner firstCopy
          rfl rfl hfirstBase
          (by
            cases hfirstBase
            exact eq_of_heq hvertices)
        simpa [candidate, owner, rxFaceX, glueFaceX] using hbridge
      · simpa [candidate, owner, rxFaceQ, glueFaceQ1] using hsecondQ
      · simpa [candidate, owner, rxFaceZ, glueFaceZ] using hsecondZ
    · rcases secondOld with ⟨secondOldFace, secondCopy⟩
      have hfirstTag := Sum.inr.inj hfirstQ
      have hsecondTag := Sum.inr.inj hsecondQ
      have hfirstBase : P.faceQ firstOldFace firstCorner = q :=
        congrArg Sigma.fst hfirstTag
      have hsecondBase : P.faceQ secondOldFace secondCorner = q :=
        congrArg Sigma.fst hsecondTag
      have hcopy : firstCopy = secondCopy := by
        have htags := congrArg (fun tagged : Σ q : P.Q,
            QDoubleCylinderVertex P q S => tagged.2.1) hfirstTag
        have htags' := congrArg (fun tagged : Σ q : P.Q,
            QDoubleCylinderVertex P q S => tagged.2.1) hsecondTag
        exact htags.trans htags'.symm
      let terminalZ : (Σ q : P.Q, QDoubleCylinderVertex P q S) → P.Z :=
        fun tagged => match tagged.2.2 with
          | Sum.inl (Sum.inr edge) => edge.1
          | _ => P.faceZ firstOldFace
      have hzOld : P.faceZ firstOldFace = P.faceZ secondOldFace := by
        have hzFirst := congrArg terminalZ hfirstTag
        have hzSecond := congrArg terminalZ hsecondTag
        exact hzFirst.trans hzSecond.symm
      subst secondCopy
      let sharedOld : SharedQ P.data (P.faceX firstOldFace)
          (P.faceZ secondOldFace) :=
        ⟨q, by
          simpa [hfirstBase, hsecondBase] using And.intro
            (P.data.faceQ_xq firstOldFace firstCorner)
            (P.data.faceQ_qz secondOldFace secondCorner)⟩
      obtain ⟨newCorner, hnewCorner⟩ :=
        (P.perfectPairing (P.faceX firstOldFace)
          (P.faceZ secondOldFace)).2 sharedOld
      rcases newCorner with ⟨newFace, newBit⟩
      have hnewQ : P.faceQ newFace.1 newBit = q :=
        congrArg Subtype.val hnewCorner
      let candidate : RXFace P S := Sum.inr (Sum.inr (newFace.1, firstCopy))
      refine ⟨candidate, newBit, ?_, ?_, ?_⟩
      · rw [hfirstX.symm]
        exact oldZFaceX_congr P S newFace.1 firstOldFace firstCopy
          newFace.2.1 (newFace.2.2.trans hzOld.symm)
      · exact (oldZFaceQ_congr P S newFace.1 secondOldFace
          newBit secondCorner firstCopy (hnewQ.trans hsecondBase.symm)
          newFace.2.2).trans hsecondQ
      · simpa [candidate, rxFaceZ, oldZFaceZ, newFace.2.2] using hsecondZ
theorem rxFaceCorner_unique
    (P : TannerSquarePresentation) (S : OddScale)
    (firstFace secondFace : RXFace P S) (firstCorner secondCorner : Two)
    (hx : rxFaceX P S firstFace = rxFaceX P S secondFace)
    (hz : rxFaceZ P S firstFace = rxFaceZ P S secondFace)
    (hq : rxFaceQ P S firstFace firstCorner =
      rxFaceQ P S secondFace secondCorner) :
    firstFace = secondFace ∧ firstCorner = secondCorner := by
  rcases firstFace with firstLocal | firstGlue | firstOld <;>
    rcases secondFace with secondLocal | secondGlue | secondOld
  · rcases firstLocal with ⟨firstX, firstCell, firstMaterialCorner⟩
    rcases secondLocal with ⟨secondX, secondCell, secondMaterialCorner⟩
    change (Sum.inl (Sum.inl (⟨firstX, firstCell⟩ :
      Σ x : P.X, DoubleCylinderFace P x S)) : RX2 P S) =
      Sum.inl (Sum.inl (⟨secondX, secondCell⟩ :
        Σ x : P.X, DoubleCylinderFace P x S)) at hz
    have hcell : (⟨firstX, firstCell⟩ :
        Σ x : P.X, DoubleCylinderFace P x S) = ⟨secondX, secondCell⟩ :=
      Sum.inl.inj (Sum.inl.inj hz)
    cases hcell
    have hmaterial : firstMaterialCorner = secondMaterialCorner :=
      localFaceX_fixedCell_injective P firstX S firstCell hx
    cases hmaterial
    have hface :
        (Sum.inl ⟨firstX, firstCell, firstMaterialCorner⟩ : RXFace P S) =
          Sum.inl ⟨firstX, firstCell, firstMaterialCorner⟩ := rfl
    refine ⟨hface, ?_⟩
    exact rxFaceQ_injective P S
      (Sum.inl ⟨firstX, firstCell, firstMaterialCorner⟩) hq
  · cases hz
  · cases hz
  · cases hz
  · rcases firstGlue with ⟨firstA, firstEdge, firstEndpoint⟩
    rcases secondGlue with ⟨secondA, secondEdge, secondEndpoint⟩
    change (Sum.inl (Sum.inr (⟨firstA.1.2, firstEdge⟩ :
      Σ q : P.Q, QDoubleCylinderEdge P q S)) : RX2 P S) =
      Sum.inl (Sum.inr (⟨secondA.1.2, secondEdge⟩ :
        Σ q : P.Q, QDoubleCylinderEdge P q S)) at hz
    have hqedge : (⟨firstA.1.2, firstEdge⟩ :
        Σ q : P.Q, QDoubleCylinderEdge P q S) =
      ⟨secondA.1.2, secondEdge⟩ := Sum.inr.inj (Sum.inl.inj hz)
    have hqbase : firstA.1.2 = secondA.1.2 :=
      congrArg Sigma.fst hqedge
    have hxold : firstA.1.1 = secondA.1.1 := congrArg Sigma.fst hx
    have ha : firstA = secondA := by
      apply Subtype.ext
      exact Prod.ext hxold hqbase
    subst secondA
    have hedge : firstEdge = secondEdge := by
      exact eq_of_heq (Sigma.mk.inj_iff.mp hqedge).2
    subst secondEdge
    change (⟨firstA.1.1,
      edgeEndpoint (tannerDoubleCylinderEdgeStart P firstA.1.1 S)
        (tannerDoubleCylinderEdgeEnd P firstA.1.1 S)
        (qToXDoubleCylinderEdgeRaw P firstA.1.2 firstA.1.1 firstA.2 S firstEdge)
        firstEndpoint⟩ : RX0 P S) =
      ⟨firstA.1.1,
        edgeEndpoint (tannerDoubleCylinderEdgeStart P firstA.1.1 S)
          (tannerDoubleCylinderEdgeEnd P firstA.1.1 S)
          (qToXDoubleCylinderEdgeRaw P firstA.1.2 firstA.1.1 firstA.2 S firstEdge)
          secondEndpoint⟩ at hx
    injection hx with _ hvertex
    have hendpoint : firstEndpoint = secondEndpoint := by
      apply twoSelect_injective
        (tannerDoubleCylinderEdgeStart_ne_end P firstA.1.1 S
          (qToXDoubleCylinderEdgeRaw P firstA.1.2 firstA.1.1 firstA.2 S
            firstEdge))
      exact hvertex
    subst secondEndpoint
    have hface :
        (Sum.inr (Sum.inl ⟨firstA, firstEdge, firstEndpoint⟩) : RXFace P S) =
          Sum.inr (Sum.inl ⟨firstA, firstEdge, firstEndpoint⟩) := rfl
    refine ⟨hface, ?_⟩
    exact rxFaceQ_injective P S
      (Sum.inr (Sum.inl ⟨firstA, firstEdge, firstEndpoint⟩)) hq
  · cases hz
  · cases hz
  · cases hz
  · rcases firstOld with ⟨firstFace, firstCopy⟩
    rcases secondOld with ⟨secondFace, secondCopy⟩
    change Sum.inr (P.faceZ firstFace, firstCopy) =
      Sum.inr (P.faceZ secondFace, secondCopy) at hz
    have hzpair : (P.faceZ firstFace, firstCopy) =
        (P.faceZ secondFace, secondCopy) := Sum.inr.inj hz
    have hcopy : firstCopy = secondCopy := congrArg Prod.snd hzpair
    subst secondCopy
    change (⟨P.faceX firstFace,
      (firstCopy, Sum.inl
        (xStarFaceZVertex P (P.faceX firstFace)
          (oldFaceInXStar P firstFace)))⟩ : RX0 P S) = _ at hx
    have hxold : P.faceX firstFace = P.faceX secondFace :=
      congrArg Sigma.fst hx
    have hzold : P.faceZ firstFace = P.faceZ secondFace :=
      congrArg Prod.fst hzpair
    have hqold : P.faceQ firstFace firstCorner =
        P.faceQ secondFace secondCorner := by
      exact congrArg (fun coordinate : RX1 P S =>
        match coordinate with
        | Sum.inl _ => P.faceQ firstFace firstCorner
        | Sum.inr qVertex => qVertex.1) hq
    let firstOver : FaceOver P.data (P.faceX firstFace) (P.faceZ firstFace) :=
      ⟨firstFace, rfl, rfl⟩
    let secondOver : FaceOver P.data (P.faceX firstFace) (P.faceZ firstFace) :=
      ⟨secondFace, hxold.symm, hzold.symm⟩
    have hshared : faceCornerToShared P.data
        (P.faceX firstFace) (P.faceZ firstFace) (firstOver, firstCorner) =
      faceCornerToShared P.data
        (P.faceX firstFace) (P.faceZ firstFace) (secondOver, secondCorner) := by
      apply Subtype.ext
      exact hqold
    have hpair := (P.perfectPairing (P.faceX firstFace)
      (P.faceZ firstFace)).1 hshared
    have hface : firstFace = secondFace := by
      exact congrArg (fun pair => pair.1.1) hpair
    have hcorner : firstCorner = secondCorner := congrArg Prod.snd hpair
    subst secondFace
    subst secondCorner
    exact ⟨rfl, rfl⟩
def qSubdivisionVertexXIncidence
    (P : TannerSquarePresentation) (q : P.Q) (x : P.X) (S : OddScale)
    (xVertex : SubdivisionVertex P x S)
    (qVertex : QSubdivisionVertex P q S) : Field :=
  if _hxq : P.xq x q = true then
    match qVertex, xVertex with
    | Sum.inl (Sum.inl _), Sum.inl vertex =>
        if vertex.1 = Vertex.q q then 1 else 0
    | Sum.inl (Sum.inr endpoint), Sum.inl vertex =>
        if vertex.1 = Vertex.z endpoint.1 then 1 else 0
    | Sum.inr qInterior, Sum.inr (Sum.inl xInterior) =>
        match xInterior.1.1 with
        | Sum.inl _ => 0
        | Sum.inr edge =>
            if edge.1.1 = q ∧ edge.1.2 = qInterior.1.1 ∧
                xInterior.2 = qInterior.2 then 1 else 0
    | _, _ => 0
  else 0
def qDoubleCylinderVertexXIncidence
    (P : TannerSquarePresentation) (q : P.Q) (x : P.X) (S : OddScale)
    (xVertex : DoubleCylinderVertex P x S)
    (qVertex : QDoubleCylinderVertex P q S) : Field :=
  if xVertex.1 = qVertex.1 then
    qSubdivisionVertexXIncidence P q x S xVertex.2 qVertex.2
  else 0
noncomputable def qDoubleCylinderEdgeXIncidence
    (P : TannerSquarePresentation) (q : P.Q) (x : P.X) (S : OddScale)
    (xEdge : DoubleCylinderEdge P x S)
    (qEdge : QDoubleCylinderEdge P q S) : Field := by
  classical
  exact if hxq : P.xq x q = true then
    if xEdge = qToXDoubleCylinderEdgeRaw P q x hxq S qEdge then 1 else 0
  else 0
def qDoubleCylinderEdgeVertexIncidence
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (vertex : QDoubleCylinderVertex P q S)
    (edge : QDoubleCylinderEdge P q S) : Field :=
  (if vertex = qDoubleCylinderEdgeStart P q S edge then 1 else 0) +
    (if vertex = qDoubleCylinderEdgeEnd P q S edge then 1 else 0)
def qDoubleCylinderVertexZIncidence
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (vertex : QDoubleCylinderVertex P q S) (zt : P.Z × Two) : Field :=
  if _hqz : P.qz q zt.1 = true then
    match vertex.2 with
    | Sum.inl (Sum.inr endpoint) =>
        if vertex.1 = zt.2 ∧ endpoint.1 = zt.1 then 1 else 0
    | _ => 0
  else 0
noncomputable def rxBoundary1Matrix
    (P : TannerSquarePresentation) (S : OddScale) :
    Matrix (RX0 P S) (RX1 P S) Field := by
  classical
  exact fun xCoordinate qCoordinate =>
    match qCoordinate with
    | Sum.inl xEdge =>
        if h : xCoordinate.1 = xEdge.1 then
          doubleCylinderEdgeVertexMatrix P xCoordinate.1 S
            xCoordinate.2 (h ▸ xEdge.2)
        else 0
    | Sum.inr qVertex =>
        qDoubleCylinderVertexXIncidence P qVertex.1 xCoordinate.1 S
          xCoordinate.2 qVertex.2
noncomputable def rxBoundary2Matrix
    (P : TannerSquarePresentation) (S : OddScale) :
    Matrix (RX1 P S) (RX2 P S) Field := by
  classical
  exact fun qCoordinate zCoordinate =>
    match zCoordinate with
    | Sum.inl (Sum.inl xFace) =>
        match qCoordinate with
        | Sum.inl xEdge =>
            if h : xEdge.1 = xFace.1 then
              doubleCylinderFaceEdgeMatrix P xFace.1 S
                (h ▸ xEdge.2) xFace.2
            else 0
        | Sum.inr _ => 0
    | Sum.inl (Sum.inr qEdge) =>
        match qCoordinate with
        | Sum.inl xEdge =>
            qDoubleCylinderEdgeXIncidence P qEdge.1 xEdge.1 S
              xEdge.2 qEdge.2
        | Sum.inr qVertex =>
            if h : qVertex.1 = qEdge.1 then
              qDoubleCylinderEdgeVertexIncidence P qEdge.1 S
                (h ▸ qVertex.2) qEdge.2
            else 0
    | Sum.inr zPoint =>
        match qCoordinate with
        | Sum.inl _ => 0
        | Sum.inr qVertex =>
            qDoubleCylinderVertexZIncidence P qVertex.1 S qVertex.2 zPoint
noncomputable def rxBoundaryProductMatrix
    (P : TannerSquarePresentation) (S : OddScale) :
    Matrix (RX0 P S) (RX2 P S) Field := fun xCoordinate zCoordinate =>
  ∑ qCoordinate : RX1 P S,
    rxBoundary1Matrix P S xCoordinate qCoordinate *
      rxBoundary2Matrix P S qCoordinate zCoordinate
noncomputable def rxXQIncidence (P : TannerSquarePresentation)
    (S : OddScale) (x : RX0 P S) (q : RX1 P S) : Bool := by
  classical
  exact decide (∃ face : RXFace P S, ∃ corner : Two,
    rxFaceX P S face = x ∧ rxFaceQ P S face corner = q)
noncomputable def rxQZIncidence (P : TannerSquarePresentation)
    (S : OddScale) (q : RX1 P S) (z : RX2 P S) : Bool := by
  classical
  exact decide (∃ face : RXFace P S, ∃ corner : Two,
    rxFaceQ P S face corner = q ∧ rxFaceZ P S face = z)
noncomputable def rxReplacementData (P : TannerSquarePresentation)
    (S : OddScale) : TannerSquareData := by
  classical
  exact
    { X := RX0 P S
      Q := RX1 P S
      Z := RX2 P S
      Face := RXFace P S
      xFintype := inferInstance
      qFintype := inferInstance
      zFintype := inferInstance
      faceFintype := inferInstance
      xDecidableEq := Classical.decEq _
      qDecidableEq := Classical.decEq _
      zDecidableEq := Classical.decEq _
      faceDecidableEq := Classical.decEq _
      xq := rxXQIncidence P S
      qz := rxQZIncidence P S
      faceX := rxFaceX P S
      faceZ := rxFaceZ P S
      faceQ := rxFaceQ P S
      faceQ_xq := by
        intro face corner
        change decide (∃ candidate : RXFace P S, ∃ bit : Two,
          rxFaceX P S candidate = rxFaceX P S face ∧
            rxFaceQ P S candidate bit = rxFaceQ P S face corner) = true
        rw [decide_eq_true_eq]
        exact ⟨face, corner, rfl, rfl⟩
      faceQ_qz := by
        intro face corner
        change decide (∃ candidate : RXFace P S, ∃ bit : Two,
          rxFaceQ P S candidate bit = rxFaceQ P S face corner ∧
            rxFaceZ P S candidate = rxFaceZ P S face) = true
        rw [decide_eq_true_eq]
        exact ⟨face, corner, rfl, rfl⟩ }
set_option maxHeartbeats 800000 in
/-- Face-defined X-Q incidence is exactly corner existence. -/
theorem rxXQIncidence_eq_true_iff
    (P : TannerSquarePresentation) (S : OddScale)
    (x : RX0 P S) (q : RX1 P S) :
    rxXQIncidence P S x q = true ↔
      ∃ face : RXFace P S, ∃ corner : Two,
        rxFaceX P S face = x ∧ rxFaceQ P S face corner = q := by
  simp [rxXQIncidence]
set_option maxHeartbeats 800000 in
/-- Face-defined Q-Z incidence is exactly corner existence. -/
theorem rxQZIncidence_eq_true_iff
    (P : TannerSquarePresentation) (S : OddScale)
    (q : RX1 P S) (z : RX2 P S) :
    rxQZIncidence P S q z = true ↔
      ∃ face : RXFace P S, ∃ corner : Two,
        rxFaceQ P S face corner = q ∧ rxFaceZ P S face = z := by
  simp [rxQZIncidence]
theorem rxReplacementFaceCorner_injective
    (P : TannerSquarePresentation) (S : OddScale)
    (x : RX0 P S) (z : RX2 P S) :
    Function.Injective (faceCornerToShared (rxReplacementData P S) x z) := by
  intro first second hshared
  rcases first with ⟨⟨firstFace, hfirstX, hfirstZ⟩, firstCorner⟩
  rcases second with ⟨⟨secondFace, hsecondX, hsecondZ⟩, secondCorner⟩
  have hq : rxFaceQ P S firstFace firstCorner =
      rxFaceQ P S secondFace secondCorner := by
    exact congrArg Subtype.val hshared
  have hunique := rxFaceCorner_unique P S firstFace secondFace
    firstCorner secondCorner (hfirstX.trans hsecondX.symm)
    (hfirstZ.trans hsecondZ.symm) hq
  rcases hunique with ⟨rfl, rfl⟩
  rfl
theorem rxReplacementFaceCorner_surjective
    (P : TannerSquarePresentation) (S : OddScale)
    (x : RX0 P S) (z : RX2 P S) :
    Function.Surjective (faceCornerToShared (rxReplacementData P S) x z) := by
  intro shared
  rcases shared with ⟨sharedQ, hshared⟩
  have hinc := (Bool.and_eq_true_eq_eq_true_and_eq_true _ _).mp hshared
  obtain ⟨firstFace, firstCorner, hfirstX, hfirstQ⟩ :=
    (rxXQIncidence_eq_true_iff P S x sharedQ).mp hinc.1
  obtain ⟨secondFace, secondCorner, hsecondQ, hsecondZ⟩ :=
    (rxQZIncidence_eq_true_iff P S sharedQ z).mp hinc.2
  rcases sharedQ with xEdge | qVertex
  · rcases xEdge with ⟨localX, edge⟩
    obtain ⟨face, corner, hfaceX, hfaceQ, hfaceZ⟩ :=
      exists_rxFaceCorner_of_xEdge_witnesses P S x z localX edge
        firstFace secondFace firstCorner secondCorner hfirstX hfirstQ
        hsecondQ hsecondZ
    refine ⟨(⟨face, hfaceX, hfaceZ⟩, corner), ?_⟩
    apply Subtype.ext
    exact hfaceQ
  · rcases qVertex with ⟨q, vertex⟩
    obtain ⟨face, corner, hfaceX, hfaceQ, hfaceZ⟩ :=
      exists_rxFaceCorner_of_qVertex_witnesses P S x z q vertex
        firstFace secondFace firstCorner secondCorner hfirstX hfirstQ
        hsecondQ hsecondZ
    refine ⟨(⟨face, hfaceX, hfaceZ⟩, corner), ?_⟩
    apply Subtype.ext
    exact hfaceQ
theorem rxReplacementPerfectPairing
    (P : TannerSquarePresentation) (S : OddScale)
    (x : RX0 P S) (z : RX2 P S) :
    Function.Bijective (faceCornerToShared (rxReplacementData P S) x z) :=
  ⟨rxReplacementFaceCorner_injective P S x z,
    rxReplacementFaceCorner_surjective P S x z⟩
noncomputable def rxReplacementPresentation
    (P : TannerSquarePresentation) (S : OddScale) : TannerSquarePresentation where
  data := rxReplacementData P S
  perfectPairing := rxReplacementPerfectPairing P S
def rxQDoubleCylinderVertexIncidentEdge
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (S : OddScale) (vertex : QDoubleCylinderVertex P q S) :
    {owned : QDoubleCylinderEdge P q S × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (qDoubleCylinderEdgeStart P q S) (qDoubleCylinderEdgeEnd P q S)
        owned.1 owned.2 = vertex} := by
  rcases vertex with ⟨copy, vertex⟩
  rcases vertex with original | interior
  · rcases original with center | endpoint
    · let radial : QStarEdge P q := ⟨(A.qzRoot q).1, (A.qzRoot q).2⟩
      let first : Fin S.half := ⟨0, S.half_pos⟩
      refine ⟨⟨Sum.inl (copy, radial, first), 0⟩, ?_⟩
      rw [BDL26TannerLocalRegularity.edgeEndpoint_zero]
      simp [qDoubleCylinderEdgeStart, qSubdivisionEdgeStart, first,
        qStarEdgeStart]
    · let last : Fin S.half :=
        ⟨S.half - 1, by have := S.half_pos; omega⟩
      refine ⟨⟨Sum.inl (copy, endpoint, last), 1⟩, ?_⟩
      rw [BDL26TannerLocalRegularity.edgeEndpoint_one]
      have hlast : last.1 + 1 = S.half := by
        dsimp [last]
        have := S.half_pos
        omega
      simp [qDoubleCylinderEdgeEnd, qSubdivisionEdgeEnd, qStarEdgeEnd, hlast]
  · rcases interior with ⟨edge, index⟩
    let preceding : Fin S.half :=
      ⟨index.1, by have := index.2; omega⟩
    refine ⟨⟨Sum.inl (copy, edge, preceding), 1⟩, ?_⟩
    rw [BDL26TannerLocalRegularity.edgeEndpoint_one]
    have hnot : preceding.1 + 1 ≠ S.half := by
      dsimp [preceding]
      have := index.2
      omega
    simp [qDoubleCylinderEdgeEnd, qSubdivisionEdgeEnd, hnot, preceding]
noncomputable def rxReplacementQZRootQVertex
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (qVertex : Σ q : P.Q, QDoubleCylinderVertex P q S) :
    {z : (rxReplacementPresentation P S).Z //
      (rxReplacementPresentation P S).qz (Sum.inr qVertex) z = true} := by
  rcases qVertex with ⟨q, vertex⟩
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  obtain ⟨⟨edge, endpoint⟩, hendpoint⟩ :=
    rxQDoubleCylinderVertexIncidentEdge P A q S vertex
  let a : XQEdge P := ⟨((A.xqRoot q).1, q), (A.xqRoot q).2⟩
  let face : RXFace P S := Sum.inr (Sum.inl ⟨a, edge, endpoint⟩)
  refine ⟨Sum.inl (Sum.inr ⟨q, edge⟩), ?_⟩
  apply (rxQZIncidence_eq_true_iff P S _ _).2
  refine ⟨face, 1, ?_, rfl⟩
  change glueFaceQ1 P S ⟨a, edge, endpoint⟩ = Sum.inr ⟨q, vertex⟩
  apply congrArg Sum.inr
  change (⟨q, edgeEndpoint (qDoubleCylinderEdgeStart P q S)
      (qDoubleCylinderEdgeEnd P q S) edge endpoint⟩ :
      Σ q : P.Q, QDoubleCylinderVertex P q S) = ⟨q, vertex⟩
  congr 1
  exact rxTwoElim (motive := fun endpoint =>
      BDL26TannerLocalRegularity.edgeEndpoint
          (qDoubleCylinderEdgeStart P q S)
          (qDoubleCylinderEdgeEnd P q S) edge endpoint = vertex →
        edgeEndpoint (qDoubleCylinderEdgeStart P q S)
          (qDoubleCylinderEdgeEnd P q S) edge endpoint = vertex)
    (fun h => h) (fun h => h) endpoint hendpoint
noncomputable def rxReplacementQZRootLocal
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (localEdge : Σ x : P.X, DoubleCylinderEdge P x S) :
    {z : (rxReplacementPresentation P S).Z //
      (rxReplacementPresentation P S).qz (Sum.inl localEdge) z = true} := by
  rcases localEdge with ⟨x, edge⟩
  obtain ⟨⟨localFace, corner⟩, hcorner⟩ :=
    rxLocalEdgeCornerOwner P A3 S x edge
  refine ⟨localFaceZ P S localFace, ?_⟩
  apply (rxQZIncidence_eq_true_iff P S _ _).2
  refine ⟨Sum.inl localFace, corner, ?_, rfl⟩
  change localFaceQAt P S localFace corner = Sum.inl ⟨x, edge⟩
  exact hcorner
noncomputable def rxReplacementQZRoot
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (q : (rxReplacementPresentation P S).Q) :
    {z : (rxReplacementPresentation P S).Z //
      (rxReplacementPresentation P S).qz q z = true} := by
  rcases q with localEdge | qVertex
  · exact rxReplacementQZRootLocal P A3 S localEdge
  · exact rxReplacementQZRootQVertex P A3 S qVertex
noncomputable def rxReplacementXQRootLocal
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (localEdge : Σ x : P.X, DoubleCylinderEdge P x S) :
    {x : (rxReplacementPresentation P S).X //
      (rxReplacementPresentation P S).xq x (Sum.inl localEdge) = true} := by
  rcases localEdge with ⟨x, edge⟩
  obtain ⟨⟨localFace, corner⟩, hcorner⟩ :=
    rxLocalEdgeCornerOwner P A3 S x edge
  refine ⟨localFaceX P S localFace, ?_⟩
  apply (rxXQIncidence_eq_true_iff P S _ _).2
  refine ⟨Sum.inl localFace, corner, rfl, ?_⟩
  change localFaceQAt P S localFace corner = Sum.inl ⟨x, edge⟩
  exact hcorner
noncomputable def rxReplacementXQRootQVertex
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (qVertex : Σ q : P.Q, QDoubleCylinderVertex P q S) :
    {x : (rxReplacementPresentation P S).X //
      (rxReplacementPresentation P S).xq x (Sum.inr qVertex) = true} := by
  rcases qVertex with ⟨q, vertex⟩
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  obtain ⟨⟨edge, endpoint⟩, hendpoint⟩ :=
    rxQDoubleCylinderVertexIncidentEdge P A q S vertex
  let a : XQEdge P := ⟨((A.xqRoot q).1, q), (A.xqRoot q).2⟩
  let glue : RXXQGlueFace P S := ⟨a, edge, endpoint⟩
  refine ⟨glueFaceX P S glue, ?_⟩
  apply (rxXQIncidence_eq_true_iff P S _ _).2
  refine ⟨Sum.inr (Sum.inl glue), 1, rfl, ?_⟩
  change glueFaceQ1 P S ⟨a, edge, endpoint⟩ = Sum.inr ⟨q, vertex⟩
  apply congrArg Sum.inr
  change (⟨q, edgeEndpoint (qDoubleCylinderEdgeStart P q S)
      (qDoubleCylinderEdgeEnd P q S) edge endpoint⟩ :
      Σ q : P.Q, QDoubleCylinderVertex P q S) = ⟨q, vertex⟩
  congr 1
  exact rxTwoElim (motive := fun endpoint =>
      BDL26TannerLocalRegularity.edgeEndpoint
          (qDoubleCylinderEdgeStart P q S)
          (qDoubleCylinderEdgeEnd P q S) edge endpoint = vertex →
        edgeEndpoint (qDoubleCylinderEdgeStart P q S)
          (qDoubleCylinderEdgeEnd P q S) edge endpoint = vertex)
    (fun h => h) (fun h => h) endpoint hendpoint
noncomputable def rxReplacementXQRoot
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (q : (rxReplacementPresentation P S).Q) :
    {x : (rxReplacementPresentation P S).X //
      (rxReplacementPresentation P S).xq x q = true} := by
  rcases q with localEdge | qVertex
  · exact rxReplacementXQRootLocal P A3 S localEdge
  · exact rxReplacementXQRootQVertex P A3 S qVertex
noncomputable def rxXStarAnchorRadialEdge
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) :
    {edge : XStarEdge P x // (xStarEdgeStart P x edge).1 = Vertex.x x} := by
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  let root := A.xBoundaryRoot x
  obtain ⟨⟨boundary, _endpoint⟩, _hendpoint⟩ :=
    A3.xBoundaryIncidentEdge x root
  rcases boundary with ⟨raw, member⟩
  rcases raw with impossible | qz
  · simp [xStarBoundaryEdgeMember] at member
  · have hxq : P.xq x qz.1.1 = true := by
      change decide (∃ face : P.Face,
        xStarFaceMember P x face = true ∧
          decide (qz = faceQZEdge P face 0 ∨
            qz = faceQZEdge P face 1) = true) = true at member
      obtain ⟨face, hface, huse⟩ := of_decide_eq_true member
      have hx : P.faceX face = x := by
        simpa [xStarFaceMember] using hface
      have hcorner : qz = faceQZEdge P face 0 ∨
          qz = faceQZEdge P face 1 := of_decide_eq_true huse
      rcases hcorner with hcorner | hcorner
      · have hq := congrArg (fun edge : QZEdge P => edge.1.1) hcorner
        simpa [hx, hq, faceQZEdge] using P.data.faceQ_xq face 0
      · have hq := congrArg (fun edge : QZEdge P => edge.1.1) hcorner
        simpa [hx, hq, faceQZEdge] using P.data.faceQ_xq face 1
    let radial : XQEdge P := ⟨(x, qz.1.1), by simpa [hxq]⟩
    have radialMember : xStarEdgeMember P x (Sum.inl radial) = true := by
      change decide (∃ face : P.Face,
        xStarFaceMember P x face = true ∧
          decide (radial = faceXQEdge P face 0 ∨
            radial = faceXQEdge P face 1) = true) = true
      rw [decide_eq_true_eq]
      change decide (∃ face : P.Face,
        xStarFaceMember P x face = true ∧
          decide (qz = faceQZEdge P face 0 ∨
            qz = faceQZEdge P face 1) = true) = true at member
      obtain ⟨face, hface, huse⟩ := of_decide_eq_true member
      refine ⟨face, hface, ?_⟩
      rw [decide_eq_true_eq]
      rcases of_decide_eq_true huse with hcorner | hcorner
      · left
        apply Subtype.ext
        have hx : P.faceX face = x := by
          simpa [xStarFaceMember] using hface
        have hq := congrArg (fun edge : QZEdge P => edge.1.1) hcorner
        exact Prod.ext hx.symm hq
      · right
        apply Subtype.ext
        have hx : P.faceX face = x := by
          simpa [xStarFaceMember] using hface
        have hq := congrArg (fun edge : QZEdge P => edge.1.1) hcorner
        exact Prod.ext hx.symm hq
    refine ⟨⟨Sum.inl radial, radialMember⟩, ?_⟩
    rfl
noncomputable def rxSubdivisionVertexIncidentEdge
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale) (vertex : SubdivisionVertex P x S) :
    {owned : SubdivisionEdge P x S × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
        owned.1 owned.2 = vertex} := by
  rcases vertex with original | interior
  · rcases original with ⟨value, member⟩
    rcases value with oldX | q | z
    · have hx : oldX = x := by
        simpa [xStarVertexMember] using member
      subst oldX
      let edge := (rxXStarAnchorRadialEdge P A3 x).1
      let first : Fin S.half := ⟨0, S.half_pos⟩
      refine ⟨⟨Sum.inl (edge, first), 0⟩, ?_⟩
      rw [BDL26TannerLocalRegularity.edgeEndpoint_zero]
      apply congrArg Sum.inl
      apply Subtype.ext
      simpa [subdivisionEdgeStart, subdivisionSegmentStart, first, edge] using
        (rxXStarAnchorRadialEdge P A3 x).2
    · let boundaryVertex : XStarBoundaryVertex P x :=
        ⟨Vertex.q q, by simpa [xStarBoundaryVertexMember,
          xStarVertexMember] using member⟩
      let subdivided := subdivisionOriginalBoundaryVertex P x S boundaryVertex
      obtain ⟨⟨edge, endpoint⟩, hendpoint⟩ :=
        subdivisionBoundaryIncidentEdge P A3.toTannerSquareAdmissibleV2
          x S subdivided
      refine ⟨⟨edge.1, endpoint⟩, ?_⟩
      exact rxTwoElim (motive := fun endpoint =>
          BDL26TannerLocalRegularity.edgeEndpoint
              (subdivisionBoundaryEdgeStart P x S)
              (subdivisionBoundaryEdgeEnd P x S) edge endpoint = subdivided →
            BDL26TannerLocalRegularity.edgeEndpoint
              (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
              edge.1 endpoint = Sum.inl ⟨Vertex.q q, member⟩)
        (fun h => by
          rw [BDL26TannerLocalRegularity.edgeEndpoint_zero] at h ⊢
          simpa [subdivided, boundaryVertex, subdivisionOriginalBoundaryVertex,
            xStarBoundaryVertexToStar] using congrArg Subtype.val h)
        (fun h => by
          rw [BDL26TannerLocalRegularity.edgeEndpoint_one] at h ⊢
          simpa [subdivided, boundaryVertex, subdivisionOriginalBoundaryVertex,
            xStarBoundaryVertexToStar] using congrArg Subtype.val h) endpoint hendpoint
    · let boundaryVertex : XStarBoundaryVertex P x :=
        ⟨Vertex.z z, by simpa [xStarBoundaryVertexMember,
          xStarVertexMember] using member⟩
      let subdivided := subdivisionOriginalBoundaryVertex P x S boundaryVertex
      obtain ⟨⟨edge, endpoint⟩, hendpoint⟩ :=
        subdivisionBoundaryIncidentEdge P A3.toTannerSquareAdmissibleV2
          x S subdivided
      refine ⟨⟨edge.1, endpoint⟩, ?_⟩
      exact rxTwoElim (motive := fun endpoint =>
          BDL26TannerLocalRegularity.edgeEndpoint
              (subdivisionBoundaryEdgeStart P x S)
              (subdivisionBoundaryEdgeEnd P x S) edge endpoint = subdivided →
            BDL26TannerLocalRegularity.edgeEndpoint
              (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
              edge.1 endpoint = Sum.inl ⟨Vertex.z z, member⟩)
        (fun h => by
          rw [BDL26TannerLocalRegularity.edgeEndpoint_zero] at h ⊢
          simpa [subdivided, boundaryVertex, subdivisionOriginalBoundaryVertex,
            xStarBoundaryVertexToStar] using congrArg Subtype.val h)
        (fun h => by
          rw [BDL26TannerLocalRegularity.edgeEndpoint_one] at h ⊢
          simpa [subdivided, boundaryVertex, subdivisionOriginalBoundaryVertex,
            xStarBoundaryVertexToStar] using congrArg Subtype.val h) endpoint hendpoint
  · rcases interior with edgeInterior | faceInterior
    · rcases edgeInterior with ⟨edge, index⟩
      let preceding : Fin S.half :=
        ⟨index.1, by have := index.2; omega⟩
      refine ⟨⟨Sum.inl (edge, preceding), 1⟩, ?_⟩
      rw [BDL26TannerLocalRegularity.edgeEndpoint_one]
      have hlt : index.1 + 1 < S.half :=
        (Nat.lt_sub_iff_add_lt).1 index.2
      have hnot : preceding.1 + 1 ≠ S.half := by
        dsimp [preceding]
        omega
      simp [subdivisionEdgeEnd, subdivisionSegmentEnd, preceding, hnot]
    · rcases faceInterior with ⟨face, i, j⟩
      let column : Fin S.half :=
        ⟨i.1, by have := i.2; omega⟩
      let row : Fin (S.half + 1) :=
        ⟨j.1 + 1, by
          have hjlt : j.1 + 1 < S.half :=
            (Nat.lt_sub_iff_add_lt).1 j.2
          omega⟩
      let targetColumn : Fin (S.half + 1) := ⟨i.1 + 1, by omega⟩
      let edge : SubdivisionEdge P x S :=
        subdivisionHorizontalEdge P x S face column row
      refine ⟨⟨edge, 1⟩, ?_⟩
      rw [BDL26TannerLocalRegularity.edgeEndpoint_one]
      have hilt : i.1 + 1 < S.half :=
        (Nat.lt_sub_iff_add_lt).1 i.2
      have hjlt : j.1 + 1 < S.half :=
        (Nat.lt_sub_iff_add_lt).1 j.2
      have hend : subdivisionEdgeEnd P x S edge =
          subdivisionGridVertex P x S face targetColumn row := by
        dsimp [edge]
        rw [subdivisionHorizontalEdge_end]
        rfl
      rw [hend]
      simp [targetColumn, row, subdivisionGridVertex, hilt.ne, hjlt.ne]
      constructor
      · apply Fin.ext
        change (i.1 + 1) - 1 = i.1
        omega
      · apply Fin.ext
        change (j.1 + 1) - 1 = j.1
        omega
noncomputable def rxDoubleCylinderVertexIncidentEdge
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale) (vertex : DoubleCylinderVertex P x S) :
    {owned : DoubleCylinderEdge P x S × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (tannerDoubleCylinderEdgeStart P x S)
        (tannerDoubleCylinderEdgeEnd P x S) owned.1 owned.2 = vertex} := by
  obtain ⟨⟨edge, endpoint⟩, hendpoint⟩ :=
    rxSubdivisionVertexIncidentEdge P A3 x S vertex.2
  refine ⟨⟨Sum.inl (vertex.1, edge), endpoint⟩, ?_⟩
  exact rxTwoElim (motive := fun endpoint =>
      BDL26TannerLocalRegularity.edgeEndpoint
          (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
          edge endpoint = vertex.2 →
        BDL26TannerLocalRegularity.edgeEndpoint
          (tannerDoubleCylinderEdgeStart P x S)
          (tannerDoubleCylinderEdgeEnd P x S)
          (Sum.inl (vertex.1, edge)) endpoint = vertex)
    (fun h => by
      rw [BDL26TannerLocalRegularity.edgeEndpoint_zero]
      exact Prod.ext rfl h)
    (fun h => by
      rw [BDL26TannerLocalRegularity.edgeEndpoint_one]
      exact Prod.ext rfl h) endpoint hendpoint
noncomputable def rxReplacementXBoundaryRoot
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (xCoordinate : (rxReplacementPresentation P S).X) :
    XStarBoundaryVertex (rxReplacementPresentation P S) xCoordinate := by
  classical
  rcases xCoordinate with ⟨x, vertex⟩
  obtain ⟨⟨edge, endpoint⟩, hendpoint⟩ :=
    rxDoubleCylinderVertexIncidentEdge P A3 x S vertex
  obtain ⟨⟨⟨ownerX, localCell, materialCorner⟩, qCorner⟩, hq⟩ :=
    rxLocalEdgeCornerOwner P A3 S x edge
  have hsigma : (⟨ownerX,
      if qCorner = 0 then localFaceQ0EdgeAt P ownerX S localCell materialCorner
      else localFaceQ1EdgeAt P ownerX S localCell materialCorner⟩ :
        Σ ownerX : P.X, DoubleCylinderEdge P ownerX S) = ⟨x, edge⟩ := by
    fin_cases qCorner
    · simpa [localFaceQAt, localFaceQ0, localFaceQ0Edge] using hq
    · simpa [localFaceQAt, localFaceQ1, localFaceQ1Edge] using hq
  have hownerX : ownerX = x := congrArg Sigma.fst hsigma
  subst ownerX
  have hedge :
      (if qCorner = 0 then localFaceQ0EdgeAt P x S localCell materialCorner
        else localFaceQ1EdgeAt P x S localCell materialCorner) = edge :=
    eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2
  let newMaterial := localMaterialCornerAtEndpoint P x S localCell
    materialCorner qCorner endpoint
  let localFace : RXLocalFace P S := ⟨x, localCell, newMaterial⟩
  let face : RXFace P S := Sum.inl localFace
  have hendpoint' : edgeEndpoint
      (tannerDoubleCylinderEdgeStart P x S)
      (tannerDoubleCylinderEdgeEnd P x S) edge endpoint = vertex :=
    rxTwoElim (motive := fun endpoint =>
        BDL26TannerLocalRegularity.edgeEndpoint
            (tannerDoubleCylinderEdgeStart P x S)
            (tannerDoubleCylinderEdgeEnd P x S) edge endpoint = vertex →
          edgeEndpoint (tannerDoubleCylinderEdgeStart P x S)
            (tannerDoubleCylinderEdgeEnd P x S) edge endpoint = vertex)
      (fun h => h) (fun h => h) endpoint hendpoint
  have hfaceX : rxFaceX P S face = ⟨x, vertex⟩ := by
    change localFaceX P S ⟨x, localCell, newMaterial⟩ = ⟨x, vertex⟩
    rw [show localFaceX P S ⟨x, localCell, newMaterial⟩ =
        ⟨x, edgeEndpoint (tannerDoubleCylinderEdgeStart P x S)
          (tannerDoubleCylinderEdgeEnd P x S)
          (if qCorner = 0 then
            localFaceQ0EdgeAt P x S localCell materialCorner
          else localFaceQ1EdgeAt P x S localCell materialCorner) endpoint⟩ by
      simpa [newMaterial] using localFaceX_atEndpoint P x S localCell
        materialCorner qCorner endpoint]
    rw [hedge, hendpoint']
  have hfaceQ : rxFaceQ P S face qCorner = Sum.inl ⟨x, edge⟩ := by
    calc
      rxFaceQ P S face qCorner =
          localFaceQAt P S ⟨x, localCell, newMaterial⟩ qCorner := rfl
      _ = localFaceQAt P S ⟨x, localCell, materialCorner⟩ qCorner := by
        simpa [localFaceQAt, newMaterial] using
          localFaceQ_atEndpoint P x S localCell materialCorner qCorner endpoint
      _ = Sum.inl ⟨x, edge⟩ := hq
  refine ⟨Vertex.q (Sum.inl ⟨x, edge⟩), ?_⟩
  simp only [xStarBoundaryVertexMember, decide_eq_true_eq]
  change ∃ candidate : RXFace P S,
    xStarFaceMember (rxReplacementPresentation P S) ⟨x, vertex⟩
        candidate = true ∧
      (Sum.inl ⟨x, edge⟩ = rxFaceQ P S candidate 0 ∨
        Sum.inl ⟨x, edge⟩ = rxFaceQ P S candidate 1)
  refine ⟨face, ?_, ?_⟩
  · simp only [xStarFaceMember, decide_eq_true_eq]
    exact hfaceX
  · exact rxTwoElim (motive := fun qCorner =>
        rxFaceQ P S face qCorner = Sum.inl ⟨x, edge⟩ →
          Sum.inl ⟨x, edge⟩ = rxFaceQ P S face 0 ∨
            Sum.inl ⟨x, edge⟩ = rxFaceQ P S face 1)
      (fun h => Or.inl h.symm) (fun h => Or.inr h.symm) qCorner hfaceQ
def faceZBoundaryXVertex (P : TannerSquarePresentation)
    (face : P.Face) : ZStarBoundaryVertex P (P.faceZ face) :=
  ⟨Vertex.x (P.faceX face), by
    simp only [zStarBoundaryVertexMember, decide_eq_true_eq]
    refine ⟨face, ?_, rfl⟩
    simp [zStarFaceMember]⟩
noncomputable def rxReplacementZBoundaryRoot
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : (rxReplacementPresentation P S).Z) :
    ZStarBoundaryVertex (rxReplacementPresentation P S) z := by
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  rcases z with localOrQEdge | oldZ
  · rcases localOrQEdge with localCell | qEdge
    · let face : (rxReplacementPresentation P S).Face :=
        Sum.inl ⟨localCell.1, localCell.2, (0, 0)⟩
      have hfaceZ : (rxReplacementPresentation P S).faceZ face =
          Sum.inl (Sum.inl localCell) := by rfl
      exact hfaceZ ▸ faceZBoundaryXVertex
        (rxReplacementPresentation P S) face
    · let xroot := A.xqRoot qEdge.1
      let a : XQEdge P := ⟨(xroot.1, qEdge.1), xroot.2⟩
      let glue : RXXQGlueFace P S := ⟨a, qEdge.2, 0⟩
      let face : (rxReplacementPresentation P S).Face :=
        Sum.inr (Sum.inl glue)
      have hfaceZ : (rxReplacementPresentation P S).faceZ face =
          Sum.inl (Sum.inr qEdge) := by
        apply congrArg (fun value => Sum.inl (Sum.inr value))
        apply Sigma.ext
        · rfl
        · rfl
      exact hfaceZ ▸ faceZBoundaryXVertex
        (rxReplacementPresentation P S) face
  · rcases oldZ with ⟨oldZ, copy⟩
    let transposedA3 := transposeTannerSquareAdmissibleV3 P A3
    obtain ⟨⟨raw, member⟩, hstart⟩ :=
      rxXStarAnchorRadialEdge (transposePresentation P) transposedA3 oldZ
    rcases raw with radial | impossible
    · let owner := transposedA3.xRadialFaceOwner oldZ radial member
      let face : (rxReplacementPresentation P S).Face :=
        Sum.inr (Sum.inr (owner.1.1.1, copy))
      have hz : P.faceZ owner.1.1.1 = oldZ := by
        have hmember : xStarFaceMember (transposePresentation P) oldZ owner.1.1.1 = true :=
          owner.1.1.2
        erw [transpose_xStarFaceMember] at hmember
        simpa only [zStarFaceMember, decide_eq_true_eq] using hmember
      have hfaceZ : (rxReplacementPresentation P S).faceZ face =
          Sum.inr (oldZ, copy) := by
        change rxFaceZ P S face = Sum.inr (oldZ, copy)
        simp [face, rxFaceZ, oldZFaceZ, hz]
      exact hfaceZ ▸ faceZBoundaryXVertex
        (rxReplacementPresentation P S) face
    · change Vertex.q impossible.1.1 = Vertex.x oldZ at hstart
      cases hstart
theorem rxOldZBoundaryXStarMember
    (P : TannerSquarePresentation) (x : P.X) (z : P.Z)
    (h : zStarBoundaryVertexMember P z (Vertex.x x) = true) :
    xStarVertexMember P x (Vertex.z z) = true := by
  change decide (∃ face : P.Face,
    zStarFaceMember P z face = true ∧ x = P.faceX face) = true at h
  change decide (∃ face : P.Face,
    xStarFaceMember P x face = true ∧ z = P.faceZ face) = true
  rw [decide_eq_true_eq] at h ⊢
  obtain ⟨face, hz, hx⟩ := h
  refine ⟨face, ?_, ?_⟩
  · simpa [xStarFaceMember] using hx.symm
  · have hz' : P.faceZ face = z := by
      simpa [zStarFaceMember] using hz
    exact hz'.symm
theorem rxOldZBoundaryQZIncidence
    (P : TannerSquarePresentation) (q : P.Q) (z : P.Z)
    (h : zStarBoundaryVertexMember P z (Vertex.q q) = true) :
    P.qz q z = true := by
  change decide (∃ face : P.Face,
    zStarFaceMember P z face = true ∧
      (q = P.faceQ face 0 ∨ q = P.faceQ face 1)) = true at h
  rw [decide_eq_true_eq] at h
  obtain ⟨face, hz, hq | hq⟩ := h
  · have hz' : P.faceZ face = z := by
      simpa [zStarFaceMember] using hz
    simpa [hq, hz'] using P.data.faceQ_qz face 0
  · have hz' : P.faceZ face = z := by
      simpa [zStarFaceMember] using hz
    simpa [hq, hz'] using P.data.faceQ_qz face 1
def rxOldZCopyXCoordinate
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z) (copy : Two)
    (x : P.X) (member : zStarBoundaryVertexMember P z (Vertex.x x) = true) :
    (rxReplacementPresentation P S).X :=
  ⟨x, (copy, Sum.inl ⟨Vertex.z z,
    rxOldZBoundaryXStarMember P x z member⟩)⟩
def rxOldZCopyQCoordinate
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z) (copy : Two)
    (q : P.Q) (member : zStarBoundaryVertexMember P z (Vertex.q q) = true) :
    (rxReplacementPresentation P S).Q :=
  let radial : QStarEdge P q :=
    ⟨z, rxOldZBoundaryQZIncidence P q z member⟩
  Sum.inr ⟨q, (copy, Sum.inl (Sum.inr radial))⟩
noncomputable def rxOldZBoundaryVertexMap
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z) (copy : Two) :
    ZStarBoundaryVertex P z →
      ZStarBoundaryVertex (rxReplacementPresentation P S) (Sum.inr (z, copy)) :=
  fun vertex => by
    classical
    rcases vertex with ⟨value, member⟩
    rcases value with x | q | impossible
    · let newX := rxOldZCopyXCoordinate P S z copy x member
      refine ⟨Vertex.x newX, ?_⟩
      simp only [zStarBoundaryVertexMember, decide_eq_true_eq]
      change ∃ face : RXFace P S,
        zStarFaceMember (rxReplacementPresentation P S) (Sum.inr (z, copy))
            face = true ∧
          newX = rxFaceX P S face
      change decide (∃ face : P.Face,
        zStarFaceMember P z face = true ∧ x = P.faceX face) = true at member
      obtain ⟨face, hz, hx⟩ := of_decide_eq_true member
      refine ⟨Sum.inr (Sum.inr (face, copy)), ?_, ?_⟩
      · have hz' : P.faceZ face = z := by
          simpa [zStarFaceMember] using hz
        simp only [zStarFaceMember, decide_eq_true_eq]
        change rxFaceZ P S (Sum.inr (Sum.inr (face, copy))) =
          Sum.inr (z, copy)
        simp [zStarFaceMember, rxFaceZ, oldZFaceZ, hz']
      · have hz' : P.faceZ face = z := by
          simpa [zStarFaceMember] using hz
        subst x
        subst z
        rfl
    · let newQ := rxOldZCopyQCoordinate P S z copy q member
      refine ⟨Vertex.q newQ, ?_⟩
      simp only [zStarBoundaryVertexMember, decide_eq_true_eq]
      change ∃ face : RXFace P S,
        zStarFaceMember (rxReplacementPresentation P S) (Sum.inr (z, copy))
            face = true ∧
          (newQ = rxFaceQ P S face 0 ∨ newQ = rxFaceQ P S face 1)
      change decide (∃ face : P.Face,
        zStarFaceMember P z face = true ∧
          (q = P.faceQ face 0 ∨ q = P.faceQ face 1)) = true at member
      obtain ⟨face, hz, hq | hq⟩ := of_decide_eq_true member
      · refine ⟨Sum.inr (Sum.inr (face, copy)), ?_, Or.inl ?_⟩
        · have hz' : P.faceZ face = z := by
            simpa [zStarFaceMember] using hz
          simp only [zStarFaceMember, decide_eq_true_eq]
          change rxFaceZ P S (Sum.inr (Sum.inr (face, copy))) =
            Sum.inr (z, copy)
          simp [zStarFaceMember, rxFaceZ, oldZFaceZ, hz']
        · have hz' : P.faceZ face = z := by
            simpa [zStarFaceMember] using hz
          subst q
          subst z
          rfl
      · refine ⟨Sum.inr (Sum.inr (face, copy)), ?_, Or.inr ?_⟩
        · have hz' : P.faceZ face = z := by
            simpa [zStarFaceMember] using hz
          simp only [zStarFaceMember, decide_eq_true_eq]
          change rxFaceZ P S (Sum.inr (Sum.inr (face, copy))) =
            Sum.inr (z, copy)
          simp [zStarFaceMember, rxFaceZ, oldZFaceZ, hz']
        · have hz' : P.faceZ face = z := by
            simpa [zStarFaceMember] using hz
          subst q
          subst z
          rfl
    · simp [zStarBoundaryVertexMember] at member
noncomputable def rxOldZBoundaryEdgeMap
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z) (copy : Two) :
    ZStarBoundaryEdge P z →
      ZStarBoundaryEdge (rxReplacementPresentation P S) (Sum.inr (z, copy)) :=
  fun oldEdge => by
    rcases oldEdge with ⟨raw, member⟩
    rcases raw with oldXQ | impossible
    · let retained : ZStarBoundaryEdge P z := ⟨Sum.inl oldXQ, member⟩
      have hstart : zStarBoundaryVertexMember P z
          (Vertex.x oldXQ.1.1) = true := by
        exact (zBoundaryEdgeStart P z retained).2
      have hend : zStarBoundaryVertexMember P z
          (Vertex.q oldXQ.1.2) = true := by
        exact (zBoundaryEdgeEnd P z retained).2
      let newX := rxOldZCopyXCoordinate P S z copy oldXQ.1.1 hstart
      let newQ := rxOldZCopyQCoordinate P S z copy oldXQ.1.2 hend
      have howner : ∃ face : RXFace P S, ∃ corner : Two,
          rxFaceZ P S face = Sum.inr (z, copy) ∧
            rxFaceX P S face = newX ∧ rxFaceQ P S face corner = newQ := by
        change decide (∃ face : P.Face,
          zStarFaceMember P z face = true ∧
            decide (oldXQ = faceXQEdge P face 0 ∨
              oldXQ = faceXQEdge P face 1) = true) = true at member
        obtain ⟨face, hz, huse⟩ := of_decide_eq_true member
        have hz' : P.faceZ face = z := by
          simpa [zStarFaceMember] using hz
        rcases of_decide_eq_true huse with hcorner | hcorner
        · cases hcorner
          subst z
          refine ⟨Sum.inr (Sum.inr (face, copy)), 0, rfl, ?_, ?_⟩
          · rfl
          · rfl
        · cases hcorner
          subst z
          refine ⟨Sum.inr (Sum.inr (face, copy)), 1, rfl, ?_, ?_⟩
          · rfl
          · rfl
      have hxq : (rxReplacementPresentation P S).xq newX newQ = true := by
        apply (rxXQIncidence_eq_true_iff P S _ _).2
        obtain ⟨face, corner, _hz, hx, hq⟩ := howner
        exact ⟨face, corner, hx, hq⟩
      let successorXQ : XQEdge (rxReplacementPresentation P S) :=
        ⟨(newX, newQ), hxq⟩
      refine ⟨Sum.inl successorXQ, ?_⟩
      simp only [zStarBoundaryEdgeMember, decide_eq_true_eq]
      obtain ⟨face, corner, hz, hx, hq⟩ := howner
      refine ⟨face, ?_, ?_⟩
      · simp only [zStarFaceMember, decide_eq_true_eq]
        exact hz
      · change decide (successorXQ = faceXQEdge (rxReplacementPresentation P S) face 0 ∨
          successorXQ = faceXQEdge (rxReplacementPresentation P S) face 1) = true
        rw [decide_eq_true_eq]
        exact rxTwoElim (motive := fun corner =>
            rxFaceQ P S face corner = newQ →
              successorXQ = faceXQEdge (rxReplacementPresentation P S) face 0 ∨
                successorXQ = faceXQEdge (rxReplacementPresentation P S) face 1)
          (fun hq => Or.inl (by
            apply Subtype.ext
            exact Prod.ext hx.symm hq.symm))
          (fun hq => Or.inr (by
            apply Subtype.ext
            exact Prod.ext hx.symm hq.symm)) corner hq
    · simp [zStarBoundaryEdgeMember] at member
theorem rxOldZBoundaryEdgeMap_start
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z) (copy : Two)
    (edge : ZStarBoundaryEdge P z) :
    zBoundaryEdgeStart (rxReplacementPresentation P S) (Sum.inr (z, copy))
        (rxOldZBoundaryEdgeMap P S z copy edge) =
      rxOldZBoundaryVertexMap P S z copy (zBoundaryEdgeStart P z edge) := by
  rcases edge with ⟨raw, member⟩
  rcases raw with oldXQ | impossible
  · apply Subtype.ext
    rfl
  · simp [zStarBoundaryEdgeMember] at member
theorem rxOldZBoundaryEdgeMap_end
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z) (copy : Two)
    (edge : ZStarBoundaryEdge P z) :
    zBoundaryEdgeEnd (rxReplacementPresentation P S) (Sum.inr (z, copy))
        (rxOldZBoundaryEdgeMap P S z copy edge) =
      rxOldZBoundaryVertexMap P S z copy (zBoundaryEdgeEnd P z edge) := by
  rcases edge with ⟨raw, member⟩
  rcases raw with oldXQ | impossible
  · apply Subtype.ext
    rfl
  · simp [zStarBoundaryEdgeMember] at member
noncomputable def rxOldZBoundaryPathMap
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z) (copy : Two)
    {root target : ZStarBoundaryVertex P z}
    (path : UndirectedPath (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z)
      root target) :
    UndirectedPath
      (zBoundaryEdgeStart (rxReplacementPresentation P S) (Sum.inr (z, copy)))
      (zBoundaryEdgeEnd (rxReplacementPresentation P S) (Sum.inr (z, copy)))
      (rxOldZBoundaryVertexMap P S z copy root)
      (rxOldZBoundaryVertexMap P S z copy target) :=
  UndirectedPath.map
    (rxOldZBoundaryVertexMap P S z copy)
    (rxOldZBoundaryEdgeMap P S z copy)
    (rxOldZBoundaryEdgeMap_start P S z copy)
    (rxOldZBoundaryEdgeMap_end P S z copy) path
noncomputable def rxOldZBoundaryVertexProject
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z) (copy : Two) :
    ZStarBoundaryVertex (rxReplacementPresentation P S) (Sum.inr (z, copy)) →
      ZStarBoundaryVertex P z :=
  fun vertex => by
    classical
    rcases vertex with ⟨value, member⟩
    rcases value with newX | newQ | impossible
    · refine ⟨Vertex.x newX.1, ?_⟩
      change decide (∃ face : P.Face,
        zStarFaceMember P z face = true ∧ newX.1 = P.faceX face) = true
      rw [decide_eq_true_eq]
      simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
      change (∃ face : RXFace P S,
        zStarFaceMember (rxReplacementPresentation P S) (Sum.inr (z, copy))
            face = true ∧ newX = rxFaceX P S face) at member
      obtain ⟨face, hz, hx⟩ := member
      rcases face with localFace | glue | old
      · simp only [zStarFaceMember, decide_eq_true_eq] at hz
        cases hz
      · simp only [zStarFaceMember, decide_eq_true_eq] at hz
        cases hz
      · rcases old with ⟨oldFace, oldCopy⟩
        simp only [zStarFaceMember, decide_eq_true_eq] at hz
        have hzpair : (P.faceZ oldFace, oldCopy) = (z, copy) :=
          Sum.inr.inj hz
        refine ⟨oldFace, ?_, ?_⟩
        · have hzbase : P.faceZ oldFace = z := congrArg Prod.fst hzpair
          simpa [zStarFaceMember] using hzbase
        · exact congrArg Sigma.fst hx
    · rcases newQ with localEdge | qVertex
      · have hfalse : False := by
          simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
          change (∃ face : RXFace P S,
            zStarFaceMember (rxReplacementPresentation P S) (Sum.inr (z, copy))
                face = true ∧
              (Sum.inl localEdge = rxFaceQ P S face 0 ∨
                Sum.inl localEdge = rxFaceQ P S face 1)) at member
          obtain ⟨face, hz, hq⟩ := member
          rcases face with localFace | glue | old
          · simp only [zStarFaceMember, decide_eq_true_eq] at hz
            cases hz
          · simp only [zStarFaceMember, decide_eq_true_eq] at hz
            cases hz
          · rcases hq with hq | hq <;> cases hq
        exact hfalse.elim
      · refine ⟨Vertex.q qVertex.1, ?_⟩
        change decide (∃ face : P.Face,
          zStarFaceMember P z face = true ∧
            (qVertex.1 = P.faceQ face 0 ∨
              qVertex.1 = P.faceQ face 1)) = true
        rw [decide_eq_true_eq]
        simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
        change (∃ face : RXFace P S,
          zStarFaceMember (rxReplacementPresentation P S) (Sum.inr (z, copy))
              face = true ∧
            (Sum.inr qVertex = rxFaceQ P S face 0 ∨
              Sum.inr qVertex = rxFaceQ P S face 1)) at member
        obtain ⟨face, hz, hq⟩ := member
        rcases face with localFace | glue | old
        · simp only [zStarFaceMember, decide_eq_true_eq] at hz
          cases hz
        · simp only [zStarFaceMember, decide_eq_true_eq] at hz
          cases hz
        · rcases old with ⟨oldFace, oldCopy⟩
          simp only [zStarFaceMember, decide_eq_true_eq] at hz
          have hzpair : (P.faceZ oldFace, oldCopy) = (z, copy) :=
            Sum.inr.inj hz
          refine ⟨oldFace, ?_, ?_⟩
          · have hzbase : P.faceZ oldFace = z := congrArg Prod.fst hzpair
            simpa [zStarFaceMember] using hzbase
          · rcases hq with hq | hq
            · left
              exact congrArg Sigma.fst (Sum.inr.inj hq)
            · right
              exact congrArg Sigma.fst (Sum.inr.inj hq)
    · simp [zStarBoundaryVertexMember] at member
theorem rxOldZBoundaryVertexMap_project
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z) (copy : Two)
    (vertex : ZStarBoundaryVertex
      (rxReplacementPresentation P S) (Sum.inr (z, copy))) :
    rxOldZBoundaryVertexMap P S z copy
        (rxOldZBoundaryVertexProject P S z copy vertex) = vertex := by
  classical
  apply Subtype.ext
  rcases vertex with ⟨value, member⟩
  rcases value with newX | newQ | impossible
  · simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
    change (∃ face : RXFace P S,
      zStarFaceMember (rxReplacementPresentation P S) (Sum.inr (z, copy))
          face = true ∧ newX = rxFaceX P S face) at member
    obtain ⟨face, hz, hx⟩ := member
    rcases face with localFace | glue | old
    · simp only [zStarFaceMember, decide_eq_true_eq] at hz
      cases hz
    · simp only [zStarFaceMember, decide_eq_true_eq] at hz
      cases hz
    · rcases old with ⟨oldFace, oldCopy⟩
      simp only [zStarFaceMember, decide_eq_true_eq] at hz
      have hzpair : (P.faceZ oldFace, oldCopy) = (z, copy) := Sum.inr.inj hz
      have hzbase : P.faceZ oldFace = z := congrArg Prod.fst hzpair
      have hcopy : oldCopy = copy := congrArg Prod.snd hzpair
      cases hzbase
      cases hcopy
      cases hx
      rfl
  · rcases newQ with localEdge | qVertex
    · simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
      change (∃ face : RXFace P S,
        zStarFaceMember (rxReplacementPresentation P S) (Sum.inr (z, copy))
            face = true ∧
          (Sum.inl localEdge = rxFaceQ P S face 0 ∨
            Sum.inl localEdge = rxFaceQ P S face 1)) at member
      obtain ⟨face, hz, hq⟩ := member
      rcases face with localFace | glue | old
      · simp only [zStarFaceMember, decide_eq_true_eq] at hz
        cases hz
      · simp only [zStarFaceMember, decide_eq_true_eq] at hz
        cases hz
      · rcases hq with hq | hq <;> cases hq
    · simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
      change (∃ face : RXFace P S,
        zStarFaceMember (rxReplacementPresentation P S) (Sum.inr (z, copy))
            face = true ∧
          (Sum.inr qVertex = rxFaceQ P S face 0 ∨
            Sum.inr qVertex = rxFaceQ P S face 1)) at member
      obtain ⟨face, hz, hq⟩ := member
      rcases face with localFace | glue | old
      · simp only [zStarFaceMember, decide_eq_true_eq] at hz
        cases hz
      · simp only [zStarFaceMember, decide_eq_true_eq] at hz
        cases hz
      · rcases old with ⟨oldFace, oldCopy⟩
        simp only [zStarFaceMember, decide_eq_true_eq] at hz
        have hzpair : (P.faceZ oldFace, oldCopy) = (z, copy) := Sum.inr.inj hz
        have hzbase : P.faceZ oldFace = z := congrArg Prod.fst hzpair
        have hcopy : oldCopy = copy := congrArg Prod.snd hzpair
        cases hzbase
        cases hcopy
        rcases hq with hq | hq
        · cases hq
          rfl
        · cases hq
          rfl
  · simp [zStarBoundaryVertexMember] at member
noncomputable def rxReplacementZBoundaryPathOldZ
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : P.Z) (copy : Two)
    (vertex : ZStarBoundaryVertex
      (rxReplacementPresentation P S) (Sum.inr (z, copy))) :
    UndirectedPath
      (zBoundaryEdgeStart (rxReplacementPresentation P S) (Sum.inr (z, copy)))
      (zBoundaryEdgeEnd (rxReplacementPresentation P S) (Sum.inr (z, copy)))
      (rxReplacementZBoundaryRoot P A3 S (Sum.inr (z, copy))) vertex := by
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  let successorRoot := rxReplacementZBoundaryRoot P A3 S (Sum.inr (z, copy))
  let oldRootTarget := rxOldZBoundaryVertexProject P S z copy successorRoot
  let oldTarget := rxOldZBoundaryVertexProject P S z copy vertex
  let rootFromInput : UndirectedPath
      (zBoundaryEdgeStart (rxReplacementPresentation P S) (Sum.inr (z, copy)))
      (zBoundaryEdgeEnd (rxReplacementPresentation P S) (Sum.inr (z, copy)))
      (rxOldZBoundaryVertexMap P S z copy (A.zBoundaryRoot z))
      (rxOldZBoundaryVertexMap P S z copy oldRootTarget) :=
    rxOldZBoundaryPathMap P S z copy (A.zBoundaryPath z oldRootTarget)
  let targetFromInput : UndirectedPath
      (zBoundaryEdgeStart (rxReplacementPresentation P S) (Sum.inr (z, copy)))
      (zBoundaryEdgeEnd (rxReplacementPresentation P S) (Sum.inr (z, copy)))
      (rxOldZBoundaryVertexMap P S z copy (A.zBoundaryRoot z))
      (rxOldZBoundaryVertexMap P S z copy oldTarget) :=
    rxOldZBoundaryPathMap P S z copy (A.zBoundaryPath z oldTarget)
  have hroot : rxOldZBoundaryVertexMap P S z copy oldRootTarget =
      successorRoot :=
    rxOldZBoundaryVertexMap_project P S z copy successorRoot
  have htarget : rxOldZBoundaryVertexMap P S z copy oldTarget = vertex :=
    rxOldZBoundaryVertexMap_project P S z copy vertex
  let rootFromInput' : UndirectedPath
      (zBoundaryEdgeStart (rxReplacementPresentation P S) (Sum.inr (z, copy)))
      (zBoundaryEdgeEnd (rxReplacementPresentation P S) (Sum.inr (z, copy)))
      (rxOldZBoundaryVertexMap P S z copy (A.zBoundaryRoot z))
      successorRoot := hroot ▸ rootFromInput
  let targetFromInput' : UndirectedPath
      (zBoundaryEdgeStart (rxReplacementPresentation P S) (Sum.inr (z, copy)))
      (zBoundaryEdgeEnd (rxReplacementPresentation P S) (Sum.inr (z, copy)))
      (rxOldZBoundaryVertexMap P S z copy (A.zBoundaryRoot z)) vertex :=
    htarget ▸ targetFromInput
  exact rootFromInput'.reverse.append targetFromInput'
def xStarFaceBoundaryEdge
    (P : TannerSquarePresentation) (x : P.X)
    (face : XStarFace P x) (corner : Two) : XStarBoundaryEdge P x := by
  let edge := xStarFaceQZEdge P x face corner
  refine ⟨edge.1, ?_⟩
  simpa [edge, xStarFaceQZEdge, xStarBoundaryEdgeMember, xStarEdgeMember] using edge.2
theorem xBoundaryEdgeStart_xStarFaceBoundaryEdge_value
    (P : TannerSquarePresentation) (x : P.X)
    (face : XStarFace P x) (corner : Two) :
    (xBoundaryEdgeStart P x
        (xStarFaceBoundaryEdge P x face corner)).1 =
      Vertex.q (P.faceQ face.1 corner) := by
  rfl
noncomputable def zStarFaceBoundaryEdge
    (P : TannerSquarePresentation) (z : P.Z)
    (face : ZStarFace P z) (corner : Two) : ZStarBoundaryEdge P z :=
  transposeXStarBoundaryEdgeEquiv P z
    (xStarFaceBoundaryEdge (transposePresentation P) z
      ((transposeXStarFaceEquiv P z).symm face) corner)
noncomputable def xStarFaceBoundaryPathToQ
    (P : TannerSquarePresentation) (x : P.X)
    (face : XStarFace P x) (corner : Two) :
    UndirectedPath (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)
      (xBoundaryEdgeStart P x (xStarFaceBoundaryEdge P x face 0))
      (xBoundaryEdgeStart P x (xStarFaceBoundaryEdge P x face corner)) :=
  rxTwoElim (motive := fun corner =>
      UndirectedPath (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)
        (xBoundaryEdgeStart P x (xStarFaceBoundaryEdge P x face 0))
        (xBoundaryEdgeStart P x
          (xStarFaceBoundaryEdge P x face corner)))
    .nil
    (.step
      (.step .nil (xStarFaceBoundaryEdge P x face 0)
        (Or.inl ⟨rfl, rfl⟩))
      (xStarFaceBoundaryEdge P x face 1)
      (Or.inr ⟨rfl, rfl⟩)) corner
def xStarFaceBoundaryPathToZ
    (P : TannerSquarePresentation) (x : P.X)
    (face : XStarFace P x) :
    UndirectedPath (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)
      (xBoundaryEdgeStart P x (xStarFaceBoundaryEdge P x face 0))
      (xBoundaryEdgeEnd P x (xStarFaceBoundaryEdge P x face 0)) :=
  .step .nil (xStarFaceBoundaryEdge P x face 0)
    (Or.inl ⟨rfl, rfl⟩)
noncomputable def xStarFaceBoundaryPathBetweenQ
    (P : TannerSquarePresentation) (x : P.X)
    (face : XStarFace P x) (source target : Two) :
    UndirectedPath (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)
      (xBoundaryEdgeStart P x
        (xStarFaceBoundaryEdge P x face source))
      (xBoundaryEdgeStart P x
        (xStarFaceBoundaryEdge P x face target)) :=
  (xStarFaceBoundaryPathToQ P x face source).reverse.append
    (xStarFaceBoundaryPathToQ P x face target)
noncomputable def xStarFaceBoundaryPathFromQToZ
    (P : TannerSquarePresentation) (x : P.X)
    (face : XStarFace P x) (source : Two) :
    UndirectedPath (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)
      (xBoundaryEdgeStart P x
        (xStarFaceBoundaryEdge P x face source))
      (xBoundaryEdgeEnd P x
        (xStarFaceBoundaryEdge P x face 0)) :=
  (xStarFaceBoundaryPathToQ P x face source).reverse.append
    (xStarFaceBoundaryPathToZ P x face)
noncomputable def zStarFaceBoundaryPathToQ
    (P : TannerSquarePresentation) (z : P.Z)
    (face : ZStarFace P z) (corner : Two) :
    UndirectedPath (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z)
      (zBoundaryEdgeEnd P z (zStarFaceBoundaryEdge P z face 0))
      (zBoundaryEdgeEnd P z (zStarFaceBoundaryEdge P z face corner)) :=
  rxTwoElim (motive := fun corner =>
      UndirectedPath (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z)
        (zBoundaryEdgeEnd P z (zStarFaceBoundaryEdge P z face 0))
        (zBoundaryEdgeEnd P z
          (zStarFaceBoundaryEdge P z face corner)))
    .nil
    (.step
      (.step .nil (zStarFaceBoundaryEdge P z face 0)
        (Or.inr ⟨rfl, rfl⟩))
      (zStarFaceBoundaryEdge P z face 1)
      (Or.inl ⟨rfl, rfl⟩)) corner
noncomputable def zStarFaceBoundaryPathToX
    (P : TannerSquarePresentation) (z : P.Z)
    (face : ZStarFace P z) :
    UndirectedPath (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z)
      (zBoundaryEdgeEnd P z (zStarFaceBoundaryEdge P z face 0))
      (zBoundaryEdgeStart P z (zStarFaceBoundaryEdge P z face 0)) :=
  .step .nil (zStarFaceBoundaryEdge P z face 0)
    (Or.inr ⟨rfl, rfl⟩)
noncomputable def zStarFaceBoundaryPathFromXToQ
    (P : TannerSquarePresentation) (z : P.Z)
    (face : ZStarFace P z) (corner : Two) :
    UndirectedPath (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z)
      (zBoundaryEdgeStart P z (zStarFaceBoundaryEdge P z face corner))
      (zBoundaryEdgeEnd P z (zStarFaceBoundaryEdge P z face corner)) :=
  .step .nil (zStarFaceBoundaryEdge P z face corner)
    (Or.inl ⟨rfl, rfl⟩)
def rxLocalCellZStarFace
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (cell : DoubleCylinderFace P x S) (corner : Two × Two) :
    ZStarFace (rxReplacementPresentation P S) (Sum.inl (Sum.inl ⟨x, cell⟩)) :=
  ⟨Sum.inl ⟨x, cell, corner⟩, by
    simp only [zStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl]
    rfl⟩
noncomputable def rxLocalCellBoundaryPathToXCorner
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (cell : DoubleCylinderFace P x S) (corner : Two × Two) :
    UndirectedPath
      (zBoundaryEdgeStart (rxReplacementPresentation P S)
        (Sum.inl (Sum.inl ⟨x, cell⟩)))
      (zBoundaryEdgeEnd (rxReplacementPresentation P S)
        (Sum.inl (Sum.inl ⟨x, cell⟩)))
      (zBoundaryEdgeStart (rxReplacementPresentation P S)
        (Sum.inl (Sum.inl ⟨x, cell⟩))
        (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (Sum.inl (Sum.inl ⟨x, cell⟩))
          (rxLocalCellZStarFace P S x cell (0, 0)) 0))
      (zBoundaryEdgeStart (rxReplacementPresentation P S)
        (Sum.inl (Sum.inl ⟨x, cell⟩))
        (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (Sum.inl (Sum.inl ⟨x, cell⟩))
          (rxLocalCellZStarFace P S x cell corner) 0)) := by
  rcases cell with small | rectangle
  · rcases corner with ⟨first, second⟩
    exact rxTwoElim (motive := fun first =>
        ∀ second, UndirectedPath
          (zBoundaryEdgeStart (rxReplacementPresentation P S)
            (Sum.inl (Sum.inl ⟨x, Sum.inl small⟩)))
          (zBoundaryEdgeEnd (rxReplacementPresentation P S)
            (Sum.inl (Sum.inl ⟨x, Sum.inl small⟩)))
          (zBoundaryEdgeStart (rxReplacementPresentation P S)
            (Sum.inl (Sum.inl ⟨x, Sum.inl small⟩))
            (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
              (Sum.inl (Sum.inl ⟨x, Sum.inl small⟩))
              (rxLocalCellZStarFace P S x (Sum.inl small) (0, 0)) 0))
          (zBoundaryEdgeStart (rxReplacementPresentation P S)
            (Sum.inl (Sum.inl ⟨x, Sum.inl small⟩))
            (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
              (Sum.inl (Sum.inl ⟨x, Sum.inl small⟩))
              (rxLocalCellZStarFace P S x (Sum.inl small) (first, second)) 0)))
      (rxTwoElim
        .nil
        ((zStarFaceBoundaryPathFromXToQ _ _
            (rxLocalCellZStarFace P S x (Sum.inl small) (0, 0)) 1).append
          (zStarFaceBoundaryPathFromXToQ _ _
            (rxLocalCellZStarFace P S x (Sum.inl small) (0, 1)) 1).reverse))
      (rxTwoElim
        ((zStarFaceBoundaryPathFromXToQ _ _
            (rxLocalCellZStarFace P S x (Sum.inl small) (0, 0)) 0).append
          (zStarFaceBoundaryPathFromXToQ _ _
            (rxLocalCellZStarFace P S x (Sum.inl small) (1, 0)) 0).reverse)
        (((zStarFaceBoundaryPathFromXToQ _ _
            (rxLocalCellZStarFace P S x (Sum.inl small) (0, 0)) 0).append
          (zStarFaceBoundaryPathFromXToQ _ _
            (rxLocalCellZStarFace P S x (Sum.inl small) (1, 0)) 0).reverse).append
          ((zStarFaceBoundaryPathFromXToQ _ _
            (rxLocalCellZStarFace P S x (Sum.inl small) (1, 0)) 1).append
          (zStarFaceBoundaryPathFromXToQ _ _
            (rxLocalCellZStarFace P S x (Sum.inl small) (1, 1)) 1).reverse)))
      first second

  · rcases corner with ⟨first, second⟩
    exact rxTwoElim (motive := fun first =>
        ∀ second, UndirectedPath
          (zBoundaryEdgeStart (rxReplacementPresentation P S)
            (Sum.inl (Sum.inl ⟨x, Sum.inr rectangle⟩)))
          (zBoundaryEdgeEnd (rxReplacementPresentation P S)
            (Sum.inl (Sum.inl ⟨x, Sum.inr rectangle⟩)))
          (zBoundaryEdgeStart (rxReplacementPresentation P S)
            (Sum.inl (Sum.inl ⟨x, Sum.inr rectangle⟩))
            (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
              (Sum.inl (Sum.inl ⟨x, Sum.inr rectangle⟩))
              (rxLocalCellZStarFace P S x (Sum.inr rectangle) (0, 0)) 0))
          (zBoundaryEdgeStart (rxReplacementPresentation P S)
            (Sum.inl (Sum.inl ⟨x, Sum.inr rectangle⟩))
            (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
              (Sum.inl (Sum.inl ⟨x, Sum.inr rectangle⟩))
              (rxLocalCellZStarFace P S x (Sum.inr rectangle) (first, second)) 0)))
      (rxTwoElim
        .nil
        ((zStarFaceBoundaryPathFromXToQ _ _
            (rxLocalCellZStarFace P S x (Sum.inr rectangle) (0, 0)) 0).append
          (zStarFaceBoundaryPathFromXToQ _ _
            (rxLocalCellZStarFace P S x (Sum.inr rectangle) (0, 1)) 0).reverse))
      (rxTwoElim
        ((zStarFaceBoundaryPathFromXToQ _ _
            (rxLocalCellZStarFace P S x (Sum.inr rectangle) (0, 0)) 1).append
          (zStarFaceBoundaryPathFromXToQ _ _
            (rxLocalCellZStarFace P S x (Sum.inr rectangle) (1, 0)) 1).reverse)
        (((zStarFaceBoundaryPathFromXToQ _ _
            (rxLocalCellZStarFace P S x (Sum.inr rectangle) (0, 0)) 1).append
          (zStarFaceBoundaryPathFromXToQ _ _
            (rxLocalCellZStarFace P S x (Sum.inr rectangle) (1, 0)) 1).reverse).append
          ((zStarFaceBoundaryPathFromXToQ _ _
            (rxLocalCellZStarFace P S x (Sum.inr rectangle) (1, 0)) 0).append
          (zStarFaceBoundaryPathFromXToQ _ _
            (rxLocalCellZStarFace P S x (Sum.inr rectangle) (1, 1)) 0).reverse)))
      first second
def rxQEdgeGlueZStarFace
    (P : TannerSquarePresentation) (S : OddScale)
    (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S)
    (x : P.X) (hxq : P.xq x qEdge.1 = true) (endpoint : Two) :
    ZStarFace (rxReplacementPresentation P S) (Sum.inl (Sum.inr qEdge)) :=
  ⟨Sum.inr (Sum.inl
      ⟨(⟨(x, qEdge.1), hxq⟩ : XQEdge P), qEdge.2, endpoint⟩), by
    simp only [zStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl]
    rfl⟩
theorem rxQEdgeBoundaryX_incidence
    (P : TannerSquarePresentation) (S : OddScale)
    (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S)
    (newX : RX0 P S)
    (member : zStarBoundaryVertexMember (rxReplacementPresentation P S)
      (Sum.inl (Sum.inr qEdge)) (Vertex.x newX) = true) :
    P.xq newX.1 qEdge.1 = true := by
  classical
  simp only [zStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    at member
  obtain ⟨face, hz, hx⟩ := of_decide_eq_true member
  simp only [zStarFaceMember, decide_eq_true_eq] at hz
  rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl] at hz
  rcases face with localFace | glue | old
  ·
    cases hz
  · rcases glue with ⟨a, edge, endpoint⟩
    change (Sum.inl (Sum.inr
      (⟨a.1.2, edge⟩ : Σ q : P.Q, QDoubleCylinderEdge P q S)) : RX2 P S) =
        Sum.inl (Sum.inr qEdge) at hz
    have howner : (⟨a.1.2, edge⟩ :
        Σ q : P.Q, QDoubleCylinderEdge P q S) = qEdge :=
      Sum.inr.inj (Sum.inl.inj hz)
    have hxowner : newX.1 = a.1.1 := congrArg Sigma.fst hx
    have hqowner : a.1.2 = qEdge.1 := congrArg Sigma.fst howner
    rw [hxowner, ← hqowner]
    exact a.2
  ·
    cases hz
theorem rxQEdgeBoundaryLocalQ_incidence
    (P : TannerSquarePresentation) (S : OddScale)
    (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S)
    (localEdge : Σ x : P.X, DoubleCylinderEdge P x S)
    (member : zStarBoundaryVertexMember (rxReplacementPresentation P S)
      (Sum.inl (Sum.inr qEdge)) (Vertex.q (Sum.inl localEdge)) = true) :
    P.xq localEdge.1 qEdge.1 = true := by
  classical
  simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
  change (∃ face : RXFace P S,
    zStarFaceMember (rxReplacementPresentation P S) (Sum.inl (Sum.inr qEdge))
        face = true ∧
      (Sum.inl localEdge = rxFaceQ P S face 0 ∨
        Sum.inl localEdge = rxFaceQ P S face 1)) at member
  obtain ⟨face, hz, hq⟩ := member
  simp only [zStarFaceMember, decide_eq_true_eq] at hz
  rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl] at hz
  rcases face with localFace | glue | old
  ·
    cases hz
  · rcases glue with ⟨a, edge, endpoint⟩
    change (Sum.inl (Sum.inr
      (⟨a.1.2, edge⟩ : Σ q : P.Q, QDoubleCylinderEdge P q S)) : RX2 P S) =
        Sum.inl (Sum.inr qEdge) at hz
    have howner : (⟨a.1.2, edge⟩ :
        Σ q : P.Q, QDoubleCylinderEdge P q S) = qEdge :=
      Sum.inr.inj (Sum.inl.inj hz)
    rcases hq with hq | hq
    · have hlocal := Sum.inl.inj hq
      have hxowner : localEdge.1 = a.1.1 := congrArg Sigma.fst hlocal
      have hqowner : a.1.2 = qEdge.1 := congrArg Sigma.fst howner
      rw [hxowner, ← hqowner]
      exact a.2
    · cases hq
  ·
    cases hz
theorem rxQEdgeBoundaryLocalQ_edge
    (P : TannerSquarePresentation) (S : OddScale)
    (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S)
    (localEdge : Σ x : P.X, DoubleCylinderEdge P x S)
    (member : zStarBoundaryVertexMember (rxReplacementPresentation P S)
      (Sum.inl (Sum.inr qEdge)) (Vertex.q (Sum.inl localEdge)) = true) :
    localEdge.2 = qToXDoubleCylinderEdgeRaw P qEdge.1 localEdge.1
      (rxQEdgeBoundaryLocalQ_incidence P S qEdge localEdge member) S qEdge.2 := by
  classical
  simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
  change (∃ face : RXFace P S,
    zStarFaceMember (rxReplacementPresentation P S) (Sum.inl (Sum.inr qEdge))
        face = true ∧
      (Sum.inl localEdge = rxFaceQ P S face 0 ∨
        Sum.inl localEdge = rxFaceQ P S face 1)) at member
  obtain ⟨face, hz, hq⟩ := member
  simp only [zStarFaceMember, decide_eq_true_eq] at hz
  rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl] at hz
  rcases face with localFace | glue | old
  ·
    cases hz
  · rcases glue with ⟨a, edge, endpoint⟩
    change (Sum.inl (Sum.inr
      (⟨a.1.2, edge⟩ : Σ q : P.Q, QDoubleCylinderEdge P q S)) : RX2 P S) =
        Sum.inl (Sum.inr qEdge) at hz
    have howner : (⟨a.1.2, edge⟩ :
        Σ q : P.Q, QDoubleCylinderEdge P q S) = qEdge :=
      Sum.inr.inj (Sum.inl.inj hz)
    rcases hq with hq | hq
    · have hlocal := Sum.inl.inj hq
      cases howner
      cases hlocal
      rfl
    · cases hq
  ·
    cases hz
theorem rxQEdgeBoundaryQVertex_endpoints
    (P : TannerSquarePresentation) (S : OddScale)
    (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S)
    (qVertex : Σ q : P.Q, QDoubleCylinderVertex P q S)
    (member : zStarBoundaryVertexMember (rxReplacementPresentation P S)
      (Sum.inl (Sum.inr qEdge)) (Vertex.q (Sum.inr qVertex)) = true) :
    qVertex = ⟨qEdge.1,
        qDoubleCylinderEdgeStart P qEdge.1 S qEdge.2⟩ ∨
      qVertex = ⟨qEdge.1,
        qDoubleCylinderEdgeEnd P qEdge.1 S qEdge.2⟩ := by
  classical
  simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
  change (∃ face : RXFace P S,
    zStarFaceMember (rxReplacementPresentation P S) (Sum.inl (Sum.inr qEdge))
        face = true ∧
      (Sum.inr qVertex = rxFaceQ P S face 0 ∨
        Sum.inr qVertex = rxFaceQ P S face 1)) at member
  obtain ⟨face, hz, hq⟩ := member
  simp only [zStarFaceMember, decide_eq_true_eq] at hz
  rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl] at hz
  rcases face with localFace | glue | old
  ·
    cases hz
  · rcases glue with ⟨a, edge, endpoint⟩
    change (Sum.inl (Sum.inr
      (⟨a.1.2, edge⟩ : Σ q : P.Q, QDoubleCylinderEdge P q S)) : RX2 P S) =
        Sum.inl (Sum.inr qEdge) at hz
    have howner : (⟨a.1.2, edge⟩ :
        Σ q : P.Q, QDoubleCylinderEdge P q S) = qEdge :=
      Sum.inr.inj (Sum.inl.inj hz)
    rcases hq with hq | hq
    · cases hq
    · have hvertex := Sum.inr.inj hq
      cases howner
      exact rxTwoElim (motive := fun endpoint =>
          qVertex = ⟨a.1.2, edgeEndpoint
              (qDoubleCylinderEdgeStart P a.1.2 S)
              (qDoubleCylinderEdgeEnd P a.1.2 S) edge endpoint⟩ →
            qVertex = ⟨a.1.2, qDoubleCylinderEdgeStart P a.1.2 S edge⟩ ∨
              qVertex = ⟨a.1.2,
                qDoubleCylinderEdgeEnd P a.1.2 S edge⟩)
        (fun h => Or.inl (by simpa [edgeEndpoint] using h))
        (fun h => Or.inr (by simpa [edgeEndpoint] using h)) endpoint hvertex
  ·
    cases hz
theorem rxQEdgeBoundaryX_endpoints
    (P : TannerSquarePresentation) (S : OddScale)
    (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S)
    (newX : RX0 P S)
    (member : zStarBoundaryVertexMember (rxReplacementPresentation P S)
      (Sum.inl (Sum.inr qEdge)) (Vertex.x newX) = true) :
    newX = glueFaceX P S
        ⟨(⟨(newX.1, qEdge.1),
          rxQEdgeBoundaryX_incidence P S qEdge newX member⟩ : XQEdge P),
          qEdge.2, 0⟩ ∨
      newX = glueFaceX P S
        ⟨(⟨(newX.1, qEdge.1),
          rxQEdgeBoundaryX_incidence P S qEdge newX member⟩ : XQEdge P),
          qEdge.2, 1⟩ := by
  classical
  simp only [zStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    at member
  obtain ⟨face, hz, hx⟩ := of_decide_eq_true member
  simp only [zStarFaceMember, decide_eq_true_eq] at hz
  rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl] at hz
  rcases face with localFace | glue | old
  · cases hz
  · rcases glue with ⟨a, edge, endpoint⟩
    change (Sum.inl (Sum.inr
      (⟨a.1.2, edge⟩ : Σ q : P.Q, QDoubleCylinderEdge P q S)) : RX2 P S) =
        Sum.inl (Sum.inr qEdge) at hz
    have howner : (⟨a.1.2, edge⟩ :
        Σ q : P.Q, QDoubleCylinderEdge P q S) = qEdge :=
      Sum.inr.inj (Sum.inl.inj hz)
    cases howner
    exact rxTwoElim (motive := fun endpoint =>
        newX = glueFaceX P S ⟨a, edge, endpoint⟩ →
          newX = glueFaceX P S
              ⟨(⟨(newX.1, a.1.2),
                rxQEdgeBoundaryX_incidence P S ⟨a.1.2, edge⟩ newX member⟩ :
                  XQEdge P), edge, 0⟩ ∨
            newX = glueFaceX P S
              ⟨(⟨(newX.1, a.1.2),
                rxQEdgeBoundaryX_incidence P S ⟨a.1.2, edge⟩ newX member⟩ :
                  XQEdge P), edge, 1⟩)
      (fun h => Or.inl (by cases h; rfl))
      (fun h => Or.inr (by cases h; rfl)) endpoint hx
  · cases hz
noncomputable def rxQEdgeBoundaryPathToXEndpoint
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S)
    (x : P.X) (hxq : P.xq x qEdge.1 = true) (endpoint : Two) :
    UndirectedPath
      (zBoundaryEdgeStart (rxReplacementPresentation P S)
        (Sum.inl (Sum.inr qEdge)))
      (zBoundaryEdgeEnd (rxReplacementPresentation P S)
        (Sum.inl (Sum.inr qEdge)))
      (zBoundaryEdgeStart (rxReplacementPresentation P S)
        (Sum.inl (Sum.inr qEdge))
        (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (Sum.inl (Sum.inr qEdge))
          (rxQEdgeGlueZStarFace P S qEdge
            (A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible.xqRoot
              qEdge.1).1
            (A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible.xqRoot
              qEdge.1).2 0) 0))
      (zBoundaryEdgeStart (rxReplacementPresentation P S)
        (Sum.inl (Sum.inr qEdge))
        (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (Sum.inl (Sum.inr qEdge))
          (rxQEdgeGlueZStarFace P S qEdge x hxq endpoint) 0)) := by
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  let rootFace := rxQEdgeGlueZStarFace P S qEdge (A.xqRoot qEdge.1).1
    (A.xqRoot qEdge.1).2 0
  let targetZero := rxQEdgeGlueZStarFace P S qEdge x hxq 0
  let targetOne := rxQEdgeGlueZStarFace P S qEdge x hxq 1
  let toTargetZero :=
    (zStarFaceBoundaryPathFromXToQ _ _ rootFace 1).append
      (zStarFaceBoundaryPathFromXToQ _ _ targetZero 1).reverse
  let zeroToOne :=
    (zStarFaceBoundaryPathFromXToQ _ _ targetZero 0).append
      (zStarFaceBoundaryPathFromXToQ _ _ targetOne 0).reverse
  refine rxTwoElim (motive := fun endpoint =>
      UndirectedPath
        (zBoundaryEdgeStart (rxReplacementPresentation P S)
          (Sum.inl (Sum.inr qEdge)))
        (zBoundaryEdgeEnd (rxReplacementPresentation P S)
          (Sum.inl (Sum.inr qEdge)))
        (zBoundaryEdgeStart (rxReplacementPresentation P S)
          (Sum.inl (Sum.inr qEdge))
          (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
            (Sum.inl (Sum.inr qEdge))
            (rxQEdgeGlueZStarFace P S qEdge
              (A.xqRoot qEdge.1).1 (A.xqRoot qEdge.1).2 0) 0))
        (zBoundaryEdgeStart (rxReplacementPresentation P S)
          (Sum.inl (Sum.inr qEdge))
          (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
            (Sum.inl (Sum.inr qEdge))
            (rxQEdgeGlueZStarFace P S qEdge x hxq endpoint) 0))) ?_ ?_ endpoint
  · exact toTargetZero
  · exact toTargetZero.append zeroToOne
theorem rxReplacementZBoundaryRoot_qEdge
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S) :
    rxReplacementZBoundaryRoot P A3 S (Sum.inl (Sum.inr qEdge)) =
      zBoundaryEdgeStart (rxReplacementPresentation P S)
        (Sum.inl (Sum.inr qEdge))
        (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (Sum.inl (Sum.inr qEdge))
          (rxQEdgeGlueZStarFace P S qEdge
            (A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible.xqRoot
              qEdge.1).1
            (A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible.xqRoot
              qEdge.1).2 0) 0) := by
  apply Subtype.ext
  rfl
noncomputable def rxReplacementZBoundaryPathQEdge
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S)
    (vertex : ZStarBoundaryVertex
      (rxReplacementPresentation P S) (Sum.inl (Sum.inr qEdge))) :
    UndirectedPath
      (zBoundaryEdgeStart (rxReplacementPresentation P S)
        (Sum.inl (Sum.inr qEdge)))
      (zBoundaryEdgeEnd (rxReplacementPresentation P S)
        (Sum.inl (Sum.inr qEdge)))
      (rxReplacementZBoundaryRoot P A3 S (Sum.inl (Sum.inr qEdge))) vertex := by
  rw [rxReplacementZBoundaryRoot_qEdge P A3 S qEdge]
  rcases vertex with ⟨value, member⟩
  rcases value with newX | newQ | impossible
  · let hxq := rxQEdgeBoundaryX_incidence P S qEdge newX member
    let path0 := rxQEdgeBoundaryPathToXEndpoint P A3 S qEdge newX.1 hxq 0
    let path1 := rxQEdgeBoundaryPathToXEndpoint P A3 S qEdge newX.1 hxq 1
    by_cases hstart : newX = glueFaceX P S
        ⟨(⟨(newX.1, qEdge.1), hxq⟩ : XQEdge P), qEdge.2, 0⟩
    · have htarget : zBoundaryEdgeStart (rxReplacementPresentation P S)
          (Sum.inl (Sum.inr qEdge))
          (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
            (Sum.inl (Sum.inr qEdge))
            (rxQEdgeGlueZStarFace P S qEdge newX.1 hxq 0) 0) =
          ⟨Vertex.x newX, member⟩ := by
        apply Subtype.ext
        change Vertex.x (glueFaceX P S
          ⟨(⟨(newX.1, qEdge.1), hxq⟩ : XQEdge P), qEdge.2, 0⟩) =
            Vertex.x newX
        exact congrArg Vertex.x hstart.symm
      rw [htarget] at path0
      exact path0
    · have hend := (rxQEdgeBoundaryX_endpoints P S qEdge newX member).resolve_left
          hstart
      have htarget : zBoundaryEdgeStart (rxReplacementPresentation P S)
          (Sum.inl (Sum.inr qEdge))
          (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
            (Sum.inl (Sum.inr qEdge))
            (rxQEdgeGlueZStarFace P S qEdge newX.1 hxq 1) 0) =
          ⟨Vertex.x newX, member⟩ := by
        apply Subtype.ext
        change Vertex.x (glueFaceX P S
          ⟨(⟨(newX.1, qEdge.1), hxq⟩ : XQEdge P), qEdge.2, 1⟩) =
            Vertex.x newX
        exact congrArg Vertex.x hend.symm
      rw [htarget] at path1
      exact path1
  · rcases newQ with localEdge | qVertex
    · rcases localEdge with ⟨x, localEdge⟩
      let hxq := rxQEdgeBoundaryLocalQ_incidence P S qEdge ⟨x, localEdge⟩ member
      let face := rxQEdgeGlueZStarFace P S qEdge x hxq 0
      let toX := rxQEdgeBoundaryPathToXEndpoint P A3 S qEdge x hxq 0
      let toQ := toX.append (zStarFaceBoundaryPathFromXToQ _ _ face 0)
      have hedge := rxQEdgeBoundaryLocalQ_edge P S qEdge ⟨x, localEdge⟩ member
      change localEdge =
        qToXDoubleCylinderEdgeRaw P qEdge.1 x hxq S qEdge.2 at hedge
      have htarget : zBoundaryEdgeEnd (rxReplacementPresentation P S)
          (Sum.inl (Sum.inr qEdge))
          (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
            (Sum.inl (Sum.inr qEdge)) face 0) =
          ⟨Vertex.q (Sum.inl ⟨x, localEdge⟩), member⟩ := by
        apply Subtype.ext
        change (Vertex.q (Sum.inl (⟨x,
            qToXDoubleCylinderEdgeRaw P qEdge.1 x hxq S qEdge.2⟩ :
              Σ x : P.X, DoubleCylinderEdge P x S)) :
                Vertex (rxReplacementPresentation P S)) =
          Vertex.q (Sum.inl (⟨x, localEdge⟩ :
            Σ x : P.X, DoubleCylinderEdge P x S))
        rw [← hedge]
      exact htarget ▸ toQ
    · by_cases hstart : qVertex = ⟨qEdge.1,
          qDoubleCylinderEdgeStart P qEdge.1 S qEdge.2⟩
      · let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
        let face := rxQEdgeGlueZStarFace P S qEdge (A.xqRoot qEdge.1).1
          (A.xqRoot qEdge.1).2 0
        let path := zStarFaceBoundaryPathFromXToQ _ _ face 1
        have htarget : zBoundaryEdgeEnd (rxReplacementPresentation P S)
            (Sum.inl (Sum.inr qEdge))
            (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
              (Sum.inl (Sum.inr qEdge)) face 1) =
            ⟨Vertex.q (Sum.inr qVertex), member⟩ := by
          apply Subtype.ext
          change (Vertex.q (Sum.inr (⟨qEdge.1,
              qDoubleCylinderEdgeStart P qEdge.1 S qEdge.2⟩ :
                Σ q : P.Q, QDoubleCylinderVertex P q S)) :
              Vertex (rxReplacementPresentation P S)) =
            Vertex.q (Sum.inr qVertex)
          exact congrArg (fun value : Σ q : P.Q, QDoubleCylinderVertex P q S =>
            (Vertex.q (Sum.inr value) :
              Vertex (rxReplacementPresentation P S))) hstart.symm
        exact htarget ▸ path
      · let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
        let x := (A.xqRoot qEdge.1).1
        let hxq := (A.xqRoot qEdge.1).2
        let faceOne := rxQEdgeGlueZStarFace P S qEdge x hxq 1
        let toX := rxQEdgeBoundaryPathToXEndpoint P A3 S qEdge x hxq 1
        let path := toX.append (zStarFaceBoundaryPathFromXToQ _ _ faceOne 1)
        have hend := (rxQEdgeBoundaryQVertex_endpoints P S qEdge qVertex member).resolve_left
          hstart
        have htarget : zBoundaryEdgeEnd (rxReplacementPresentation P S)
            (Sum.inl (Sum.inr qEdge))
            (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
              (Sum.inl (Sum.inr qEdge)) faceOne 1) =
            ⟨Vertex.q (Sum.inr qVertex), member⟩ := by
          apply Subtype.ext
          change (Vertex.q (Sum.inr (⟨qEdge.1,
              qDoubleCylinderEdgeEnd P qEdge.1 S qEdge.2⟩ :
                Σ q : P.Q, QDoubleCylinderVertex P q S)) :
              Vertex (rxReplacementPresentation P S)) =
            Vertex.q (Sum.inr qVertex)
          exact congrArg (fun value : Σ q : P.Q, QDoubleCylinderVertex P q S =>
            (Vertex.q (Sum.inr value) :
              Vertex (rxReplacementPresentation P S))) hend.symm
        exact htarget ▸ path
  · simp [zStarBoundaryVertexMember] at member
noncomputable def rxLocalCellXAt
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (cell : DoubleCylinderFace P x S) (corner : Two × Two) : RX0 P S :=
  localFaceX P S ⟨x, cell, corner⟩
noncomputable def rxLocalCellQAt
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (cell : DoubleCylinderFace P x S) (corner : Two × Two)
    (qCorner : Two) : RX1 P S :=
  localFaceQAt P S ⟨x, cell, corner⟩ qCorner
theorem rxLocalCellBoundaryX_cases
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (cell : DoubleCylinderFace P x S) (newX : RX0 P S)
    (member : zStarBoundaryVertexMember (rxReplacementPresentation P S)
      (Sum.inl (Sum.inl ⟨x, cell⟩)) (Vertex.x newX) = true) :
    newX = rxLocalCellXAt P S x cell (0, 0) ∨
      newX = rxLocalCellXAt P S x cell (0, 1) ∨
      newX = rxLocalCellXAt P S x cell (1, 0) ∨
      newX = rxLocalCellXAt P S x cell (1, 1) := by
  classical
  simp only [zStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    at member
  obtain ⟨face, hz, hx⟩ := of_decide_eq_true member
  simp only [zStarFaceMember, decide_eq_true_eq] at hz
  rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl] at hz
  rcases face with localFaceData | glue | old
  · rcases localFaceData with ⟨oldX, localCell, corner⟩
    change (Sum.inl (Sum.inl (⟨oldX, localCell⟩ :
      Σ oldX : P.X, DoubleCylinderFace P oldX S)) : RX2 P S) =
        Sum.inl (Sum.inl ⟨x, cell⟩) at hz
    have howner : (⟨oldX, localCell⟩ :
        Σ oldX : P.X, DoubleCylinderFace P oldX S) = ⟨x, cell⟩ :=
      Sum.inl.inj (Sum.inl.inj hz)
    cases howner
    rcases corner with ⟨first, second⟩
    exact rxTwoElim (motive := fun first =>
        ∀ second,
          newX = rxLocalCellXAt P S x cell (first, second) →
            newX = rxLocalCellXAt P S x cell (0, 0) ∨
            newX = rxLocalCellXAt P S x cell (0, 1) ∨
            newX = rxLocalCellXAt P S x cell (1, 0) ∨
            newX = rxLocalCellXAt P S x cell (1, 1))
      (rxTwoElim (fun h => Or.inl h)
        (fun h => Or.inr (Or.inl h)))
      (rxTwoElim (fun h => Or.inr (Or.inr (Or.inl h)))
        (fun h => Or.inr (Or.inr (Or.inr h)))) first second hx
  · cases hz
  · cases hz
theorem rxLocalCellBoundaryQ_cases
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (cell : DoubleCylinderFace P x S) (newQ : RX1 P S)
    (member : zStarBoundaryVertexMember (rxReplacementPresentation P S)
      (Sum.inl (Sum.inl ⟨x, cell⟩)) (Vertex.q newQ) = true) :
    newQ = rxLocalCellQAt P S x cell (0, 0) 0 ∨
      newQ = rxLocalCellQAt P S x cell (0, 0) 1 ∨
      newQ = rxLocalCellQAt P S x cell (0, 1) 0 ∨
      newQ = rxLocalCellQAt P S x cell (0, 1) 1 ∨
      newQ = rxLocalCellQAt P S x cell (1, 0) 0 ∨
      newQ = rxLocalCellQAt P S x cell (1, 0) 1 ∨
      newQ = rxLocalCellQAt P S x cell (1, 1) 0 ∨
      newQ = rxLocalCellQAt P S x cell (1, 1) 1 := by
  classical
  simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
  change (∃ face : RXFace P S,
    zStarFaceMember (rxReplacementPresentation P S)
        (Sum.inl (Sum.inl ⟨x, cell⟩)) face = true ∧
      (newQ = rxFaceQ P S face 0 ∨ newQ = rxFaceQ P S face 1)) at member
  obtain ⟨face, hz, hq⟩ := member
  simp only [zStarFaceMember, decide_eq_true_eq] at hz
  rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl] at hz
  rcases face with localFaceData | glue | old
  · rcases localFaceData with ⟨oldX, localCell, corner⟩
    change (Sum.inl (Sum.inl (⟨oldX, localCell⟩ :
      Σ oldX : P.X, DoubleCylinderFace P oldX S)) : RX2 P S) =
        Sum.inl (Sum.inl ⟨x, cell⟩) at hz
    have howner : (⟨oldX, localCell⟩ :
        Σ oldX : P.X, DoubleCylinderFace P oldX S) = ⟨x, cell⟩ :=
      Sum.inl.inj (Sum.inl.inj hz)
    cases howner
    rcases corner with ⟨first, second⟩
    have route : ∀ qCorner,
        newQ = rxLocalCellQAt P S x cell (first, second) qCorner →
          newQ = rxLocalCellQAt P S x cell (0, 0) 0 ∨
          newQ = rxLocalCellQAt P S x cell (0, 0) 1 ∨
          newQ = rxLocalCellQAt P S x cell (0, 1) 0 ∨
          newQ = rxLocalCellQAt P S x cell (0, 1) 1 ∨
          newQ = rxLocalCellQAt P S x cell (1, 0) 0 ∨
          newQ = rxLocalCellQAt P S x cell (1, 0) 1 ∨
          newQ = rxLocalCellQAt P S x cell (1, 1) 0 ∨
          newQ = rxLocalCellQAt P S x cell (1, 1) 1 :=
      rxTwoElim (motive := fun first => ∀ second qCorner,
          newQ = rxLocalCellQAt P S x cell (first, second) qCorner → _)
        (rxTwoElim
          (rxTwoElim (fun h => Or.inl h)
            (fun h => Or.inr (Or.inl h)))
          (rxTwoElim (fun h => Or.inr (Or.inr (Or.inl h)))
            (fun h => Or.inr (Or.inr (Or.inr (Or.inl h))))))
        (rxTwoElim
          (rxTwoElim (fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
            (fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
          (rxTwoElim
            (fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inl h)))))))
            (fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inr h))))))))) first second
    rcases hq with hq | hq
    · exact route 0 hq
    · exact route 1 hq
  · cases hz
  · cases hz
noncomputable def rxLocalCellBoundaryPathToQCorner
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (cell : DoubleCylinderFace P x S) (corner : Two × Two)
    (qCorner : Two) :
    UndirectedPath
      (zBoundaryEdgeStart (rxReplacementPresentation P S)
        (Sum.inl (Sum.inl ⟨x, cell⟩)))
      (zBoundaryEdgeEnd (rxReplacementPresentation P S)
        (Sum.inl (Sum.inl ⟨x, cell⟩)))
      (zBoundaryEdgeStart (rxReplacementPresentation P S)
        (Sum.inl (Sum.inl ⟨x, cell⟩))
        (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (Sum.inl (Sum.inl ⟨x, cell⟩))
          (rxLocalCellZStarFace P S x cell (0, 0)) 0))
      (zBoundaryEdgeEnd (rxReplacementPresentation P S)
        (Sum.inl (Sum.inl ⟨x, cell⟩))
        (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (Sum.inl (Sum.inl ⟨x, cell⟩))
          (rxLocalCellZStarFace P S x cell corner) qCorner)) :=
  (rxLocalCellBoundaryPathToXCorner P S x cell corner).append
    (zStarFaceBoundaryPathFromXToQ _ _
      (rxLocalCellZStarFace P S x cell corner) qCorner)
theorem rxReplacementZBoundaryRoot_localCell
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (x : P.X) (cell : DoubleCylinderFace P x S) :
    rxReplacementZBoundaryRoot P A3 S (Sum.inl (Sum.inl ⟨x, cell⟩)) =
      zBoundaryEdgeStart (rxReplacementPresentation P S)
        (Sum.inl (Sum.inl ⟨x, cell⟩))
        (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (Sum.inl (Sum.inl ⟨x, cell⟩))
          (rxLocalCellZStarFace P S x cell (0, 0)) 0) := by
  apply Subtype.ext
  rfl
noncomputable def rxReplacementZBoundaryPathLocalCell
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (x : P.X) (cell : DoubleCylinderFace P x S)
    (vertex : ZStarBoundaryVertex (rxReplacementPresentation P S)
      (Sum.inl (Sum.inl ⟨x, cell⟩))) :
    UndirectedPath
      (zBoundaryEdgeStart (rxReplacementPresentation P S)
        (Sum.inl (Sum.inl ⟨x, cell⟩)))
      (zBoundaryEdgeEnd (rxReplacementPresentation P S)
        (Sum.inl (Sum.inl ⟨x, cell⟩)))
      (rxReplacementZBoundaryRoot P A3 S (Sum.inl (Sum.inl ⟨x, cell⟩)))
      vertex := by
  rw [rxReplacementZBoundaryRoot_localCell P A3 S x cell]
  rcases vertex with ⟨value, member⟩
  rcases value with newX | newQ | impossible
  · by_cases h00 : newX = rxLocalCellXAt P S x cell (0, 0)
    · let path := rxLocalCellBoundaryPathToXCorner P S x cell (0, 0)
      have htarget : zBoundaryEdgeStart (rxReplacementPresentation P S)
          (Sum.inl (Sum.inl ⟨x, cell⟩))
          (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
            (Sum.inl (Sum.inl ⟨x, cell⟩))
            (rxLocalCellZStarFace P S x cell (0, 0)) 0) =
          ⟨Vertex.x newX, member⟩ := by
        apply Subtype.ext
        exact congrArg Vertex.x h00.symm
      exact htarget ▸ path
    · by_cases h01 : newX = rxLocalCellXAt P S x cell (0, 1)
      · let path := rxLocalCellBoundaryPathToXCorner P S x cell (0, 1)
        have htarget : zBoundaryEdgeStart (rxReplacementPresentation P S)
            (Sum.inl (Sum.inl ⟨x, cell⟩))
            (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
              (Sum.inl (Sum.inl ⟨x, cell⟩))
              (rxLocalCellZStarFace P S x cell (0, 1)) 0) =
            ⟨Vertex.x newX, member⟩ := by
          apply Subtype.ext
          exact congrArg Vertex.x h01.symm
        exact htarget ▸ path
      · by_cases h10 : newX = rxLocalCellXAt P S x cell (1, 0)
        · let path := rxLocalCellBoundaryPathToXCorner P S x cell (1, 0)
          have htarget : zBoundaryEdgeStart (rxReplacementPresentation P S)
              (Sum.inl (Sum.inl ⟨x, cell⟩))
              (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
                (Sum.inl (Sum.inl ⟨x, cell⟩))
                (rxLocalCellZStarFace P S x cell (1, 0)) 0) =
              ⟨Vertex.x newX, member⟩ := by
            apply Subtype.ext
            exact congrArg Vertex.x h10.symm
          exact htarget ▸ path
        · have h11 := (((rxLocalCellBoundaryX_cases P S x cell newX member).resolve_left
              h00).resolve_left h01).resolve_left h10
          let path := rxLocalCellBoundaryPathToXCorner P S x cell (1, 1)
          have htarget : zBoundaryEdgeStart (rxReplacementPresentation P S)
              (Sum.inl (Sum.inl ⟨x, cell⟩))
              (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
                (Sum.inl (Sum.inl ⟨x, cell⟩))
                (rxLocalCellZStarFace P S x cell (1, 1)) 0) =
              ⟨Vertex.x newX, member⟩ := by
            apply Subtype.ext
            exact congrArg Vertex.x h11.symm
          exact htarget ▸ path
  · have cases := rxLocalCellBoundaryQ_cases P S x cell newQ member
    by_cases h000 : newQ = rxLocalCellQAt P S x cell (0, 0) 0
    · let path := rxLocalCellBoundaryPathToQCorner P S x cell (0, 0) 0
      have htarget : zBoundaryEdgeEnd (rxReplacementPresentation P S)
          (Sum.inl (Sum.inl ⟨x, cell⟩))
          (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
            (Sum.inl (Sum.inl ⟨x, cell⟩))
            (rxLocalCellZStarFace P S x cell (0, 0)) 0) =
          ⟨Vertex.q newQ, member⟩ := by
        apply Subtype.ext
        exact congrArg Vertex.q h000.symm
      exact htarget ▸ path
    · by_cases h001 : newQ = rxLocalCellQAt P S x cell (0, 0) 1
      · let path := rxLocalCellBoundaryPathToQCorner P S x cell (0, 0) 1
        have htarget : zBoundaryEdgeEnd (rxReplacementPresentation P S)
            (Sum.inl (Sum.inl ⟨x, cell⟩))
            (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
              (Sum.inl (Sum.inl ⟨x, cell⟩))
              (rxLocalCellZStarFace P S x cell (0, 0)) 1) =
            ⟨Vertex.q newQ, member⟩ := by
          apply Subtype.ext
          exact congrArg Vertex.q h001.symm
        exact htarget ▸ path
      · by_cases h010 : newQ = rxLocalCellQAt P S x cell (0, 1) 0
        · let path := rxLocalCellBoundaryPathToQCorner P S x cell (0, 1) 0
          have htarget : zBoundaryEdgeEnd (rxReplacementPresentation P S)
              (Sum.inl (Sum.inl ⟨x, cell⟩))
              (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
                (Sum.inl (Sum.inl ⟨x, cell⟩))
                (rxLocalCellZStarFace P S x cell (0, 1)) 0) =
              ⟨Vertex.q newQ, member⟩ := by
            apply Subtype.ext
            exact congrArg Vertex.q h010.symm
          exact htarget ▸ path
        · by_cases h011 : newQ = rxLocalCellQAt P S x cell (0, 1) 1
          · let path := rxLocalCellBoundaryPathToQCorner P S x cell (0, 1) 1
            have htarget : zBoundaryEdgeEnd (rxReplacementPresentation P S)
                (Sum.inl (Sum.inl ⟨x, cell⟩))
                (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
                  (Sum.inl (Sum.inl ⟨x, cell⟩))
                  (rxLocalCellZStarFace P S x cell (0, 1)) 1) =
                ⟨Vertex.q newQ, member⟩ := by
              apply Subtype.ext
              exact congrArg Vertex.q h011.symm
            exact htarget ▸ path
          · by_cases h100 : newQ = rxLocalCellQAt P S x cell (1, 0) 0
            · let path := rxLocalCellBoundaryPathToQCorner P S x cell (1, 0) 0
              have htarget : zBoundaryEdgeEnd (rxReplacementPresentation P S)
                  (Sum.inl (Sum.inl ⟨x, cell⟩))
                  (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
                    (Sum.inl (Sum.inl ⟨x, cell⟩))
                    (rxLocalCellZStarFace P S x cell (1, 0)) 0) =
                  ⟨Vertex.q newQ, member⟩ := by
                apply Subtype.ext
                exact congrArg Vertex.q h100.symm
              exact htarget ▸ path
            · by_cases h101 : newQ = rxLocalCellQAt P S x cell (1, 0) 1
              · let path := rxLocalCellBoundaryPathToQCorner P S x cell (1, 0) 1
                have htarget : zBoundaryEdgeEnd (rxReplacementPresentation P S)
                    (Sum.inl (Sum.inl ⟨x, cell⟩))
                    (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
                      (Sum.inl (Sum.inl ⟨x, cell⟩))
                      (rxLocalCellZStarFace P S x cell (1, 0)) 1) =
                    ⟨Vertex.q newQ, member⟩ := by
                  apply Subtype.ext
                  exact congrArg Vertex.q h101.symm
                exact htarget ▸ path
              · by_cases h110 : newQ = rxLocalCellQAt P S x cell (1, 1) 0
                · let path := rxLocalCellBoundaryPathToQCorner P S x cell (1, 1) 0
                  have htarget : zBoundaryEdgeEnd (rxReplacementPresentation P S)
                      (Sum.inl (Sum.inl ⟨x, cell⟩))
                      (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
                        (Sum.inl (Sum.inl ⟨x, cell⟩))
                        (rxLocalCellZStarFace P S x cell (1, 1)) 0) =
                      ⟨Vertex.q newQ, member⟩ := by
                    apply Subtype.ext
                    exact congrArg Vertex.q h110.symm
                  exact htarget ▸ path
                · have remaining001 := cases.resolve_left h000
                  have remaining010 := remaining001.resolve_left h001
                  have remaining011 := remaining010.resolve_left h010
                  have remaining100 := remaining011.resolve_left h011
                  have remaining101 := remaining100.resolve_left h100
                  have remaining110 := remaining101.resolve_left h101
                  have h111 := remaining110.resolve_left h110
                  let path := rxLocalCellBoundaryPathToQCorner P S x cell (1, 1) 1
                  have htarget : zBoundaryEdgeEnd (rxReplacementPresentation P S)
                      (Sum.inl (Sum.inl ⟨x, cell⟩))
                      (zStarFaceBoundaryEdge (rxReplacementPresentation P S)
                        (Sum.inl (Sum.inl ⟨x, cell⟩))
                        (rxLocalCellZStarFace P S x cell (1, 1)) 1) =
                      ⟨Vertex.q newQ, member⟩ := by
                    apply Subtype.ext
                    exact congrArg Vertex.q h111.symm
                  exact htarget ▸ path
  · simp [zStarBoundaryVertexMember] at member
noncomputable def rxReplacementZBoundaryPath
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (z : (rxReplacementPresentation P S).Z)
    (vertex : ZStarBoundaryVertex (rxReplacementPresentation P S) z) :
    UndirectedPath
      (zBoundaryEdgeStart (rxReplacementPresentation P S) z)
      (zBoundaryEdgeEnd (rxReplacementPresentation P S) z)
      (rxReplacementZBoundaryRoot P A3 S z) vertex := by
  rcases z with localOrQEdge | oldZ
  · rcases localOrQEdge with localCell | qEdge
    · exact rxReplacementZBoundaryPathLocalCell P A3 S localCell.1
        localCell.2 vertex
    · exact rxReplacementZBoundaryPathQEdge P A3 S qEdge vertex
  · exact rxReplacementZBoundaryPathOldZ P A3 S oldZ.1 oldZ.2 vertex
def rxOriginalXStarVertex (P : TannerSquarePresentation) (x : P.X) :
    XStarVertex P x :=
  ⟨Vertex.x x, by simp [xStarVertexMember]⟩
def rxOriginalCentralXCoordinate
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two) :
    (rxReplacementPresentation P S).X :=
  ⟨x, (copy, Sum.inl (rxOriginalXStarVertex P x))⟩
def rxOriginalCentralCell
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (face : XStarFace P x) : DoubleCylinderFace P x S :=
  Sum.inl (copy, (face, rxRadialGridZero S, rxRadialGridZero S))
def rxOriginalCentralFace
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (face : XStarFace P x) : RXFace P S :=
  Sum.inl ⟨x, rxOriginalCentralCell P S x copy face, (0, 0)⟩
@[simp] theorem rxOriginalCentralFace_x
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (face : XStarFace P x) :
    rxFaceX P S (rxOriginalCentralFace P S x copy face) =
      rxOriginalCentralXCoordinate P S x copy := by
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    change (copy, subdivisionGridVertex P x S face 0 0) =
      (copy, Sum.inl (rxOriginalXStarVertex P x))
    apply Prod.ext
    · rfl
    · have hx : P.faceX face.1 = x := by
        simpa [xStarFaceMember] using face.2
      simp [subdivisionGridVertex, rxOriginalXStarVertex,
        xStarFaceXVertex, hx]
@[simp] theorem rxOriginalCentralFace_z
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (face : XStarFace P x) :
    rxFaceZ P S (rxOriginalCentralFace P S x copy face) =
      Sum.inl (Sum.inl ⟨x, rxOriginalCentralCell P S x copy face⟩) := rfl
theorem subdivisionGridVertex_eq_originalX_coordinates
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (face : XStarFace P x) (a b : Fin (S.half + 1))
    (h : subdivisionGridVertex P x S face a b =
      Sum.inl (rxOriginalXStarVertex P x)) :
    a.1 = 0 ∧ b.1 = 0 ∧ P.faceX face.1 = x := by
  simp only [subdivisionGridVertex] at h
  split at h <;> rename_i ha0
  · split at h <;> rename_i hb0
    · refine ⟨ha0, hb0, ?_⟩
      have raw := congrArg Subtype.val (Sum.inl.inj h)
      exact Vertex.x.inj raw
    · split at h <;> rename_i hblast
      · have raw := congrArg Subtype.val (Sum.inl.inj h)
        cases raw
      · cases h
  · split at h <;> rename_i halast
    · split at h <;> rename_i hb0
      · have raw := congrArg Subtype.val (Sum.inl.inj h)
        cases raw
      · split at h <;> rename_i hblast
        · have raw := congrArg Subtype.val (Sum.inl.inj h)
          cases raw
        · cases h
    · split at h <;> rename_i hb0
      · cases h
      · split at h <;> rename_i hblast <;> cases h
theorem rxOriginalCentralFace_cases
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (candidate : RXFace P S)
    (hx : rxFaceX P S candidate =
      rxOriginalCentralXCoordinate P S x copy) :
    ∃ face : XStarFace P x,
      candidate = rxOriginalCentralFace P S x copy face := by
  classical
  rcases candidate with candidateLocal | glue | old
  · rcases candidateLocal with ⟨oldX, localCell, material⟩
    rcases localCell with copyFace | rectangle
    · rcases copyFace with ⟨candidateCopy, small⟩
      rcases small with ⟨candidateFace, column, row⟩
      rcases material with ⟨first, second⟩
      have howner : oldX = x := congrArg Sigma.fst hx
      subst oldX
      have hvertex :
          (candidateCopy,
            subdivisionGridVertex P x S candidateFace
              (gridEndpoint column first) (gridEndpoint row second)) =
            (copy, Sum.inl (rxOriginalXStarVertex P x)) :=
        eq_of_heq (Sigma.mk.inj_iff.mp hx).2
      have hcopy : candidateCopy = copy := congrArg Prod.fst hvertex
      subst candidateCopy
      have hgrid : subdivisionGridVertex P x S candidateFace
          (gridEndpoint column first) (gridEndpoint row second) =
          Sum.inl (rxOriginalXStarVertex P x) := congrArg Prod.snd hvertex
      have coordinates := subdivisionGridVertex_eq_originalX_coordinates
        P S x candidateFace (gridEndpoint column first)
          (gridEndpoint row second) hgrid
      fin_cases first <;> fin_cases second
      · have hcolumn : column = rxRadialGridZero S := by
          apply Fin.ext
          simpa [gridEndpoint, lowerGridIndex, rxRadialGridZero] using
            coordinates.1
        have hrow : row = rxRadialGridZero S := by
          apply Fin.ext
          simpa [gridEndpoint, lowerGridIndex, rxRadialGridZero] using
            coordinates.2.1
        let face : XStarFace P x := ⟨candidateFace, by
          simp [xStarFaceMember, coordinates.2.2]⟩
        refine ⟨face, ?_⟩
        rw [hcolumn, hrow]
        rfl
      · have := coordinates.2.1
        simp [gridEndpoint, upperGridIndex] at this
      · have := coordinates.1
        simp [gridEndpoint, upperGridIndex] at this
      · have := coordinates.1
        simp [gridEndpoint, upperGridIndex] at this
    · rcases material with ⟨materialCopy, endpoint⟩
      have howner : oldX = x := congrArg Sigma.fst hx
      subst oldX
      have hvertex : doubleCylinderRectangleCorner P x S rectangle
          (materialCopy, endpoint) =
          (copy, Sum.inl (rxOriginalXStarVertex P x)) :=
        eq_of_heq (Sigma.mk.inj_iff.mp hx).2
      have hsubdivision := congrArg Prod.snd hvertex
      fin_cases endpoint
      · have hmember := (subdivisionBoundaryEdgeStart P x S rectangle).2
        rw [subdivisionBoundaryEdgeStart_value] at hmember
        have himpossible : subdivisionEdgeStart P x S rectangle.1 =
            Sum.inl (rxOriginalXStarVertex P x) := by
          simpa [doubleCylinderRectangleCorner] using hsubdivision
        rw [himpossible] at hmember
        simp [subdivisionBoundaryVertexMember, rxOriginalXStarVertex,
          xStarBoundaryVertexMember] at hmember
      · have hmember := (subdivisionBoundaryEdgeEnd P x S rectangle).2
        rw [subdivisionBoundaryEdgeEnd_value] at hmember
        have himpossible : subdivisionEdgeEnd P x S rectangle.1 =
            Sum.inl (rxOriginalXStarVertex P x) := by
          simpa [doubleCylinderRectangleCorner] using hsubdivision
        rw [himpossible] at hmember
        simp [subdivisionBoundaryVertexMember, rxOriginalXStarVertex,
          xStarBoundaryVertexMember] at hmember
  · rcases glue with ⟨a, edge, endpoint⟩
    have howner : a.1.1 = x := congrArg Sigma.fst hx
    subst x
    have hvertex : edgeEndpoint
          (tannerDoubleCylinderEdgeStart P a.1.1 S)
          (tannerDoubleCylinderEdgeEnd P a.1.1 S)
          (qToXDoubleCylinderEdgeRaw P a.1.2 a.1.1 a.2 S edge) endpoint =
        (copy, Sum.inl (rxOriginalXStarVertex P a.1.1)) :=
      eq_of_heq (Sigma.mk.inj_iff.mp hx).2
    rcases edge with copyEdge | vertical
    · rcases copyEdge with ⟨edgeCopy, qEdge⟩
      fin_cases endpoint
      · have hmember :=
            (subdivisionBoundaryEdgeStart P a.1.1 S
              (qToXSubdivisionBoundaryEdge P a.1.2 a.1.1 a.2 S qEdge)).2
        rw [subdivisionBoundaryEdgeStart_value] at hmember
        have himpossible : subdivisionEdgeStart P a.1.1 S
              (qToXSubdivisionBoundaryEdge P a.1.2 a.1.1 a.2 S qEdge).1 =
            Sum.inl (rxOriginalXStarVertex P a.1.1) := by
          simpa [edgeEndpoint, qToXDoubleCylinderEdgeRaw,
            tannerDoubleCylinderEdgeStart] using congrArg Prod.snd hvertex
        rw [himpossible] at hmember
        simp [subdivisionBoundaryVertexMember, rxOriginalXStarVertex,
          xStarBoundaryVertexMember] at hmember
      · have hmember :=
            (subdivisionBoundaryEdgeEnd P a.1.1 S
              (qToXSubdivisionBoundaryEdge P a.1.2 a.1.1 a.2 S qEdge)).2
        rw [subdivisionBoundaryEdgeEnd_value] at hmember
        have himpossible : subdivisionEdgeEnd P a.1.1 S
              (qToXSubdivisionBoundaryEdge P a.1.2 a.1.1 a.2 S qEdge).1 =
            Sum.inl (rxOriginalXStarVertex P a.1.1) := by
          simpa [edgeEndpoint, qToXDoubleCylinderEdgeRaw,
            tannerDoubleCylinderEdgeEnd] using congrArg Prod.snd hvertex
        rw [himpossible] at hmember
        simp [subdivisionBoundaryVertexMember, rxOriginalXStarVertex,
          xStarBoundaryVertexMember] at hmember
    · let boundaryVertex := subdivisionOriginalBoundaryVertex P a.1.1 S
          (xBoundaryEdgeEnd P a.1.1
            (qToXBoundaryEdge P a.1.2 a.1.1 a.2 vertical))
      have hmember := boundaryVertex.2
      have himpossible : boundaryVertex.1 =
          Sum.inl (rxOriginalXStarVertex P a.1.1) := by
        fin_cases endpoint <;>
          simpa [boundaryVertex, edgeEndpoint, qToXDoubleCylinderEdgeRaw,
            tannerDoubleCylinderEdgeStart, tannerDoubleCylinderEdgeEnd] using
            congrArg Prod.snd hvertex
      rw [himpossible] at hmember
      simp [subdivisionBoundaryVertexMember, rxOriginalXStarVertex,
        xStarBoundaryVertexMember] at hmember
  · rcases old with ⟨oldFace, oldCopy⟩
    have howner : P.faceX oldFace = x := congrArg Sigma.fst hx
    subst x
    have hvertex :
        (oldCopy, Sum.inl
          (xStarFaceZVertex P (P.faceX oldFace) (oldFaceInXStar P oldFace))) =
          (copy, Sum.inl (rxOriginalXStarVertex P (P.faceX oldFace))) :=
      eq_of_heq (Sigma.mk.inj_iff.mp hx).2
    have hstar := Sum.inl.inj (congrArg Prod.snd hvertex)
    have raw := congrArg Subtype.val hstar
    cases raw
def rxOriginalBoundaryQXCoordinate
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    (rxReplacementPresentation P S).X :=
  ⟨x, (copy, Sum.inl ⟨Vertex.q q, by
    simpa [xStarBoundaryVertexMember, xStarVertexMember] using member⟩)⟩
def rxOriginalBoundaryZXCoordinate
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true) :
    (rxReplacementPresentation P S).X :=
  ⟨x, (copy, Sum.inl ⟨Vertex.z z, by
    simpa [xStarBoundaryVertexMember, xStarVertexMember] using member⟩)⟩
theorem subdivisionGridVertex_eq_originalQ_coordinates
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (face : XStarFace P x) (a b : Fin (S.half + 1)) (q : P.Q)
    (member : xStarVertexMember P x (Vertex.q q) = true)
    (h : subdivisionGridVertex P x S face a b =
      Sum.inl ⟨Vertex.q q, member⟩) :
    (a.1 = S.half ∧ b.1 = 0 ∧ P.faceQ face.1 0 = q) ∨
      (a.1 = 0 ∧ b.1 = S.half ∧ P.faceQ face.1 1 = q) := by
  simp only [subdivisionGridVertex] at h
  split at h <;> rename_i ha0
  · split at h <;> rename_i hb0
    · have raw := congrArg Subtype.val (Sum.inl.inj h)
      cases raw
    · split at h <;> rename_i hblast
      · right
        refine ⟨ha0, hblast, ?_⟩
        exact Vertex.q.inj (congrArg Subtype.val (Sum.inl.inj h))
      · cases h
  · split at h <;> rename_i halast
    · split at h <;> rename_i hb0
      · left
        refine ⟨halast, hb0, ?_⟩
        exact Vertex.q.inj (congrArg Subtype.val (Sum.inl.inj h))
      · split at h <;> rename_i hblast
        · have raw := congrArg Subtype.val (Sum.inl.inj h)
          cases raw
        · cases h
    · split at h <;> rename_i hb0
      · cases h
      · split at h <;> rename_i hblast <;> cases h
theorem subdivisionGridVertex_eq_originalZ_coordinates
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (face : XStarFace P x) (a b : Fin (S.half + 1)) (z : P.Z)
    (member : xStarVertexMember P x (Vertex.z z) = true)
    (h : subdivisionGridVertex P x S face a b =
      Sum.inl ⟨Vertex.z z, member⟩) :
    a.1 = S.half ∧ b.1 = S.half ∧ P.faceZ face.1 = z := by
  simp only [subdivisionGridVertex] at h
  split at h <;> rename_i ha0
  · split at h <;> rename_i hb0
    · have raw := congrArg Subtype.val (Sum.inl.inj h)
      cases raw
    · split at h <;> rename_i hblast
      · have raw := congrArg Subtype.val (Sum.inl.inj h)
        cases raw
      · cases h
  · split at h <;> rename_i halast
    · split at h <;> rename_i hb0
      · have raw := congrArg Subtype.val (Sum.inl.inj h)
        cases raw
      · split at h <;> rename_i hblast
        · refine ⟨halast, hblast, ?_⟩
          exact Vertex.z.inj (congrArg Subtype.val (Sum.inl.inj h))
        · cases h
    · split at h <;> rename_i hb0
      · cases h
      · split at h <;> rename_i hblast <;> cases h
theorem rxOriginalXBoundaryQ_incidence
    (P : TannerSquarePresentation) (x : P.X) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    P.xq x q = true := by
  change decide (∃ face : P.Face,
    xStarFaceMember P x face = true ∧
      (q = P.faceQ face 0 ∨ q = P.faceQ face 1)) = true at member
  obtain ⟨face, hx, hq | hq⟩ := of_decide_eq_true member
  · have hx' : P.faceX face = x := by
      simpa [xStarFaceMember] using hx
    simpa [hx', hq] using P.data.faceQ_xq face 0
  · have hx' : P.faceX face = x := by
      simpa [xStarFaceMember] using hx
    simpa [hx', hq] using P.data.faceQ_xq face 1
theorem rxOriginalXBoundaryQ_radialMember
    (P : TannerSquarePresentation) (x : P.X) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    xStarEdgeMember P x
      (Sum.inl ⟨(x, q), rxOriginalXBoundaryQ_incidence P x q member⟩) =
        true := by
  change decide (∃ face : P.Face,
    xStarFaceMember P x face = true ∧
      (q = P.faceQ face 0 ∨ q = P.faceQ face 1)) = true at member
  change decide (∃ face : P.Face,
    xStarFaceMember P x face = true ∧
      decide ((⟨(x, q), rxOriginalXBoundaryQ_incidence P x q member⟩ :
          XQEdge P) = faceXQEdge P face 0 ∨
        ⟨(x, q), rxOriginalXBoundaryQ_incidence P x q member⟩ =
          faceXQEdge P face 1) = true) = true
  rw [decide_eq_true_eq]
  obtain ⟨face, hx, hq | hq⟩ := of_decide_eq_true member
  · refine ⟨face, hx, ?_⟩
    rw [decide_eq_true_eq]
    left
    apply Subtype.ext
    have hx' : P.faceX face = x := by
      simpa [xStarFaceMember] using hx
    exact Prod.ext hx'.symm hq
  · refine ⟨face, hx, ?_⟩
    rw [decide_eq_true_eq]
    right
    apply Subtype.ext
    have hx' : P.faceX face = x := by
      simpa [xStarFaceMember] using hx
    exact Prod.ext hx'.symm hq
def rxOriginalXBoundaryRadialEdge
    (P : TannerSquarePresentation) (x : P.X) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    XStarEdge P x :=
  ⟨Sum.inl ⟨(x, q), rxOriginalXBoundaryQ_incidence P x q member⟩,
    rxOriginalXBoundaryQ_radialMember P x q member⟩
def rxOriginalCentralQCoordinate
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (q : P.Q) (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    (rxReplacementPresentation P S).Q :=
  Sum.inl ⟨x, Sum.inl (copy, Sum.inl
    (rxOriginalXBoundaryRadialEdge P x q member, rxRadialGridZero S))⟩
theorem rxOriginalCentralFace_q
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    let radial := rxOriginalXBoundaryRadialEdge P x q member
    let owner := A4.toTannerSquareAdmissibleV3.xRadialFaceOwner x
      ⟨(x, q), rxOriginalXBoundaryQ_incidence P x q member⟩ radial.2
    rxFaceQ P S (rxOriginalCentralFace P S x copy owner.1.1) owner.1.2 =
      rxOriginalCentralQCoordinate P S x copy q member := by
  dsimp only
  let owner := A4.toTannerSquareAdmissibleV3.xRadialFaceOwner x
    ⟨(x, q), rxOriginalXBoundaryQ_incidence P x q member⟩
      (rxOriginalXBoundaryRadialEdge P x q member).2
  change rxFaceQ P S
      (rxOriginalCentralFace P S x copy owner.1.1) owner.1.2 =
    rxOriginalCentralQCoordinate P S x copy q member
  have edgeExact := owner.2
  generalize hcorner : owner.1.2 = corner
  fin_cases corner
  all_goals rw [hcorner] at edgeExact
  · simp only [rxFaceQ, rxOriginalCentralFace, twoSelect_zero,
      localFaceQ0, localFaceQ0Edge, localFaceQ0EdgeAt,
      rxOriginalCentralCell, subdivisionFaceBoundaryEdge_zero_zero]
    simp [subdivisionHorizontalEdge, rxRadialGridZero,
      rxOriginalCentralQCoordinate, rxOriginalXBoundaryRadialEdge]
    apply congrArg (fun selected : XStarEdge P x =>
      (Sum.inl (selected, rxRadialGridZero S) : SubdivisionEdge P x S))
    simpa [owner] using edgeExact
  · simp only [rxFaceQ, rxOriginalCentralFace, twoSelect_one,
      localFaceQ1, localFaceQ1Edge, localFaceQ1EdgeAt,
      rxOriginalCentralCell, subdivisionFaceBoundaryEdge_one_zero]
    simp [subdivisionVerticalEdge, rxRadialGridZero,
      rxOriginalCentralQCoordinate, rxOriginalXBoundaryRadialEdge]
    apply congrArg (fun selected : XStarEdge P x =>
      (Sum.inl (selected, rxRadialGridZero S) : SubdivisionEdge P x S))
    simpa [owner] using edgeExact
noncomputable def rxOriginalCentralZFaceOwner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (x : P.X) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true) :
    {face : XStarFace P x // P.faceZ face.1 = z} := by
  let vertex : XStarBoundaryVertex P x := ⟨Vertex.z z, member⟩
  obtain ⟨⟨boundary, endpoint⟩, hendpoint⟩ :=
    A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2
      |>.xBoundaryIncidentEdge x vertex
  rcases boundary with ⟨raw, boundaryMember⟩
  rcases raw with impossible | edge
  · simp [xStarBoundaryEdgeMember] at boundaryMember
  · have starMember : xStarEdgeMember P x (Sum.inr edge) = true := by
      simpa [xStarBoundaryEdgeMember, xStarEdgeMember] using boundaryMember
    obtain ⟨⟨face, corner⟩, edgeExact⟩ :=
      A4.xBoundaryFaceOwner x edge starMember
    refine ⟨face, ?_⟩
    have edgeRaw : faceQZEdge P face.1 corner = edge := by
      have := congrArg Subtype.val edgeExact
      exact Sum.inr.inj this
    have faceZ : P.faceZ face.1 = edge.1.2 :=
      congrArg (fun selected : QZEdge P => selected.1.2) edgeRaw
    fin_cases endpoint
    · change BDL26TannerLocalRegularity.edgeEndpoint
          (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)
          ⟨Sum.inr edge, boundaryMember⟩ 0 = vertex at hendpoint
      rw [BDL26TannerLocalRegularity.edgeEndpoint_zero] at hendpoint
      have impossibleVertex := congrArg Subtype.val hendpoint
      cases impossibleVertex
    · change BDL26TannerLocalRegularity.edgeEndpoint
          (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)
          ⟨Sum.inr edge, boundaryMember⟩ 1 = vertex at hendpoint
      rw [BDL26TannerLocalRegularity.edgeEndpoint_one] at hendpoint
      have edgeZ : edge.1.2 = z := by
        have hraw := congrArg Subtype.val hendpoint
        change Vertex.z edge.1.2 = Vertex.z z at hraw
        exact Vertex.z.inj hraw
      exact faceZ.trans edgeZ
structure RXOriginalBoundaryOwnerData
    (P : TannerSquarePresentation) (x : P.X) where
  edge : QZEdge P
  member : xStarEdgeMember P x (Sum.inr edge) = true
  face : XStarFace P x
  corner : Two
  edgeExact : xStarFaceQZEdge P x face corner =
    ⟨Sum.inr edge, member⟩
noncomputable def rxOriginalBoundaryQRootOwnerFromIncident
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (x : P.X) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (incident : {owned : XStarBoundaryEdge P x × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)
        owned.1 owned.2 = ⟨Vertex.q q, member⟩}) :
    {owner : RXOriginalBoundaryOwnerData P x // owner.edge.1.1 = q} := by
  let vertex : XStarBoundaryVertex P x := ⟨Vertex.q q, member⟩
  obtain ⟨⟨boundary, endpoint⟩, hendpoint⟩ := incident
  rcases boundary with ⟨raw, boundaryMember⟩
  rcases raw with impossible | edge
  · simp [xStarBoundaryEdgeMember] at boundaryMember
  · have starMember : xStarEdgeMember P x (Sum.inr edge) = true := by
      simpa [xStarBoundaryEdgeMember, xStarEdgeMember] using boundaryMember
    obtain ⟨⟨face, corner⟩, edgeExact⟩ :=
      A4.xBoundaryFaceOwner x edge starMember
    refine ⟨⟨edge, starMember, face, corner, edgeExact⟩, ?_⟩
    fin_cases endpoint
    · change BDL26TannerLocalRegularity.edgeEndpoint
          (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)
          ⟨Sum.inr edge, boundaryMember⟩ 0 = vertex at hendpoint
      rw [BDL26TannerLocalRegularity.edgeEndpoint_zero] at hendpoint
      exact Vertex.q.inj (congrArg Subtype.val hendpoint)
    · change BDL26TannerLocalRegularity.edgeEndpoint
          (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)
          ⟨Sum.inr edge, boundaryMember⟩ 1 = vertex at hendpoint
      rw [BDL26TannerLocalRegularity.edgeEndpoint_one] at hendpoint
      have rawEndpoint := congrArg Subtype.val hendpoint
      cases rawEndpoint
theorem rxOriginalBoundaryQRootOwnerFromIncident_edge
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (x : P.X) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (incident : {owned : XStarBoundaryEdge P x × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)
        owned.1 owned.2 = ⟨Vertex.q q, member⟩}) :
    Sum.inr (rxOriginalBoundaryQRootOwnerFromIncident
      P A4 x q member incident).1.edge = incident.1.1.1 := by
  rcases incident with ⟨⟨⟨raw, boundaryMember⟩, endpoint⟩, hendpoint⟩
  rcases raw with impossible | edge
  · simp [xStarBoundaryEdgeMember] at boundaryMember
  · rfl
noncomputable def rxOriginalBoundaryQRootOwner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (x : P.X) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    {owner : RXOriginalBoundaryOwnerData P x // owner.edge.1.1 = q} :=
  rxOriginalBoundaryQRootOwnerFromIncident P A4 x q member
    (A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2
      |>.xBoundaryIncidentEdge x ⟨Vertex.q q, member⟩)
noncomputable def rxOriginalBoundaryZRootOwnerFromIncident
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (x : P.X) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (incident : {owned : XStarBoundaryEdge P x × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)
        owned.1 owned.2 = ⟨Vertex.z z, member⟩}) :
    {owner : RXOriginalBoundaryOwnerData P x // owner.edge.1.2 = z} := by
  let vertex : XStarBoundaryVertex P x := ⟨Vertex.z z, member⟩
  obtain ⟨⟨boundary, endpoint⟩, hendpoint⟩ :=
    incident
  rcases boundary with ⟨raw, boundaryMember⟩
  rcases raw with impossible | edge
  · simp [xStarBoundaryEdgeMember] at boundaryMember
  · have starMember : xStarEdgeMember P x (Sum.inr edge) = true := by
      simpa [xStarBoundaryEdgeMember, xStarEdgeMember] using boundaryMember
    obtain ⟨⟨face, corner⟩, edgeExact⟩ :=
      A4.xBoundaryFaceOwner x edge starMember
    refine ⟨⟨edge, starMember, face, corner, edgeExact⟩, ?_⟩
    fin_cases endpoint
    · change BDL26TannerLocalRegularity.edgeEndpoint
          (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)
          ⟨Sum.inr edge, boundaryMember⟩ 0 = vertex at hendpoint
      rw [BDL26TannerLocalRegularity.edgeEndpoint_zero] at hendpoint
      have rawEndpoint := congrArg Subtype.val hendpoint
      cases rawEndpoint
    · change BDL26TannerLocalRegularity.edgeEndpoint
          (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)
          ⟨Sum.inr edge, boundaryMember⟩ 1 = vertex at hendpoint
      rw [BDL26TannerLocalRegularity.edgeEndpoint_one] at hendpoint
      exact Vertex.z.inj (congrArg Subtype.val hendpoint)
theorem rxOriginalBoundaryZRootOwnerFromIncident_edge
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (x : P.X) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (incident : {owned : XStarBoundaryEdge P x × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)
        owned.1 owned.2 = ⟨Vertex.z z, member⟩}) :
    Sum.inr (rxOriginalBoundaryZRootOwnerFromIncident
      P A4 x z member incident).1.edge = incident.1.1.1 := by
  rcases incident with ⟨⟨⟨raw, boundaryMember⟩, endpoint⟩, hendpoint⟩
  rcases raw with impossible | edge
  · simp [xStarBoundaryEdgeMember] at boundaryMember
  · rfl
noncomputable def rxOriginalBoundaryZRootOwner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (x : P.X) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true) :
    {owner : RXOriginalBoundaryOwnerData P x // owner.edge.1.2 = z} :=
  rxOriginalBoundaryZRootOwnerFromIncident P A4 x z member
    (A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2
      |>.xBoundaryIncidentEdge x ⟨Vertex.z z, member⟩)
noncomputable def rxOriginalBoundaryQRootFace
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (x : P.X) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    XStarFace P x :=
  (rxOriginalBoundaryQRootOwner P A4 x q member).1.face
noncomputable def rxOriginalBoundaryQRootCorner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (x : P.X) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) : Two :=
  (rxOriginalBoundaryQRootOwner P A4 x q member).1.corner
theorem rxOriginalBoundaryQRootFace_q
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (x : P.X) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    P.faceQ (rxOriginalBoundaryQRootFace P A4 x q member).1
        (rxOriginalBoundaryQRootCorner P A4 x q member) = q := by
  let owner := rxOriginalBoundaryQRootOwner P A4 x q member
  have rawEdge := congrArg Subtype.val owner.1.edgeExact
  have edgeExact : faceQZEdge P owner.1.face.1 owner.1.corner =
      owner.1.edge := Sum.inr.inj rawEdge
  exact (congrArg (fun edge : QZEdge P => edge.1.1) edgeExact).trans owner.2
noncomputable def rxOriginalBoundaryZRootFace
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (x : P.X) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true) :
    XStarFace P x :=
  (rxOriginalBoundaryZRootOwner P A4 x z member).1.face
noncomputable def rxOriginalBoundaryZRootCorner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (x : P.X) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true) : Two :=
  (rxOriginalBoundaryZRootOwner P A4 x z member).1.corner
theorem rxOriginalBoundaryZRootFace_z
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (x : P.X) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true) :
    P.faceZ (rxOriginalBoundaryZRootFace P A4 x z member).1 = z := by
  let owner := rxOriginalBoundaryZRootOwner P A4 x z member
  have rawEdge := congrArg Subtype.val owner.1.edgeExact
  have edgeExact : faceQZEdge P owner.1.face.1 owner.1.corner =
      owner.1.edge := Sum.inr.inj rawEdge
  exact (congrArg (fun edge : QZEdge P => edge.1.2) edgeExact).trans owner.2
noncomputable def rxOriginalCentralZCoordinate
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true) :
    (rxReplacementPresentation P S).Z :=
  Sum.inl (Sum.inl ⟨x,
    rxOriginalCentralCell P S x copy
      (rxOriginalCentralZFaceOwner P A4 x z member).1⟩)
noncomputable def rxOriginalCentralBoundaryVertexMap
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) :
    XStarBoundaryVertex P x →
      XStarBoundaryVertex (rxReplacementPresentation P S)
        (rxOriginalCentralXCoordinate P S x copy) :=
  fun vertex => by
    classical
    rcases vertex with ⟨value, member⟩
    rcases value with impossible | q | z
    · simp [xStarBoundaryVertexMember] at member
    · let newQ := rxOriginalCentralQCoordinate P S x copy q member
      let radial := rxOriginalXBoundaryRadialEdge P x q member
      let owner := A4.toTannerSquareAdmissibleV3.xRadialFaceOwner x
        ⟨(x, q), rxOriginalXBoundaryQ_incidence P x q member⟩ radial.2
      let face := rxOriginalCentralFace P S x copy owner.1.1
      refine ⟨Vertex.q newQ, ?_⟩
      simp only [xStarBoundaryVertexMember, decide_eq_true_eq]
      change (∃ candidate : RXFace P S,
        xStarFaceMember (rxReplacementPresentation P S)
            (rxOriginalCentralXCoordinate P S x copy) candidate = true ∧
          (newQ = rxFaceQ P S candidate 0 ∨
            newQ = rxFaceQ P S candidate 1))
      refine ⟨face, ?_, ?_⟩
      · simp only [xStarFaceMember]
        rw [decide_eq_true_eq]
        change rxFaceX P S
            (rxOriginalCentralFace P S x copy owner.1.1) =
          rxOriginalCentralXCoordinate P S x copy
        exact rxOriginalCentralFace_x P S x copy owner.1.1
      · have hq : rxFaceQ P S face owner.1.2 = newQ := by
          simpa [face, owner, radial, newQ] using
            rxOriginalCentralFace_q P A4 S x copy q member
        exact rxTwoElim (motive := fun corner =>
            rxFaceQ P S face corner = newQ →
              newQ = rxFaceQ P S face 0 ∨ newQ = rxFaceQ P S face 1)
          (fun h => Or.inl h.symm) (fun h => Or.inr h.symm) owner.1.2 hq
    · let selected := rxOriginalCentralZFaceOwner P A4 x z member
      let newZ := rxOriginalCentralZCoordinate P A4 S x copy z member
      let face := rxOriginalCentralFace P S x copy selected.1
      refine ⟨Vertex.z newZ, ?_⟩
      simp only [xStarBoundaryVertexMember, decide_eq_true_eq]
      change (∃ candidate : RXFace P S,
        xStarFaceMember (rxReplacementPresentation P S)
            (rxOriginalCentralXCoordinate P S x copy) candidate = true ∧
          newZ = rxFaceZ P S candidate)
      refine ⟨face, ?_, ?_⟩
      · simp only [xStarFaceMember]
        rw [decide_eq_true_eq]
        change rxFaceX P S
            (rxOriginalCentralFace P S x copy selected.1) =
          rxOriginalCentralXCoordinate P S x copy
        exact rxOriginalCentralFace_x P S x copy selected.1
      · rfl
theorem rxOriginalCentralBoundaryOwner_q
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : QZEdge P)
    (starMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (qMember : xStarBoundaryVertexMember P x (Vertex.q edge.1.1) = true) :
    let owner := A4.xBoundaryFaceOwner x edge starMember
    rxFaceQ P S (rxOriginalCentralFace P S x copy owner.1.1) owner.1.2 =
      rxOriginalCentralQCoordinate P S x copy edge.1.1 qMember := by
  dsimp only
  let owner := A4.xBoundaryFaceOwner x edge starMember
  change rxFaceQ P S
      (rxOriginalCentralFace P S x copy owner.1.1) owner.1.2 =
    rxOriginalCentralQCoordinate P S x copy edge.1.1 qMember
  have edgeExact := owner.2
  have rawExact : faceQZEdge P owner.1.1.1 owner.1.2 = edge := by
    have := congrArg Subtype.val edgeExact
    exact Sum.inr.inj this
  have hx : P.faceX owner.1.1.1 = x := by
    simpa [xStarFaceMember] using owner.1.1.2
  have hq : P.faceQ owner.1.1.1 owner.1.2 = edge.1.1 :=
    congrArg (fun selected : QZEdge P => selected.1.1) rawExact
  generalize hcorner : owner.1.2 = corner
  fin_cases corner
  all_goals rw [hcorner] at edgeExact rawExact hq
  · simp only [rxFaceQ, rxOriginalCentralFace, twoSelect_zero,
      localFaceQ0, localFaceQ0Edge, localFaceQ0EdgeAt,
      rxOriginalCentralCell, subdivisionFaceBoundaryEdge_zero_zero]
    simp [subdivisionHorizontalEdge, rxRadialGridZero,
      rxOriginalCentralQCoordinate, rxOriginalXBoundaryRadialEdge]
    apply congrArg (fun selected : XStarEdge P x =>
      (Sum.inl (selected, rxRadialGridZero S) : SubdivisionEdge P x S))
    apply Subtype.ext
    apply congrArg Sum.inl
    apply Subtype.ext
    change (P.faceX owner.1.1.1, P.faceQ owner.1.1.1 0) =
      (x, edge.1.1)
    exact Prod.ext hx hq
  · simp only [rxFaceQ, rxOriginalCentralFace, twoSelect_one,
      localFaceQ1, localFaceQ1Edge, localFaceQ1EdgeAt,
      rxOriginalCentralCell, subdivisionFaceBoundaryEdge_one_zero]
    simp [subdivisionVerticalEdge, rxRadialGridZero,
      rxOriginalCentralQCoordinate, rxOriginalXBoundaryRadialEdge]
    apply congrArg (fun selected : XStarEdge P x =>
      (Sum.inl (selected, rxRadialGridZero S) : SubdivisionEdge P x S))
    apply Subtype.ext
    apply congrArg Sum.inl
    apply Subtype.ext
    change (P.faceX owner.1.1.1, P.faceQ owner.1.1.1 1) =
      (x, edge.1.1)
    exact Prod.ext hx hq
theorem rxOriginalCentralFace_qCoordinate
    (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (copy : Two) (face : XStarFace P x) (corner : Two) :
    let oldBoundary := xStarFaceBoundaryEdge P x face corner
    rxFaceQ P S (rxOriginalCentralFace P S x copy face) corner =
      rxOriginalCentralQCoordinate P S x copy (P.faceQ face.1 corner)
        (xBoundaryEdgeStart P x oldBoundary).2 := by
  dsimp only
  have hx : P.faceX face.1 = x := by
    simpa [xStarFaceMember] using face.2
  fin_cases corner
  · simp only [rxFaceQ, rxOriginalCentralFace, twoSelect_zero,
      localFaceQ0, localFaceQ0Edge, localFaceQ0EdgeAt,
      rxOriginalCentralCell, subdivisionFaceBoundaryEdge_zero_zero]
    simp [subdivisionHorizontalEdge, rxRadialGridZero,
      rxOriginalCentralQCoordinate, rxOriginalXBoundaryRadialEdge]
    apply congrArg (fun selected : XStarEdge P x =>
      (Sum.inl (selected, rxRadialGridZero S) : SubdivisionEdge P x S))
    apply Subtype.ext
    apply congrArg Sum.inl
    apply Subtype.ext
    exact Prod.ext hx rfl
  · simp only [rxFaceQ, rxOriginalCentralFace, twoSelect_one,
      localFaceQ1, localFaceQ1Edge, localFaceQ1EdgeAt,
      rxOriginalCentralCell, subdivisionFaceBoundaryEdge_one_zero]
    simp [subdivisionVerticalEdge, rxRadialGridZero,
      rxOriginalCentralQCoordinate, rxOriginalXBoundaryRadialEdge]
    apply congrArg (fun selected : XStarEdge P x =>
      (Sum.inl (selected, rxRadialGridZero S) : SubdivisionEdge P x S))
    apply Subtype.ext
    apply congrArg Sum.inl
    apply Subtype.ext
    exact Prod.ext hx rfl
theorem rxOriginalCentralFace_zCoordinate
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (x : P.X) (copy : Two) (face : XStarFace P x) :
    let oldBoundary := xStarFaceBoundaryEdge P x face 0
    rxOriginalCentralZCoordinate P A4 S x copy (P.faceZ face.1)
        (xBoundaryEdgeEnd P x oldBoundary).2 =
      rxFaceZ P S (rxOriginalCentralFace P S x copy face) := by
  dsimp only
  let member := (xBoundaryEdgeEnd P x
    (xStarFaceBoundaryEdge P x face 0)).2
  let selected := rxOriginalCentralZFaceOwner P A4 x (P.faceZ face.1) member
  have hxFace : P.faceX face.1 = x := by
    simpa [xStarFaceMember] using face.2
  have hxSelected : P.faceX selected.1.1 = x := by
    simpa [xStarFaceMember] using selected.1.2
  have hfaceRaw : selected.1.1 = face.1 :=
    R.faceXZ_injective (Prod.ext
      (hxSelected.trans hxFace.symm) selected.2)
  have hface : selected.1 = face := by
    apply Subtype.ext
    exact hfaceRaw
  simp only [rxOriginalCentralZCoordinate, rxOriginalCentralFace_z]
  rw [show rxOriginalCentralZFaceOwner P A4 x (P.faceZ face.1) member =
      selected from rfl, hface]
def rxOriginalCentralQTag
    (P : TannerSquarePresentation) (S : OddScale) : RX1 P S → Option P.Q
  | Sum.inl localEdge =>
      match localEdge.2 with
      | Sum.inl copyEdge =>
          match copyEdge.2 with
          | Sum.inl starSegment =>
              match starSegment.1.1 with
              | Sum.inl edge => some edge.1.2
              | Sum.inr _ => none
          | Sum.inr _ => none
      | Sum.inr _ => none
  | _ => none
def rxOriginalCentralZTag
    (P : TannerSquarePresentation) (S : OddScale) : RX2 P S → Option P.Z
  | Sum.inl (Sum.inl localFace) =>
      match localFace.2 with
      | Sum.inl copyFace => some (P.faceZ copyFace.2.1.1)
      | Sum.inr _ => none
  | _ => none
noncomputable def rxOriginalCentralBoundaryEdgeMap
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) :
    XStarBoundaryEdge P x →
      XStarBoundaryEdge (rxReplacementPresentation P S)
        (rxOriginalCentralXCoordinate P S x copy) :=
  fun boundary => by
    classical
    rcases boundary with ⟨raw, boundaryMember⟩
    rcases raw with impossible | edge
    · simp [xStarBoundaryEdgeMember] at boundaryMember
    · have starMember : xStarEdgeMember P x (Sum.inr edge) = true := by
        simpa [xStarBoundaryEdgeMember, xStarEdgeMember] using boundaryMember
      let owner := A4.xBoundaryFaceOwner x edge starMember
      let face := rxOriginalCentralFace P S x copy owner.1.1
      let newQ := rxFaceQ P S face owner.1.2
      let newZ := rxFaceZ P S face
      have incidence : (rxReplacementPresentation P S).qz newQ newZ = true := by
        apply (rxQZIncidence_eq_true_iff P S newQ newZ).2
        exact ⟨face, owner.1.2, rfl, rfl⟩
      let successor : QZEdge (rxReplacementPresentation P S) :=
        ⟨(newQ, newZ), incidence⟩
      refine ⟨Sum.inr successor, ?_⟩
      simp only [xStarBoundaryEdgeMember, decide_eq_true_eq]
      refine ⟨face, ?_, ?_⟩
      · simp only [xStarFaceMember]
        rw [decide_eq_true_eq]
        change rxFaceX P S
            (rxOriginalCentralFace P S x copy owner.1.1) =
          rxOriginalCentralXCoordinate P S x copy
        exact rxOriginalCentralFace_x P S x copy owner.1.1
      · change decide (successor = faceQZEdge (rxReplacementPresentation P S)
            face 0 ∨
          successor = faceQZEdge (rxReplacementPresentation P S) face 1) = true
        rw [decide_eq_true_eq]
        exact rxTwoElim (motive := fun corner =>
            owner.1.2 = corner →
              successor = faceQZEdge (rxReplacementPresentation P S) face 0 ∨
                successor = faceQZEdge (rxReplacementPresentation P S) face 1)
          (fun hcorner => Or.inl (by
            apply Subtype.ext
            rw [← hcorner]
            rfl))
          (fun hcorner => Or.inr (by
            apply Subtype.ext
            rw [← hcorner]
            rfl)) owner.1.2 rfl
theorem rxOriginalCentralBoundaryEdgeMap_start
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : XStarBoundaryEdge P x) :
    xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalCentralXCoordinate P S x copy)
        (rxOriginalCentralBoundaryEdgeMap P A4 S x copy edge) =
      rxOriginalCentralBoundaryVertexMap P A4 S x copy
        (xBoundaryEdgeStart P x edge) := by
  classical
  rcases edge with ⟨raw, boundaryMember⟩
  rcases raw with impossible | oldEdge
  · simp [xStarBoundaryEdgeMember] at boundaryMember
  · let retained : XStarBoundaryEdge P x :=
      ⟨Sum.inr oldEdge, boundaryMember⟩
    have starMember : xStarEdgeMember P x (Sum.inr oldEdge) = true := by
      simpa [xStarBoundaryEdgeMember, xStarEdgeMember] using boundaryMember
    have qMember : xStarBoundaryVertexMember P x
        (Vertex.q oldEdge.1.1) = true :=
      (xBoundaryEdgeStart P x retained).2
    apply Subtype.ext
    change Vertex.q _ = Vertex.q _
    apply congrArg Vertex.q
    exact rxOriginalCentralBoundaryOwner_q P A4 S x copy oldEdge
      starMember qMember
theorem rxOriginalCentralBoundaryEdgeMap_end
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : XStarBoundaryEdge P x) :
    xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalCentralXCoordinate P S x copy)
        (rxOriginalCentralBoundaryEdgeMap P A4 S x copy edge) =
      rxOriginalCentralBoundaryVertexMap P A4 S x copy
        (xBoundaryEdgeEnd P x edge) := by
  classical
  rcases edge with ⟨raw, boundaryMember⟩
  rcases raw with impossible | oldEdge
  · simp [xStarBoundaryEdgeMember] at boundaryMember
  · let retained : XStarBoundaryEdge P x :=
      ⟨Sum.inr oldEdge, boundaryMember⟩
    have starMember : xStarEdgeMember P x (Sum.inr oldEdge) = true := by
      simpa [xStarBoundaryEdgeMember, xStarEdgeMember] using boundaryMember
    have zMember : xStarBoundaryVertexMember P x
        (Vertex.z oldEdge.1.2) = true :=
      (xBoundaryEdgeEnd P x retained).2
    let owner := A4.xBoundaryFaceOwner x oldEdge starMember
    let selected := rxOriginalCentralZFaceOwner P A4 x oldEdge.1.2 zMember
    have rawExact : faceQZEdge P owner.1.1.1 owner.1.2 = oldEdge := by
      have exactStar := congrArg Subtype.val owner.2
      exact Sum.inr.inj exactStar
    have hxOwner : P.faceX owner.1.1.1 = x := by
      simpa [xStarFaceMember] using owner.1.1.2
    have hzOwner : P.faceZ owner.1.1.1 = oldEdge.1.2 :=
      congrArg (fun actual : QZEdge P => actual.1.2) rawExact
    have hxSelected : P.faceX selected.1.1 = x := by
      simpa [xStarFaceMember] using selected.1.2
    have hfaceRaw : owner.1.1.1 = selected.1.1 :=
      R.faceXZ_injective (Prod.ext
        (hxOwner.trans hxSelected.symm)
        (hzOwner.trans selected.2.symm))
    have hface : owner.1.1 = selected.1 := by
      apply Subtype.ext
      exact hfaceRaw
    apply Subtype.ext
    change Vertex.z _ = Vertex.z _
    apply congrArg Vertex.z
    simp only [rxOriginalCentralFace_z, rxOriginalCentralZCoordinate]
    rw [hface]
noncomputable def rxOriginalCentralBoundaryPathMap
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P)
    (S : OddScale) (x : P.X) (copy : Two)
    {root target : XStarBoundaryVertex P x}
    (path : UndirectedPath (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)
      root target) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalCentralXCoordinate P S x copy))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalCentralXCoordinate P S x copy))
      (rxOriginalCentralBoundaryVertexMap P A4 S x copy root)
      (rxOriginalCentralBoundaryVertexMap P A4 S x copy target) :=
  UndirectedPath.map
    (rxOriginalCentralBoundaryVertexMap P A4 S x copy)
    (rxOriginalCentralBoundaryEdgeMap P A4 S x copy)
    (rxOriginalCentralBoundaryEdgeMap_start P A4 S x copy)
    (rxOriginalCentralBoundaryEdgeMap_end P A4 R S x copy) path
theorem rxOriginalCentralBoundaryVertexMap_surjective
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P)
    (S : OddScale) (x : P.X) (copy : Two) :
    Function.Surjective
      (rxOriginalCentralBoundaryVertexMap P A4 S x copy) := by
  classical
  rintro ⟨value, member⟩
  rcases value with impossible | newQ | newZ
  · simp [xStarBoundaryVertexMember] at member
  · simp only [xStarBoundaryVertexMember, decide_eq_true_eq] at member
    change (∃ candidate : RXFace P S,
      xStarFaceMember (rxReplacementPresentation P S)
          (rxOriginalCentralXCoordinate P S x copy) candidate = true ∧
        (newQ = rxFaceQ P S candidate 0 ∨
          newQ = rxFaceQ P S candidate 1)) at member
    obtain ⟨candidate, hx, hq⟩ := member
    have hx' : rxFaceX P S candidate =
        rxOriginalCentralXCoordinate P S x copy := by
      simp only [xStarFaceMember, decide_eq_true_eq] at hx
      rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
      exact hx
    obtain ⟨face, hface⟩ :=
      rxOriginalCentralFace_cases P S x copy candidate hx'
    subst candidate
    rcases hq with hq | hq
    · let oldVertex := xBoundaryEdgeStart P x
        (xStarFaceBoundaryEdge P x face 0)
      refine ⟨oldVertex, ?_⟩
      apply Subtype.ext
      change Vertex.q _ = Vertex.q newQ
      apply congrArg Vertex.q
      exact (rxOriginalCentralFace_qCoordinate P S x copy face 0).symm.trans
        hq.symm
    · let oldVertex := xBoundaryEdgeStart P x
        (xStarFaceBoundaryEdge P x face 1)
      refine ⟨oldVertex, ?_⟩
      apply Subtype.ext
      change Vertex.q _ = Vertex.q newQ
      apply congrArg Vertex.q
      exact (rxOriginalCentralFace_qCoordinate P S x copy face 1).symm.trans
        hq.symm
  · simp only [xStarBoundaryVertexMember, decide_eq_true_eq] at member
    change (∃ candidate : RXFace P S,
      xStarFaceMember (rxReplacementPresentation P S)
          (rxOriginalCentralXCoordinate P S x copy) candidate = true ∧
        newZ = rxFaceZ P S candidate) at member
    obtain ⟨candidate, hx, hz⟩ := member
    have hx' : rxFaceX P S candidate =
        rxOriginalCentralXCoordinate P S x copy := by
      simp only [xStarFaceMember, decide_eq_true_eq] at hx
      rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
      exact hx
    obtain ⟨face, hface⟩ :=
      rxOriginalCentralFace_cases P S x copy candidate hx'
    subst candidate
    let oldVertex := xBoundaryEdgeEnd P x
      (xStarFaceBoundaryEdge P x face 0)
    refine ⟨oldVertex, ?_⟩
    apply Subtype.ext
    change Vertex.z _ = Vertex.z newZ
    apply congrArg Vertex.z
    exact (rxOriginalCentralFace_zCoordinate P A4 R S x copy face).trans
      hz.symm
theorem rxOriginalCentralQTag_member
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (x : P.X) (copy : Two) (newQ : RX1 P S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalCentralXCoordinate P S x copy) (Vertex.q newQ) = true)
    (q : P.Q) (htag : rxOriginalCentralQTag P S newQ = some q) :
    xStarBoundaryVertexMember P x (Vertex.q q) = true := by
  obtain ⟨oldVertex, himage⟩ :=
    rxOriginalCentralBoundaryVertexMap_surjective P A4 R S x copy
      ⟨Vertex.q newQ, member⟩
  rcases oldVertex with ⟨oldValue, oldMember⟩
  rcases oldValue with impossible | oldQ | oldZ
  · simp [xStarBoundaryVertexMember] at oldMember
  · have hraw := congrArg Subtype.val himage
    have hcoordinate := Vertex.q.inj hraw
    have hbase := congrArg (rxOriginalCentralQTag P S) hcoordinate
    rw [htag] at hbase
    simp [rxOriginalCentralBoundaryVertexMap, rxOriginalCentralQTag,
      rxOriginalCentralQCoordinate, rxOriginalXBoundaryRadialEdge] at hbase
    subst oldQ
    exact oldMember
  · have hraw := congrArg Subtype.val himage
    cases hraw
theorem rxOriginalCentralQTag_image
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (x : P.X) (copy : Two) (newQ : RX1 P S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalCentralXCoordinate P S x copy) (Vertex.q newQ) = true)
    (q : P.Q) (htag : rxOriginalCentralQTag P S newQ = some q)
    (qMember : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    rxOriginalCentralBoundaryVertexMap P A4 S x copy
        ⟨Vertex.q q, qMember⟩ = ⟨Vertex.q newQ, member⟩ := by
  obtain ⟨oldVertex, himage⟩ :=
    rxOriginalCentralBoundaryVertexMap_surjective P A4 R S x copy
      ⟨Vertex.q newQ, member⟩
  rcases oldVertex with ⟨oldValue, oldMember⟩
  rcases oldValue with impossible | oldQ | oldZ
  · simp [xStarBoundaryVertexMember] at oldMember
  · have hraw := congrArg Subtype.val himage
    have hcoordinate := Vertex.q.inj hraw
    have hbase := congrArg (rxOriginalCentralQTag P S) hcoordinate
    rw [htag] at hbase
    simp [rxOriginalCentralBoundaryVertexMap, rxOriginalCentralQTag,
      rxOriginalCentralQCoordinate, rxOriginalXBoundaryRadialEdge] at hbase
    subst oldQ
    have hold : (⟨Vertex.q q, oldMember⟩ : XStarBoundaryVertex P x) =
        ⟨Vertex.q q, qMember⟩ := by
      rfl
    exact hold ▸ himage
  · have hraw := congrArg Subtype.val himage
    cases hraw
theorem rxOriginalCentralZTag_member
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (x : P.X) (copy : Two) (newZ : RX2 P S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalCentralXCoordinate P S x copy) (Vertex.z newZ) = true)
    (z : P.Z) (htag : rxOriginalCentralZTag P S newZ = some z) :
    xStarBoundaryVertexMember P x (Vertex.z z) = true := by
  obtain ⟨oldVertex, himage⟩ :=
    rxOriginalCentralBoundaryVertexMap_surjective P A4 R S x copy
      ⟨Vertex.z newZ, member⟩
  rcases oldVertex with ⟨oldValue, oldMember⟩
  rcases oldValue with impossible | oldQ | oldZ
  · simp [xStarBoundaryVertexMember] at oldMember
  · have hraw := congrArg Subtype.val himage
    cases hraw
  · have hraw := congrArg Subtype.val himage
    have hcoordinate := Vertex.z.inj hraw
    have hbase := congrArg (rxOriginalCentralZTag P S) hcoordinate
    rw [htag] at hbase
    simp [rxOriginalCentralBoundaryVertexMap, rxOriginalCentralZTag,
      rxOriginalCentralZCoordinate, rxOriginalCentralCell] at hbase
    have holdZ : oldZ = z :=
      (rxOriginalCentralZFaceOwner P A4 x oldZ oldMember).2.symm.trans hbase
    subst oldZ
    exact oldMember
theorem rxOriginalCentralZTag_image
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (x : P.X) (copy : Two) (newZ : RX2 P S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalCentralXCoordinate P S x copy) (Vertex.z newZ) = true)
    (z : P.Z) (htag : rxOriginalCentralZTag P S newZ = some z)
    (zMember : xStarBoundaryVertexMember P x (Vertex.z z) = true) :
    rxOriginalCentralBoundaryVertexMap P A4 S x copy
        ⟨Vertex.z z, zMember⟩ = ⟨Vertex.z newZ, member⟩ := by
  obtain ⟨oldVertex, himage⟩ :=
    rxOriginalCentralBoundaryVertexMap_surjective P A4 R S x copy
      ⟨Vertex.z newZ, member⟩
  rcases oldVertex with ⟨oldValue, oldMember⟩
  rcases oldValue with impossible | oldQ | oldZ
  · simp [xStarBoundaryVertexMember] at oldMember
  · have hraw := congrArg Subtype.val himage
    cases hraw
  · have hraw := congrArg Subtype.val himage
    have hcoordinate := Vertex.z.inj hraw
    have hbase := congrArg (rxOriginalCentralZTag P S) hcoordinate
    rw [htag] at hbase
    simp [rxOriginalCentralBoundaryVertexMap, rxOriginalCentralZTag,
      rxOriginalCentralZCoordinate, rxOriginalCentralCell] at hbase
    have holdZ : oldZ = z :=
      (rxOriginalCentralZFaceOwner P A4 x oldZ oldMember).2.symm.trans hbase
    subst oldZ
    have hold : (⟨Vertex.z z, oldMember⟩ : XStarBoundaryVertex P x) =
        ⟨Vertex.z z, zMember⟩ := by
      rfl
    exact hold ▸ himage
theorem rxOriginalCentralQTag_ne_none
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (x : P.X) (copy : Two) (newQ : RX1 P S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalCentralXCoordinate P S x copy) (Vertex.q newQ) = true) :
    rxOriginalCentralQTag P S newQ ≠ none := by
  intro hnone
  obtain ⟨oldVertex, himage⟩ :=
    rxOriginalCentralBoundaryVertexMap_surjective P A4 R S x copy
      ⟨Vertex.q newQ, member⟩
  rcases oldVertex with ⟨oldValue, oldMember⟩
  rcases oldValue with impossible | oldQ | oldZ
  · simp [xStarBoundaryVertexMember] at oldMember
  · have hraw := congrArg Subtype.val himage
    have hcoordinate := Vertex.q.inj hraw
    have hbase := congrArg (rxOriginalCentralQTag P S) hcoordinate
    rw [hnone] at hbase
    simp [rxOriginalCentralBoundaryVertexMap, rxOriginalCentralQTag,
      rxOriginalCentralQCoordinate, rxOriginalXBoundaryRadialEdge] at hbase
  · have hraw := congrArg Subtype.val himage
    cases hraw
theorem rxOriginalCentralZTag_ne_none
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (x : P.X) (copy : Two) (newZ : RX2 P S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalCentralXCoordinate P S x copy) (Vertex.z newZ) = true) :
    rxOriginalCentralZTag P S newZ ≠ none := by
  intro hnone
  obtain ⟨oldVertex, himage⟩ :=
    rxOriginalCentralBoundaryVertexMap_surjective P A4 R S x copy
      ⟨Vertex.z newZ, member⟩
  rcases oldVertex with ⟨oldValue, oldMember⟩
  rcases oldValue with impossible | oldQ | oldZ
  · simp [xStarBoundaryVertexMember] at oldMember
  · have hraw := congrArg Subtype.val himage
    cases hraw
  · have hraw := congrArg Subtype.val himage
    have hcoordinate := Vertex.z.inj hraw
    have hbase := congrArg (rxOriginalCentralZTag P S) hcoordinate
    rw [hnone] at hbase
    simp [rxOriginalCentralBoundaryVertexMap, rxOriginalCentralZTag,
      rxOriginalCentralZCoordinate, rxOriginalCentralCell] at hbase
noncomputable def rxOriginalCentralBoundaryPathFromInputRoot
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (x : P.X) (copy : Two)
    (vertex : XStarBoundaryVertex (rxReplacementPresentation P S)
      (rxOriginalCentralXCoordinate P S x copy)) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalCentralXCoordinate P S x copy))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalCentralXCoordinate P S x copy))
      (rxOriginalCentralBoundaryVertexMap P A4 S x copy
        (A4.toTannerSquareAdmissibleV2.toTannerSquareAdmissible.xBoundaryRoot x))
      vertex := by
  let A := A4.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  rcases vertex with ⟨value, member⟩
  rcases value with impossible | newQ | newZ
  · simp [xStarBoundaryVertexMember] at member
  · match htag : rxOriginalCentralQTag P S newQ with
    | none =>
        exact (rxOriginalCentralQTag_ne_none P A4 R S x copy newQ member htag).elim
    | some q =>
        let qMember := rxOriginalCentralQTag_member
          P A4 R S x copy newQ member q htag
        let oldTarget : XStarBoundaryVertex P x := ⟨Vertex.q q, qMember⟩
        let path := rxOriginalCentralBoundaryPathMap P A4 R S x copy
          (A.xBoundaryPath x oldTarget)
        have htarget := rxOriginalCentralQTag_image
          P A4 R S x copy newQ member q htag qMember
        exact htarget ▸ path
  · match htag : rxOriginalCentralZTag P S newZ with
    | none =>
        exact (rxOriginalCentralZTag_ne_none P A4 R S x copy newZ member htag).elim
    | some z =>
        let zMember := rxOriginalCentralZTag_member
          P A4 R S x copy newZ member z htag
        let oldTarget : XStarBoundaryVertex P x := ⟨Vertex.z z, zMember⟩
        let path := rxOriginalCentralBoundaryPathMap P A4 R S x copy
          (A.xBoundaryPath x oldTarget)
        have htarget := rxOriginalCentralZTag_image
          P A4 R S x copy newZ member z htag zMember
        exact htarget ▸ path
noncomputable def rxReplacementXBoundaryPathOriginalCentral
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (x : P.X) (copy : Two)
    (vertex : XStarBoundaryVertex (rxReplacementPresentation P S)
      (rxOriginalCentralXCoordinate P S x copy)) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalCentralXCoordinate P S x copy))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalCentralXCoordinate P S x copy))
      (rxReplacementXBoundaryRoot P A4.toTannerSquareAdmissibleV3 S
        (rxOriginalCentralXCoordinate P S x copy))
      vertex := by
  let successorRoot := rxReplacementXBoundaryRoot P
    A4.toTannerSquareAdmissibleV3 S
    (rxOriginalCentralXCoordinate P S x copy)
  let rootFromInput := rxOriginalCentralBoundaryPathFromInputRoot
    P A4 R S x copy successorRoot
  let targetFromInput := rxOriginalCentralBoundaryPathFromInputRoot
    P A4 R S x copy vertex
  exact rootFromInput.reverse.append targetFromInput
def rxStarEdgeInteriorPreviousIndex (S : OddScale)
    (index : Fin (S.half - 1)) : Fin S.half :=
  ⟨index.1, by have := index.2; omega⟩
def rxStarEdgeInteriorNextIndex (S : OddScale)
    (index : Fin (S.half - 1)) : Fin S.half :=
  ⟨index.1 + 1, by have := index.2; omega⟩
def rxStarEdgeInteriorLastIndex (S : OddScale) : Fin S.half :=
  ⟨S.half - 1, by have := S.half_pos; omega⟩
def rxStarEdgeInteriorXCoordinate
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1)) : (rxReplacementPresentation P S).X :=
  ⟨x, (copy, Sum.inr (Sum.inl (edge, index)))⟩
noncomputable def rxStarEdgeInteriorOwner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (x : P.X) (edge : XStarEdge P x) :
    {owner : XStarFace P x × Two //
      match edge.1 with
      | Sum.inl _ =>
          xStarFaceXQEdge P x owner.1 owner.2 = edge
      | Sum.inr _ =>
          xStarFaceQZEdge P x owner.1 owner.2 = edge} := by
  rcases edge with ⟨raw, member⟩
  rcases raw with radial | boundary
  · exact A4.toTannerSquareAdmissibleV3.xRadialFaceOwner x radial member
  · exact A4.xBoundaryFaceOwner x boundary member
noncomputable def rxStarEdgeInteriorBeforeLocalFaceAt
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (edge : XStarEdge P x) (index : Fin (S.half - 1))
    (face : XStarFace P x) (corner : Two) : RXLocalFace P S := by
  rcases edge with ⟨raw, member⟩
  rcases raw with radial | boundary
  · exact rxTwoElim (motive := fun _ => RXLocalFace P S)
      ⟨x, Sum.inl (copy, (face,
        rxStarEdgeInteriorPreviousIndex S index, rxRadialGridZero S)), (1, 0)⟩
      ⟨x, Sum.inl (copy, (face,
        rxRadialGridZero S, rxStarEdgeInteriorPreviousIndex S index)), (0, 1)⟩
      corner
  · exact rxTwoElim (motive := fun _ => RXLocalFace P S)
      ⟨x, Sum.inl (copy, (face, rxStarEdgeInteriorLastIndex S,
        rxStarEdgeInteriorPreviousIndex S index)), (1, 1)⟩
      ⟨x, Sum.inl (copy, (face, rxStarEdgeInteriorPreviousIndex S index,
        rxStarEdgeInteriorLastIndex S)), (1, 1)⟩
      corner
noncomputable def rxStarEdgeInteriorAfterLocalFaceAt
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (edge : XStarEdge P x) (index : Fin (S.half - 1))
    (face : XStarFace P x) (corner : Two) : RXLocalFace P S := by
  rcases edge with ⟨raw, member⟩
  rcases raw with radial | boundary
  · exact rxTwoElim (motive := fun _ => RXLocalFace P S)
      ⟨x, Sum.inl (copy, (face,
        rxStarEdgeInteriorNextIndex S index, rxRadialGridZero S)), (0, 0)⟩
      ⟨x, Sum.inl (copy, (face,
        rxRadialGridZero S, rxStarEdgeInteriorNextIndex S index)), (0, 0)⟩
      corner
  · exact rxTwoElim (motive := fun _ => RXLocalFace P S)
      ⟨x, Sum.inl (copy, (face, rxStarEdgeInteriorLastIndex S,
        rxStarEdgeInteriorNextIndex S index)), (1, 0)⟩
      ⟨x, Sum.inl (copy, (face, rxStarEdgeInteriorNextIndex S index,
        rxStarEdgeInteriorLastIndex S)), (0, 1)⟩
      corner
theorem rxStarEdgeInteriorBeforeLocalFaceAt_x
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (edge : XStarEdge P x) (index : Fin (S.half - 1))
    (face : XStarFace P x) (corner : Two)
    (hedge : match edge.1 with
      | Sum.inl _ => xStarFaceXQEdge P x face corner = edge
      | Sum.inr _ => xStarFaceQZEdge P x face corner = edge) :
    localFaceX P S
        (rxStarEdgeInteriorBeforeLocalFaceAt P S x copy edge index face corner) =
      rxStarEdgeInteriorXCoordinate P S x copy edge index := by
  have hlast : S.half - 1 + 1 = S.half := by have := S.half_pos; omega
  rcases edge with ⟨raw, member⟩
  rcases raw with radial | boundary <;> fin_cases corner <;>
    simp [rxStarEdgeInteriorBeforeLocalFaceAt, rxTwoElim,
      rxStarEdgeInteriorXCoordinate, localFaceX,
      gridEndpoint, lowerGridIndex, upperGridIndex,
      rxStarEdgeInteriorPreviousIndex,
      rxStarEdgeInteriorLastIndex, rxRadialGridZero, hlast] at hedge ⊢
  all_goals exact hedge
theorem rxStarEdgeInteriorAfterLocalFaceAt_x
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (edge : XStarEdge P x) (index : Fin (S.half - 1))
    (face : XStarFace P x) (corner : Two)
    (hedge : match edge.1 with
      | Sum.inl _ => xStarFaceXQEdge P x face corner = edge
      | Sum.inr _ => xStarFaceQZEdge P x face corner = edge) :
    localFaceX P S
        (rxStarEdgeInteriorAfterLocalFaceAt P S x copy edge index face corner) =
      rxStarEdgeInteriorXCoordinate P S x copy edge index := by
  have hlast : S.half - 1 + 1 = S.half := by have := S.half_pos; omega
  rcases edge with ⟨raw, member⟩
  rcases raw with radial | boundary <;> fin_cases corner <;>
    simp [rxStarEdgeInteriorAfterLocalFaceAt, rxTwoElim,
      rxStarEdgeInteriorXCoordinate, localFaceX,
      gridEndpoint, lowerGridIndex, upperGridIndex,
      rxStarEdgeInteriorNextIndex,
      rxStarEdgeInteriorLastIndex, rxRadialGridZero, hlast] at hedge ⊢
  all_goals exact hedge
noncomputable def rxStarEdgeInteriorBeforeLocalFace
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1)) : RXLocalFace P S :=
  let owner := rxStarEdgeInteriorOwner P A4 x edge
  rxStarEdgeInteriorBeforeLocalFaceAt P S x copy edge index
    owner.1.1 owner.1.2
noncomputable def rxStarEdgeInteriorAfterLocalFace
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1)) : RXLocalFace P S :=
  let owner := rxStarEdgeInteriorOwner P A4 x edge
  rxStarEdgeInteriorAfterLocalFaceAt P S x copy edge index
    owner.1.1 owner.1.2
theorem rxStarEdgeInteriorBeforeLocalFace_x
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1)) :
    localFaceX P S
        (rxStarEdgeInteriorBeforeLocalFace P A4 S x copy edge index) =
      rxStarEdgeInteriorXCoordinate P S x copy edge index := by
  exact rxStarEdgeInteriorBeforeLocalFaceAt_x P S x copy edge index
    (rxStarEdgeInteriorOwner P A4 x edge).1.1
    (rxStarEdgeInteriorOwner P A4 x edge).1.2
    (rxStarEdgeInteriorOwner P A4 x edge).2
theorem rxStarEdgeInteriorAfterLocalFace_x
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1)) :
    localFaceX P S
        (rxStarEdgeInteriorAfterLocalFace P A4 S x copy edge index) =
      rxStarEdgeInteriorXCoordinate P S x copy edge index := by
  exact rxStarEdgeInteriorAfterLocalFaceAt_x P S x copy edge index
    (rxStarEdgeInteriorOwner P A4 x edge).1.1
    (rxStarEdgeInteriorOwner P A4 x edge).1.2
    (rxStarEdgeInteriorOwner P A4 x edge).2
noncomputable def rxStarEdgeInteriorAlongCornerAt
    {P : TannerSquarePresentation} {x : P.X}
    (edge : XStarEdge P x) (ownerCorner : Two) : Two :=
  match edge.1 with
  | Sum.inl _ => ownerCorner
  | Sum.inr _ => flipEndpoint ownerCorner
noncomputable def rxStarEdgeInteriorAcrossCornerAt
    {P : TannerSquarePresentation} {x : P.X}
    (edge : XStarEdge P x) (ownerCorner : Two) : Two :=
  flipEndpoint (rxStarEdgeInteriorAlongCornerAt edge ownerCorner)
theorem rxStarEdgeInteriorBeforeAlongQAt
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (edge : XStarEdge P x) (index : Fin (S.half - 1))
    (face : XStarFace P x) (ownerCorner : Two)
    (hedge : match edge.1 with
      | Sum.inl _ => xStarFaceXQEdge P x face ownerCorner = edge
      | Sum.inr _ => xStarFaceQZEdge P x face ownerCorner = edge) :
    localFaceQAt P S
        (rxStarEdgeInteriorBeforeLocalFaceAt P S x copy edge index
          face ownerCorner)
        (rxStarEdgeInteriorAlongCornerAt edge ownerCorner) =
      Sum.inl ⟨x, Sum.inl (copy, Sum.inl
        (edge, rxStarEdgeInteriorPreviousIndex S index))⟩ := by
  rcases edge with ⟨raw, member⟩
  rcases raw with radial | boundary
  · fin_cases ownerCorner
    · simp [rxStarEdgeInteriorBeforeLocalFaceAt,
        rxStarEdgeInteriorAlongCornerAt, rxTwoElim_zero, rxTwoElim_one, localFaceQAt,
        localFaceQ0, localFaceQ0Edge, localFaceQ0EdgeAt,
        subdivisionFaceBoundaryEdge_zero_zero] at hedge ⊢
      change Sum.inl (xStarFaceXQEdge P x face 0,
          rxStarEdgeInteriorPreviousIndex S index) =
        Sum.inl (⟨Sum.inl radial, member⟩,
          rxStarEdgeInteriorPreviousIndex S index)
      exact congrArg (fun selected : XStarEdge P x =>
        (Sum.inl (selected, rxStarEdgeInteriorPreviousIndex S index) :
          SubdivisionEdge P x S)) hedge
    · simp [rxStarEdgeInteriorBeforeLocalFaceAt,
        rxStarEdgeInteriorAlongCornerAt, rxTwoElim_zero, rxTwoElim_one, localFaceQAt,
        localFaceQ1, localFaceQ1Edge, localFaceQ1EdgeAt,
        subdivisionFaceBoundaryEdge_one_zero] at hedge ⊢
      change Sum.inl (xStarFaceXQEdge P x face 1,
          rxStarEdgeInteriorPreviousIndex S index) =
        Sum.inl (⟨Sum.inl radial, member⟩,
          rxStarEdgeInteriorPreviousIndex S index)
      exact congrArg (fun selected : XStarEdge P x =>
        (Sum.inl (selected, rxStarEdgeInteriorPreviousIndex S index) :
          SubdivisionEdge P x S)) hedge
  · fin_cases ownerCorner
    · have hlast : S.half - 1 + 1 = S.half := by
        have := S.half_pos
        omega
      simp [rxStarEdgeInteriorBeforeLocalFaceAt,
        rxStarEdgeInteriorAlongCornerAt, rxTwoElim_zero, rxTwoElim_one,
        localFaceQAt, localFaceQ1, localFaceQ1Edge,
        localFaceQ1EdgeAt,
        subdivisionFaceBoundaryEdge_one_one,
        subdivisionVerticalEdge, rxStarEdgeInteriorLastIndex,
        hlast] at hedge ⊢
      split <;> rename_i hzero
      · have hzeroValue := congrArg Fin.val hzero
        change S.half - 1 + 1 = 0 at hzeroValue
        omega
      · split <;> rename_i hboundary
        · exact congrArg (fun selected : XStarEdge P x =>
            (Sum.inl (selected, rxStarEdgeInteriorPreviousIndex S index) :
              SubdivisionEdge P x S)) hedge
        · exfalso
          apply hboundary
          change S.half - 1 + 1 = S.half
          omega
    · have hlast : S.half - 1 + 1 = S.half := by
        have := S.half_pos
        omega
      simp [rxStarEdgeInteriorBeforeLocalFaceAt,
        rxStarEdgeInteriorAlongCornerAt, rxTwoElim_zero, rxTwoElim_one,
        localFaceQAt, localFaceQ0, localFaceQ0Edge,
        localFaceQ0EdgeAt,
        subdivisionFaceBoundaryEdge_zero_one,
        subdivisionHorizontalEdge, rxStarEdgeInteriorLastIndex,
        hlast] at hedge ⊢
      split <;> rename_i hzero
      · have hzeroValue := congrArg Fin.val hzero
        change S.half - 1 + 1 = 0 at hzeroValue
        omega
      · split <;> rename_i hboundary
        · exact congrArg (fun selected : XStarEdge P x =>
            (Sum.inl (selected, rxStarEdgeInteriorPreviousIndex S index) :
              SubdivisionEdge P x S)) hedge
        · exfalso
          apply hboundary
          change S.half - 1 + 1 = S.half
          omega
theorem rxStarEdgeInteriorAfterAlongQAt
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (edge : XStarEdge P x) (index : Fin (S.half - 1))
    (face : XStarFace P x) (ownerCorner : Two)
    (hedge : match edge.1 with
      | Sum.inl _ => xStarFaceXQEdge P x face ownerCorner = edge
      | Sum.inr _ => xStarFaceQZEdge P x face ownerCorner = edge) :
    localFaceQAt P S
        (rxStarEdgeInteriorAfterLocalFaceAt P S x copy edge index
          face ownerCorner)
        (rxStarEdgeInteriorAlongCornerAt edge ownerCorner) =
      Sum.inl ⟨x, Sum.inl (copy, Sum.inl
        (edge, rxStarEdgeInteriorNextIndex S index))⟩ := by
  rcases edge with ⟨raw, member⟩
  rcases raw with radial | boundary
  · fin_cases ownerCorner
    · simp [rxStarEdgeInteriorAfterLocalFaceAt,
        rxStarEdgeInteriorAlongCornerAt, rxTwoElim_zero, rxTwoElim_one, localFaceQAt,
        localFaceQ0, localFaceQ0Edge, localFaceQ0EdgeAt,
        subdivisionFaceBoundaryEdge_zero_zero] at hedge ⊢
      change Sum.inl (xStarFaceXQEdge P x face 0,
          rxStarEdgeInteriorNextIndex S index) =
        Sum.inl (⟨Sum.inl radial, member⟩,
          rxStarEdgeInteriorNextIndex S index)
      exact congrArg (fun selected : XStarEdge P x =>
        (Sum.inl (selected, rxStarEdgeInteriorNextIndex S index) :
          SubdivisionEdge P x S)) hedge
    · simp [rxStarEdgeInteriorAfterLocalFaceAt,
        rxStarEdgeInteriorAlongCornerAt, rxTwoElim_zero, rxTwoElim_one, localFaceQAt,
        localFaceQ1, localFaceQ1Edge, localFaceQ1EdgeAt,
        subdivisionFaceBoundaryEdge_one_zero] at hedge ⊢
      change Sum.inl (xStarFaceXQEdge P x face 1,
          rxStarEdgeInteriorNextIndex S index) =
        Sum.inl (⟨Sum.inl radial, member⟩,
          rxStarEdgeInteriorNextIndex S index)
      exact congrArg (fun selected : XStarEdge P x =>
        (Sum.inl (selected, rxStarEdgeInteriorNextIndex S index) :
          SubdivisionEdge P x S)) hedge
  · fin_cases ownerCorner
    · have hlast : S.half - 1 + 1 = S.half := by
        have := S.half_pos
        omega
      simp [rxStarEdgeInteriorAfterLocalFaceAt,
        rxStarEdgeInteriorAlongCornerAt, rxTwoElim_zero, rxTwoElim_one,
        localFaceQAt, localFaceQ1, localFaceQ1Edge,
        localFaceQ1EdgeAt,
        subdivisionFaceBoundaryEdge_one_one,
        subdivisionVerticalEdge, rxStarEdgeInteriorLastIndex,
        hlast] at hedge ⊢
      split <;> rename_i hzero
      · have hzeroValue := congrArg Fin.val hzero
        change S.half - 1 + 1 = 0 at hzeroValue
        omega
      · split <;> rename_i hboundary
        · exact congrArg (fun selected : XStarEdge P x =>
            (Sum.inl (selected, rxStarEdgeInteriorNextIndex S index) :
              SubdivisionEdge P x S)) hedge
        · exfalso
          apply hboundary
          change S.half - 1 + 1 = S.half
          omega
    · have hlast : S.half - 1 + 1 = S.half := by
        have := S.half_pos
        omega
      simp [rxStarEdgeInteriorAfterLocalFaceAt,
        rxStarEdgeInteriorAlongCornerAt, rxTwoElim_zero, rxTwoElim_one,
        localFaceQAt, localFaceQ0, localFaceQ0Edge,
        localFaceQ0EdgeAt,
        subdivisionFaceBoundaryEdge_zero_one,
        subdivisionHorizontalEdge, rxStarEdgeInteriorLastIndex,
        hlast] at hedge ⊢
      split <;> rename_i hzero
      · have hzeroValue := congrArg Fin.val hzero
        change S.half - 1 + 1 = 0 at hzeroValue
        omega
      · split <;> rename_i hboundary
        · exact congrArg (fun selected : XStarEdge P x =>
            (Sum.inl (selected, rxStarEdgeInteriorNextIndex S index) :
              SubdivisionEdge P x S)) hedge
        · exfalso
          apply hboundary
          change S.half - 1 + 1 = S.half
          omega
theorem rxStarEdgeInteriorAcrossQAt
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (edge : XStarEdge P x) (index : Fin (S.half - 1))
    (face : XStarFace P x) (ownerCorner : Two) :
    localFaceQAt P S
        (rxStarEdgeInteriorBeforeLocalFaceAt P S x copy edge index
          face ownerCorner)
        (rxStarEdgeInteriorAcrossCornerAt edge ownerCorner) =
      localFaceQAt P S
        (rxStarEdgeInteriorAfterLocalFaceAt P S x copy edge index
          face ownerCorner)
        (rxStarEdgeInteriorAcrossCornerAt edge ownerCorner) := by
  rcases edge with ⟨raw, member⟩
  rcases raw with radial | boundary <;> fin_cases ownerCorner
  · simp [rxStarEdgeInteriorBeforeLocalFaceAt,
      rxStarEdgeInteriorAfterLocalFaceAt,
      rxStarEdgeInteriorAcrossCornerAt,
      rxStarEdgeInteriorAlongCornerAt, rxTwoElim_zero, rxTwoElim_one,
      localFaceQAt, localFaceQ1, localFaceQ1Edge, localFaceQ1EdgeAt,
      subdivisionFaceBoundaryEdge_one_zero,
      subdivisionFaceBoundaryEdge_one_one]
    congr 4
  · simp [rxStarEdgeInteriorBeforeLocalFaceAt,
      rxStarEdgeInteriorAfterLocalFaceAt,
      rxStarEdgeInteriorAcrossCornerAt,
      rxStarEdgeInteriorAlongCornerAt, rxTwoElim_zero, rxTwoElim_one,
      localFaceQAt, localFaceQ0, localFaceQ0Edge, localFaceQ0EdgeAt,
      subdivisionFaceBoundaryEdge_zero_zero,
      subdivisionFaceBoundaryEdge_zero_one]
    congr 4
  · simp [rxStarEdgeInteriorBeforeLocalFaceAt,
      rxStarEdgeInteriorAfterLocalFaceAt,
      rxStarEdgeInteriorAcrossCornerAt,
      rxStarEdgeInteriorAlongCornerAt, rxTwoElim_zero, rxTwoElim_one,
      localFaceQAt, localFaceQ0, localFaceQ0Edge, localFaceQ0EdgeAt,
      subdivisionFaceBoundaryEdge_zero_zero,
      subdivisionFaceBoundaryEdge_zero_one]
    congr 4
  · simp [rxStarEdgeInteriorBeforeLocalFaceAt,
      rxStarEdgeInteriorAfterLocalFaceAt,
      rxStarEdgeInteriorAcrossCornerAt,
      rxStarEdgeInteriorAlongCornerAt, rxTwoElim_zero, rxTwoElim_one,
      localFaceQAt, localFaceQ1, localFaceQ1Edge, localFaceQ1EdgeAt,
      subdivisionFaceBoundaryEdge_one_zero,
      subdivisionFaceBoundaryEdge_one_one]
    congr 4
noncomputable def rxStarEdgeInteriorBeforeXStarFace
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1)) :
    XStarFace (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy edge index) :=
  ⟨Sum.inl (rxStarEdgeInteriorBeforeLocalFace P A4 S x copy edge index), by
    simp only [xStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    exact rxStarEdgeInteriorBeforeLocalFace_x P A4 S x copy edge index⟩
noncomputable def rxStarEdgeInteriorAfterXStarFace
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1)) :
    XStarFace (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy edge index) :=
  ⟨Sum.inl (rxStarEdgeInteriorAfterLocalFace P A4 S x copy edge index), by
    simp only [xStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    exact rxStarEdgeInteriorAfterLocalFace_x P A4 S x copy edge index⟩
theorem rxStarEdgeInteriorAcrossBoundaryQEq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1)) :
    xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxStarEdgeInteriorXCoordinate P S x copy edge index)
          (rxStarEdgeInteriorBeforeXStarFace P A4 S x copy edge index)
          (rxStarEdgeInteriorAcrossCornerAt edge
            (rxStarEdgeInteriorOwner P A4 x edge).1.2)) =
      xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxStarEdgeInteriorXCoordinate P S x copy edge index)
          (rxStarEdgeInteriorAfterXStarFace P A4 S x copy edge index)
          (rxStarEdgeInteriorAcrossCornerAt edge
            (rxStarEdgeInteriorOwner P A4 x edge).1.2)) := by
  apply Subtype.ext
  exact congrArg Vertex.q (rxStarEdgeInteriorAcrossQAt P S x copy edge index
    (rxStarEdgeInteriorOwner P A4 x edge).1.1
    (rxStarEdgeInteriorOwner P A4 x edge).1.2)
noncomputable def rxStarEdgeInteriorBoundaryPathBefore
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1)) (qCorner : Two) :=
  xStarFaceBoundaryPathToQ (rxReplacementPresentation P S)
    (rxStarEdgeInteriorXCoordinate P S x copy edge index)
    (rxStarEdgeInteriorBeforeXStarFace P A4 S x copy edge index) qCorner
noncomputable def rxStarEdgeInteriorBoundaryPathAfter
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1)) (qCorner : Two) := by
  let across := rxStarEdgeInteriorAcrossCornerAt edge
    (rxStarEdgeInteriorOwner P A4 x edge).1.2
  let first := rxStarEdgeInteriorBoundaryPathBefore
    P A4 S x copy edge index across
  let bridge := (xStarFaceBoundaryPathToQ (rxReplacementPresentation P S)
    (rxStarEdgeInteriorXCoordinate P S x copy edge index)
    (rxStarEdgeInteriorAfterXStarFace P A4 S x copy edge index) across).reverse
  let last := xStarFaceBoundaryPathToQ (rxReplacementPresentation P S)
    (rxStarEdgeInteriorXCoordinate P S x copy edge index)
    (rxStarEdgeInteriorAfterXStarFace P A4 S x copy edge index) qCorner
  exact first.append
    (((rxStarEdgeInteriorAcrossBoundaryQEq P A4 S x copy edge index).symm ▸
      bridge).append last)
noncomputable def rxStarEdgeInteriorBoundaryPathToZBefore
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1)) :=
  (rxStarEdgeInteriorBoundaryPathBefore P A4 S x copy edge index 0).append
    (xStarFaceBoundaryPathToZ _ _
      (rxStarEdgeInteriorBeforeXStarFace P A4 S x copy edge index))
noncomputable def rxStarEdgeInteriorBoundaryPathToZAfter
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1)) :=
  (rxStarEdgeInteriorBoundaryPathAfter P A4 S x copy edge index 0).append
    (xStarFaceBoundaryPathToZ _ _
      (rxStarEdgeInteriorAfterXStarFace P A4 S x copy edge index))
inductive RXStarEdgeInteriorAdjacentTarget
  | beforeQ (corner : Two)
  | afterQ (corner : Two)
  | beforeZ
  | afterZ
noncomputable def rxStarEdgeInteriorAdjacentBoundaryVertex
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1)) :
    RXStarEdgeInteriorAdjacentTarget →
      XStarBoundaryVertex (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index)
  | .beforeQ qCorner =>
      xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxStarEdgeInteriorXCoordinate P S x copy edge index)
          (rxStarEdgeInteriorBeforeXStarFace P A4 S x copy edge index)
          qCorner)
  | .afterQ qCorner =>
      xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxStarEdgeInteriorXCoordinate P S x copy edge index)
          (rxStarEdgeInteriorAfterXStarFace P A4 S x copy edge index)
          qCorner)
  | .beforeZ =>
      xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxStarEdgeInteriorXCoordinate P S x copy edge index)
          (rxStarEdgeInteriorBeforeXStarFace P A4 S x copy edge index) 0)
  | .afterZ =>
      xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxStarEdgeInteriorXCoordinate P S x copy edge index)
          (rxStarEdgeInteriorAfterXStarFace P A4 S x copy edge index) 0)
noncomputable def rxStarEdgeInteriorAdjacentBoundaryPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1))
    (target : RXStarEdgeInteriorAdjacentTarget) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index))
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxStarEdgeInteriorXCoordinate P S x copy edge index)
          (rxStarEdgeInteriorBeforeXStarFace P A4 S x copy edge index) 0))
      (rxStarEdgeInteriorAdjacentBoundaryVertex P A4 S x copy edge index
        target) := by
  rcases target with beforeQ | afterQ | beforeZ | afterZ
  · exact rxStarEdgeInteriorBoundaryPathBefore
      P A4 S x copy edge index beforeQ
  · exact rxStarEdgeInteriorBoundaryPathAfter
      P A4 S x copy edge index afterQ
  · exact rxStarEdgeInteriorBoundaryPathToZBefore
      P A4 S x copy edge index
  · exact rxStarEdgeInteriorBoundaryPathToZAfter
      P A4 S x copy edge index
def rxStarEdgeInteriorBoundaryEdge
    (P : TannerSquarePresentation) (x : P.X) (edge : QZEdge P)
    (member : xStarEdgeMember P x (Sum.inr edge) = true) :
    XStarBoundaryEdge P x :=
  ⟨Sum.inr edge, by
    simpa [xStarBoundaryEdgeMember, xStarEdgeMember] using member⟩
def rxStarEdgeInteriorRectangleBefore
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) : SubdivisionBoundaryEdge P x S :=
  subdivisionOriginalBoundaryEdge P x S
    (rxStarEdgeInteriorBoundaryEdge P x edge member)
    (rxStarEdgeInteriorPreviousIndex S index)
def rxStarEdgeInteriorRectangleAfter
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) : SubdivisionBoundaryEdge P x S :=
  subdivisionOriginalBoundaryEdge P x S
    (rxStarEdgeInteriorBoundaryEdge P x edge member)
    (rxStarEdgeInteriorNextIndex S index)
def rxStarEdgeInteriorRectangleBeforeLocalFace
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) : RXLocalFace P S :=
  ⟨x, Sum.inr (rxStarEdgeInteriorRectangleBefore P S x edge member index),
    (copy, 1)⟩
def rxStarEdgeInteriorRectangleAfterLocalFace
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) : RXLocalFace P S :=
  ⟨x, Sum.inr (rxStarEdgeInteriorRectangleAfter P S x edge member index),
    (copy, 0)⟩
theorem rxStarEdgeInteriorRectangleBeforeLocalFace_x
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) :
    localFaceX P S
        (rxStarEdgeInteriorRectangleBeforeLocalFace P S x copy edge member index) =
      rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inr edge, member⟩ index := by
  have hnotlast : index.1 + 1 ≠ S.half := by
    have := index.2
    omega
  simp [rxStarEdgeInteriorRectangleBeforeLocalFace,
    rxStarEdgeInteriorRectangleBefore, rxStarEdgeInteriorBoundaryEdge,
    rxStarEdgeInteriorXCoordinate, localFaceX,
    subdivisionOriginalBoundaryEdge, subdivisionBoundaryEdgeEnd,
    subdivisionEdgeEnd, subdivisionSegmentEnd,
    rxStarEdgeInteriorPreviousIndex, hnotlast]
  apply Subtype.ext
  rfl
theorem rxStarEdgeInteriorRectangleAfterLocalFace_x
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) :
    localFaceX P S
        (rxStarEdgeInteriorRectangleAfterLocalFace P S x copy edge member index) =
      rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inr edge, member⟩ index := by
  simp [rxStarEdgeInteriorRectangleAfterLocalFace,
    rxStarEdgeInteriorRectangleAfter, rxStarEdgeInteriorBoundaryEdge,
    rxStarEdgeInteriorXCoordinate, localFaceX,
    subdivisionOriginalBoundaryEdge, subdivisionBoundaryEdgeStart,
    subdivisionEdgeStart, subdivisionSegmentStart,
    rxStarEdgeInteriorNextIndex]
  apply Subtype.ext
  rfl
def rxStarEdgeInteriorRectangleBeforeXStarFace
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) :
    XStarFace (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inr edge, member⟩ index) :=
  ⟨Sum.inl
      (rxStarEdgeInteriorRectangleBeforeLocalFace P S x copy edge member index), by
    simp only [xStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    exact rxStarEdgeInteriorRectangleBeforeLocalFace_x
      P S x copy edge member index⟩
def rxStarEdgeInteriorRectangleAfterXStarFace
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) :
    XStarFace (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inr edge, member⟩ index) :=
  ⟨Sum.inl
      (rxStarEdgeInteriorRectangleAfterLocalFace P S x copy edge member index), by
    simp only [xStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    exact rxStarEdgeInteriorRectangleAfterLocalFace_x
      P S x copy edge member index⟩
theorem rxStarEdgeInteriorRectangleBeforeQ0
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) :
    localFaceQAt P S
        (rxStarEdgeInteriorRectangleBeforeLocalFace P S x copy edge member index) 0 =
      Sum.inl ⟨x, Sum.inl (copy, Sum.inl
        (⟨Sum.inr edge, member⟩,
          rxStarEdgeInteriorPreviousIndex S index))⟩ := by
  simp [rxStarEdgeInteriorRectangleBeforeLocalFace,
    rxStarEdgeInteriorRectangleBefore, rxStarEdgeInteriorBoundaryEdge,
    localFaceQAt, localFaceQ0, localFaceQ0Edge,
    localFaceQ0EdgeAt, doubleCylinderRectangleBoundaryEdge]
  change Sum.inl (xStarBoundaryEdgeToStar P x
      ⟨Sum.inr edge, _⟩, rxStarEdgeInteriorPreviousIndex S index) =
    Sum.inl (⟨Sum.inr edge, member⟩,
      rxStarEdgeInteriorPreviousIndex S index)
  congr 2
theorem rxStarEdgeInteriorRectangleAfterQ0
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) :
    localFaceQAt P S
        (rxStarEdgeInteriorRectangleAfterLocalFace P S x copy edge member index) 0 =
      Sum.inl ⟨x, Sum.inl (copy, Sum.inl
        (⟨Sum.inr edge, member⟩,
          rxStarEdgeInteriorNextIndex S index))⟩ := by
  simp [rxStarEdgeInteriorRectangleAfterLocalFace,
    rxStarEdgeInteriorRectangleAfter, rxStarEdgeInteriorBoundaryEdge,
    localFaceQAt, localFaceQ0, localFaceQ0Edge,
    localFaceQ0EdgeAt, doubleCylinderRectangleBoundaryEdge]
  change Sum.inl (xStarBoundaryEdgeToStar P x
      ⟨Sum.inr edge, _⟩, rxStarEdgeInteriorNextIndex S index) =
    Sum.inl (⟨Sum.inr edge, member⟩,
      rxStarEdgeInteriorNextIndex S index)
  congr 2
theorem rxStarEdgeInteriorRectangleBeforeBoundaryQEq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) :
    xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy
          ⟨Sum.inr edge, member⟩ index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxStarEdgeInteriorXCoordinate P S x copy
            ⟨Sum.inr edge, member⟩ index)
          (rxStarEdgeInteriorBeforeXStarFace P A4 S x copy
            ⟨Sum.inr edge, member⟩ index)
          (rxStarEdgeInteriorAlongCornerAt ⟨Sum.inr edge, member⟩
            (rxStarEdgeInteriorOwner P A4 x
              ⟨Sum.inr edge, member⟩).1.2)) =
      xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy
          ⟨Sum.inr edge, member⟩ index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxStarEdgeInteriorXCoordinate P S x copy
            ⟨Sum.inr edge, member⟩ index)
          (rxStarEdgeInteriorRectangleBeforeXStarFace
            P S x copy edge member index) 0) := by
  apply Subtype.ext
  apply congrArg Vertex.q
  change localFaceQAt P S
      (rxStarEdgeInteriorBeforeLocalFace P A4 S x copy
        ⟨Sum.inr edge, member⟩ index)
      (rxStarEdgeInteriorAlongCornerAt ⟨Sum.inr edge, member⟩
        (rxStarEdgeInteriorOwner P A4 x
          ⟨Sum.inr edge, member⟩).1.2) =
    localFaceQAt P S
      (rxStarEdgeInteriorRectangleBeforeLocalFace
        P S x copy edge member index) 0
  exact (rxStarEdgeInteriorBeforeAlongQAt P S x copy
    ⟨Sum.inr edge, member⟩ index
    (rxStarEdgeInteriorOwner P A4 x ⟨Sum.inr edge, member⟩).1.1
    (rxStarEdgeInteriorOwner P A4 x ⟨Sum.inr edge, member⟩).1.2
    (rxStarEdgeInteriorOwner P A4 x
      ⟨Sum.inr edge, member⟩).2).trans
    (rxStarEdgeInteriorRectangleBeforeQ0
      P S x copy edge member index).symm
theorem rxStarEdgeInteriorRectangleAfterBoundaryQEq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) :
    xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy
          ⟨Sum.inr edge, member⟩ index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxStarEdgeInteriorXCoordinate P S x copy
            ⟨Sum.inr edge, member⟩ index)
          (rxStarEdgeInteriorAfterXStarFace P A4 S x copy
            ⟨Sum.inr edge, member⟩ index)
          (rxStarEdgeInteriorAlongCornerAt ⟨Sum.inr edge, member⟩
            (rxStarEdgeInteriorOwner P A4 x
              ⟨Sum.inr edge, member⟩).1.2)) =
      xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy
          ⟨Sum.inr edge, member⟩ index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxStarEdgeInteriorXCoordinate P S x copy
            ⟨Sum.inr edge, member⟩ index)
          (rxStarEdgeInteriorRectangleAfterXStarFace
            P S x copy edge member index) 0) := by
  apply Subtype.ext
  apply congrArg Vertex.q
  change localFaceQAt P S
      (rxStarEdgeInteriorAfterLocalFace P A4 S x copy
        ⟨Sum.inr edge, member⟩ index)
      (rxStarEdgeInteriorAlongCornerAt ⟨Sum.inr edge, member⟩
        (rxStarEdgeInteriorOwner P A4 x
          ⟨Sum.inr edge, member⟩).1.2) =
    localFaceQAt P S
      (rxStarEdgeInteriorRectangleAfterLocalFace
        P S x copy edge member index) 0
  exact (rxStarEdgeInteriorAfterAlongQAt P S x copy
    ⟨Sum.inr edge, member⟩ index
    (rxStarEdgeInteriorOwner P A4 x ⟨Sum.inr edge, member⟩).1.1
    (rxStarEdgeInteriorOwner P A4 x ⟨Sum.inr edge, member⟩).1.2
    (rxStarEdgeInteriorOwner P A4 x
      ⟨Sum.inr edge, member⟩).2).trans
    (rxStarEdgeInteriorRectangleAfterQ0
      P S x copy edge member index).symm
noncomputable def rxStarEdgeInteriorRectangleBoundaryPathBefore
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) (qCorner : Two) := by
  let oldEdge : XStarEdge P x := ⟨Sum.inr edge, member⟩
  let along := rxStarEdgeInteriorAlongCornerAt oldEdge
    (rxStarEdgeInteriorOwner P A4 x oldEdge).1.2
  let first := rxStarEdgeInteriorBoundaryPathBefore
    P A4 S x copy oldEdge index along
  let last := xStarFaceBoundaryPathToQ (rxReplacementPresentation P S)
    (rxStarEdgeInteriorXCoordinate P S x copy oldEdge index)
    (rxStarEdgeInteriorRectangleBeforeXStarFace
      P S x copy edge member index) qCorner
  exact first.append
    ((rxStarEdgeInteriorRectangleBeforeBoundaryQEq
      P A4 S x copy edge member index).symm ▸ last)
noncomputable def rxStarEdgeInteriorRectangleBoundaryPathAfter
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) (qCorner : Two) := by
  let oldEdge : XStarEdge P x := ⟨Sum.inr edge, member⟩
  let along := rxStarEdgeInteriorAlongCornerAt oldEdge
    (rxStarEdgeInteriorOwner P A4 x oldEdge).1.2
  let first := rxStarEdgeInteriorBoundaryPathAfter
    P A4 S x copy oldEdge index along
  let last := xStarFaceBoundaryPathToQ (rxReplacementPresentation P S)
    (rxStarEdgeInteriorXCoordinate P S x copy oldEdge index)
    (rxStarEdgeInteriorRectangleAfterXStarFace
      P S x copy edge member index) qCorner
  exact first.append
    ((rxStarEdgeInteriorRectangleAfterBoundaryQEq
      P A4 S x copy edge member index).symm ▸ last)
noncomputable def rxStarEdgeInteriorRectangleBoundaryPathToZBefore
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) :=
  (rxStarEdgeInteriorRectangleBoundaryPathBefore
    P A4 S x copy edge member index 0).append
    (xStarFaceBoundaryPathToZ _ _
      (rxStarEdgeInteriorRectangleBeforeXStarFace
        P S x copy edge member index))
noncomputable def rxStarEdgeInteriorRectangleBoundaryPathToZAfter
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) :=
  (rxStarEdgeInteriorRectangleBoundaryPathAfter
    P A4 S x copy edge member index 0).append
    (xStarFaceBoundaryPathToZ _ _
      (rxStarEdgeInteriorRectangleAfterXStarFace
        P S x copy edge member index))
inductive RXStarEdgeInteriorRectangleTarget
  | beforeQ (corner : Two)
  | afterQ (corner : Two)
  | beforeZ
  | afterZ
noncomputable def rxStarEdgeInteriorRectangleBoundaryVertex
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) :
    RXStarEdgeInteriorRectangleTarget →
      XStarBoundaryVertex (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy
          ⟨Sum.inr edge, member⟩ index)
  | .beforeQ corner =>
      xBoundaryEdgeStart (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxStarEdgeInteriorRectangleBeforeXStarFace
            P S x copy edge member index) corner)
  | .afterQ corner =>
      xBoundaryEdgeStart (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxStarEdgeInteriorRectangleAfterXStarFace
            P S x copy edge member index) corner)
  | .beforeZ =>
      xBoundaryEdgeEnd (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxStarEdgeInteriorRectangleBeforeXStarFace
            P S x copy edge member index) 0)
  | .afterZ =>
      xBoundaryEdgeEnd (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxStarEdgeInteriorRectangleAfterXStarFace
            P S x copy edge member index) 0)
noncomputable def rxStarEdgeInteriorRectangleBoundaryPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1))
    (target : RXStarEdgeInteriorRectangleTarget) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy
          ⟨Sum.inr edge, member⟩ index))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy
          ⟨Sum.inr edge, member⟩ index))
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy
          ⟨Sum.inr edge, member⟩ index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxStarEdgeInteriorXCoordinate P S x copy
            ⟨Sum.inr edge, member⟩ index)
          (rxStarEdgeInteriorBeforeXStarFace P A4 S x copy
            ⟨Sum.inr edge, member⟩ index) 0))
      (rxStarEdgeInteriorRectangleBoundaryVertex
        P S x copy edge member index target) := by
  rcases target with beforeQ | afterQ | beforeZ | afterZ
  · exact rxStarEdgeInteriorRectangleBoundaryPathBefore
      P A4 S x copy edge member index beforeQ
  · exact rxStarEdgeInteriorRectangleBoundaryPathAfter
      P A4 S x copy edge member index afterQ
  · exact rxStarEdgeInteriorRectangleBoundaryPathToZBefore
      P A4 S x copy edge member index
  · exact rxStarEdgeInteriorRectangleBoundaryPathToZAfter
      P A4 S x copy edge member index
theorem rxStarEdgeInteriorBoundaryQIncidence
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (x : P.X) (edge : QZEdge P)
    (member : xStarEdgeMember P x (Sum.inr edge) = true) :
    P.xq x edge.1.1 = true := by
  let owner := A4.xBoundaryFaceOwner x edge member
  have hfaceX : P.faceX owner.1.1.1 = x := by
    simpa [xStarFaceMember] using owner.1.1.2
  have hraw : faceQZEdge P owner.1.1.1 owner.1.2 = edge := by
    have hexact := congrArg Subtype.val owner.2
    exact Sum.inr.inj hexact
  have hfaceQ : P.faceQ owner.1.1.1 owner.1.2 = edge.1.1 :=
    congrArg (fun selected : QZEdge P => selected.1.1) hraw
  simpa [hfaceX, hfaceQ] using
    P.data.faceQ_xq owner.1.1.1 owner.1.2
def rxStarEdgeInteriorBoundaryXQEdge
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (x : P.X) (edge : QZEdge P)
    (member : xStarEdgeMember P x (Sum.inr edge) = true) : XQEdge P :=
  ⟨(x, edge.1.1),
    rxStarEdgeInteriorBoundaryQIncidence P A4 x edge member⟩
def rxStarEdgeInteriorBoundaryQStarEdge
    (P : TannerSquarePresentation) (edge : QZEdge P) :
    QStarEdge P edge.1.1 :=
  ⟨edge.1.2, edge.2⟩
def rxStarEdgeInteriorGlueBefore
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) : RXXQGlueFace P S :=
  ⟨rxStarEdgeInteriorBoundaryXQEdge P A4 x edge member,
    Sum.inl (copy,
      (rxStarEdgeInteriorBoundaryQStarEdge P edge,
        rxStarEdgeInteriorPreviousIndex S index)), 1⟩
def rxStarEdgeInteriorGlueAfter
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) : RXXQGlueFace P S :=
  ⟨rxStarEdgeInteriorBoundaryXQEdge P A4 x edge member,
    Sum.inl (copy,
      (rxStarEdgeInteriorBoundaryQStarEdge P edge,
        rxStarEdgeInteriorNextIndex S index)), 0⟩
theorem rxStarEdgeInteriorGlueBefore_x
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) :
    glueFaceX P S
        (rxStarEdgeInteriorGlueBefore P A4 S x copy edge member index) =
      rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inr edge, member⟩ index := by
  have hnotlast : index.1 + 1 ≠ S.half := by
    have := index.2
    omega
  simp [rxStarEdgeInteriorGlueBefore,
    rxStarEdgeInteriorBoundaryXQEdge,
    rxStarEdgeInteriorBoundaryQStarEdge,
    glueFaceX, qToXDoubleCylinderEdgeRaw,
    qToXSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge,
    tannerDoubleCylinderEdgeEnd, subdivisionEdgeEnd,
    subdivisionSegmentEnd, edgeEndpoint,
    rxStarEdgeInteriorPreviousIndex, rxStarEdgeInteriorXCoordinate,
    hnotlast]
  congr 3
theorem rxStarEdgeInteriorGlueAfter_x
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) :
    glueFaceX P S
        (rxStarEdgeInteriorGlueAfter P A4 S x copy edge member index) =
      rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inr edge, member⟩ index := by
  simp [rxStarEdgeInteriorGlueAfter,
    rxStarEdgeInteriorBoundaryXQEdge,
    rxStarEdgeInteriorBoundaryQStarEdge,
    glueFaceX, qToXDoubleCylinderEdgeRaw,
    qToXSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge,
    tannerDoubleCylinderEdgeStart, subdivisionEdgeStart,
    subdivisionSegmentStart, edgeEndpoint,
    rxStarEdgeInteriorNextIndex, rxStarEdgeInteriorXCoordinate]
  congr 3
def rxStarEdgeInteriorGlueBeforeXStarFace
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) :
    XStarFace (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inr edge, member⟩ index) :=
  ⟨Sum.inr (Sum.inl
      (rxStarEdgeInteriorGlueBefore P A4 S x copy edge member index)), by
    simp only [xStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    exact rxStarEdgeInteriorGlueBefore_x P A4 S x copy edge member index⟩
def rxStarEdgeInteriorGlueAfterXStarFace
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) :
    XStarFace (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inr edge, member⟩ index) :=
  ⟨Sum.inr (Sum.inl
      (rxStarEdgeInteriorGlueAfter P A4 S x copy edge member index)), by
    simp only [xStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    exact rxStarEdgeInteriorGlueAfter_x P A4 S x copy edge member index⟩
theorem rxStarEdgeInteriorGlueBeforeQ0
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) :
    glueFaceQ0 P S
        (rxStarEdgeInteriorGlueBefore P A4 S x copy edge member index) =
      Sum.inl ⟨x, Sum.inl (copy, Sum.inl
        (⟨Sum.inr edge, member⟩,
          rxStarEdgeInteriorPreviousIndex S index))⟩ := by
  simp [rxStarEdgeInteriorGlueBefore,
    rxStarEdgeInteriorBoundaryXQEdge,
    rxStarEdgeInteriorBoundaryQStarEdge,
    glueFaceQ0, qToXDoubleCylinderEdgeRaw,
    qToXSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge]
  apply Subtype.ext
  rfl
theorem rxStarEdgeInteriorGlueAfterQ0
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) :
    glueFaceQ0 P S
        (rxStarEdgeInteriorGlueAfter P A4 S x copy edge member index) =
      Sum.inl ⟨x, Sum.inl (copy, Sum.inl
        (⟨Sum.inr edge, member⟩,
          rxStarEdgeInteriorNextIndex S index))⟩ := by
  simp [rxStarEdgeInteriorGlueAfter,
    rxStarEdgeInteriorBoundaryXQEdge,
    rxStarEdgeInteriorBoundaryQStarEdge,
    glueFaceQ0, qToXDoubleCylinderEdgeRaw,
    qToXSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge]
  apply Subtype.ext
  rfl
theorem rxStarEdgeInteriorGlueBeforeBoundaryQEq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) :
    xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy
          ⟨Sum.inr edge, member⟩ index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxStarEdgeInteriorXCoordinate P S x copy
            ⟨Sum.inr edge, member⟩ index)
          (rxStarEdgeInteriorRectangleBeforeXStarFace
            P S x copy edge member index) 0) =
      xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy
          ⟨Sum.inr edge, member⟩ index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxStarEdgeInteriorXCoordinate P S x copy
            ⟨Sum.inr edge, member⟩ index)
          (rxStarEdgeInteriorGlueBeforeXStarFace
            P A4 S x copy edge member index) 0) := by
  apply Subtype.ext
  apply congrArg Vertex.q
  change localFaceQAt P S
      (rxStarEdgeInteriorRectangleBeforeLocalFace
        P S x copy edge member index) 0 =
    glueFaceQ0 P S
      (rxStarEdgeInteriorGlueBefore P A4 S x copy edge member index)
  exact (rxStarEdgeInteriorRectangleBeforeQ0
    P S x copy edge member index).trans
    (rxStarEdgeInteriorGlueBeforeQ0
      P A4 S x copy edge member index).symm
theorem rxStarEdgeInteriorGlueAfterBoundaryQEq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) :
    xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy
          ⟨Sum.inr edge, member⟩ index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxStarEdgeInteriorXCoordinate P S x copy
            ⟨Sum.inr edge, member⟩ index)
          (rxStarEdgeInteriorRectangleAfterXStarFace
            P S x copy edge member index) 0) =
      xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy
          ⟨Sum.inr edge, member⟩ index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxStarEdgeInteriorXCoordinate P S x copy
            ⟨Sum.inr edge, member⟩ index)
          (rxStarEdgeInteriorGlueAfterXStarFace
            P A4 S x copy edge member index) 0) := by
  apply Subtype.ext
  apply congrArg Vertex.q
  change localFaceQAt P S
      (rxStarEdgeInteriorRectangleAfterLocalFace
        P S x copy edge member index) 0 =
    glueFaceQ0 P S
      (rxStarEdgeInteriorGlueAfter P A4 S x copy edge member index)
  exact (rxStarEdgeInteriorRectangleAfterQ0
    P S x copy edge member index).trans
    (rxStarEdgeInteriorGlueAfterQ0
      P A4 S x copy edge member index).symm
noncomputable def rxStarEdgeInteriorGlueBoundaryPathBefore
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) (qCorner : Two) := by
  let first := rxStarEdgeInteriorRectangleBoundaryPathBefore
    P A4 S x copy edge member index 0
  let last := xStarFaceBoundaryPathToQ (rxReplacementPresentation P S)
    (rxStarEdgeInteriorXCoordinate P S x copy
      ⟨Sum.inr edge, member⟩ index)
    (rxStarEdgeInteriorGlueBeforeXStarFace
      P A4 S x copy edge member index) qCorner
  exact first.append ((rxStarEdgeInteriorGlueBeforeBoundaryQEq
    P A4 S x copy edge member index).symm ▸ last)
noncomputable def rxStarEdgeInteriorGlueBoundaryPathAfter
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) (qCorner : Two) := by
  let first := rxStarEdgeInteriorRectangleBoundaryPathAfter
    P A4 S x copy edge member index 0
  let last := xStarFaceBoundaryPathToQ (rxReplacementPresentation P S)
    (rxStarEdgeInteriorXCoordinate P S x copy
      ⟨Sum.inr edge, member⟩ index)
    (rxStarEdgeInteriorGlueAfterXStarFace
      P A4 S x copy edge member index) qCorner
  exact first.append ((rxStarEdgeInteriorGlueAfterBoundaryQEq
    P A4 S x copy edge member index).symm ▸ last)
noncomputable def rxStarEdgeInteriorGlueBoundaryPathToZBefore
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) :=
  (rxStarEdgeInteriorGlueBoundaryPathBefore
    P A4 S x copy edge member index 0).append
    (xStarFaceBoundaryPathToZ _ _
      (rxStarEdgeInteriorGlueBeforeXStarFace
        P A4 S x copy edge member index))
noncomputable def rxStarEdgeInteriorGlueBoundaryPathToZAfter
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) :=
  (rxStarEdgeInteriorGlueBoundaryPathAfter
    P A4 S x copy edge member index 0).append
    (xStarFaceBoundaryPathToZ _ _
      (rxStarEdgeInteriorGlueAfterXStarFace
        P A4 S x copy edge member index))
inductive RXStarEdgeInteriorGlueTarget
  | beforeQ (corner : Two)
  | afterQ (corner : Two)
  | beforeZ
  | afterZ
noncomputable def rxStarEdgeInteriorGlueBoundaryVertex
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) :
    RXStarEdgeInteriorGlueTarget →
      XStarBoundaryVertex (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy
          ⟨Sum.inr edge, member⟩ index)
  | .beforeQ corner =>
      xBoundaryEdgeStart (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxStarEdgeInteriorGlueBeforeXStarFace
            P A4 S x copy edge member index) corner)
  | .afterQ corner =>
      xBoundaryEdgeStart (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxStarEdgeInteriorGlueAfterXStarFace
            P A4 S x copy edge member index) corner)
  | .beforeZ =>
      xBoundaryEdgeEnd (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxStarEdgeInteriorGlueBeforeXStarFace
            P A4 S x copy edge member index) 0)
  | .afterZ =>
      xBoundaryEdgeEnd (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxStarEdgeInteriorGlueAfterXStarFace
            P A4 S x copy edge member index) 0)
noncomputable def rxStarEdgeInteriorGlueBoundaryPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1))
    (target : RXStarEdgeInteriorGlueTarget) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy
          ⟨Sum.inr edge, member⟩ index))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy
          ⟨Sum.inr edge, member⟩ index))
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy
          ⟨Sum.inr edge, member⟩ index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxStarEdgeInteriorXCoordinate P S x copy
            ⟨Sum.inr edge, member⟩ index)
          (rxStarEdgeInteriorBeforeXStarFace P A4 S x copy
            ⟨Sum.inr edge, member⟩ index) 0))
      (rxStarEdgeInteriorGlueBoundaryVertex
        P A4 S x copy edge member index target) := by
  rcases target with beforeQ | afterQ | beforeZ | afterZ
  · exact rxStarEdgeInteriorGlueBoundaryPathBefore
      P A4 S x copy edge member index beforeQ
  · exact rxStarEdgeInteriorGlueBoundaryPathAfter
      P A4 S x copy edge member index afterQ
  · exact rxStarEdgeInteriorGlueBoundaryPathToZBefore
      P A4 S x copy edge member index
  · exact rxStarEdgeInteriorGlueBoundaryPathToZAfter
      P A4 S x copy edge member index
def RXStarEdgeInteriorOuterFace
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) (candidate : RXFace P S) : Prop :=
  candidate = Sum.inl
      (rxStarEdgeInteriorRectangleBeforeLocalFace
        P S x copy edge member index) ∨
    candidate = Sum.inl
      (rxStarEdgeInteriorRectangleAfterLocalFace
        P S x copy edge member index) ∨
    candidate = Sum.inr (Sum.inl
      (rxStarEdgeInteriorGlueBefore P A4 S x copy edge member index)) ∨
    candidate = Sum.inr (Sum.inl
      (rxStarEdgeInteriorGlueAfter P A4 S x copy edge member index))
theorem rxStarEdgeInteriorLocalFace_cases
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (edge : XStarEdge P x) (index : Fin (S.half - 1))
    (candidate : RXLocalFace P S)
    (hx : localFaceX P S candidate =
      rxStarEdgeInteriorXCoordinate P S x copy edge index)
    (hsmall : ∃ copyFace : Two × SubdivisionFace P candidate.1 S,
      candidate.2.1 = Sum.inl copyFace) :
    ∃ face : XStarFace P x, ∃ corner : Two,
      (match edge.1 with
        | Sum.inl _ => xStarFaceXQEdge P x face corner = edge
        | Sum.inr _ => xStarFaceQZEdge P x face corner = edge) ∧
      (candidate = rxStarEdgeInteriorBeforeLocalFaceAt
          P S x copy edge index face corner ∨
        candidate = rxStarEdgeInteriorAfterLocalFaceAt
          P S x copy edge index face corner) := by
  classical
  rcases candidate with ⟨oldX, localCell, material⟩
  rcases localCell with copyFace | rectangle
  · rcases copyFace with ⟨candidateCopy, small⟩
    rcases small with ⟨candidateFace, column, row⟩
    rcases material with ⟨first, second⟩
    have howner : oldX = x := congrArg Sigma.fst hx
    subst oldX
    have hvertex :
        (candidateCopy,
          subdivisionGridVertex P x S candidateFace
            (gridEndpoint column first) (gridEndpoint row second)) =
          (copy, Sum.inr (Sum.inl (edge, index))) :=
      eq_of_heq (Sigma.mk.inj_iff.mp hx).2
    have hcopy : candidateCopy = copy := congrArg Prod.fst hvertex
    subst candidateCopy
    have hgrid : subdivisionGridVertex P x S candidateFace
        (gridEndpoint column first) (gridEndpoint row second) =
        Sum.inr (Sum.inl (edge, index)) := congrArg Prod.snd hvertex
    rcases subdivisionGridVertex_eq_edgeInterior_coordinates
        P x S candidateFace (gridEndpoint column first)
          (gridEndpoint row second) edge index hgrid with
      hleft | hright | hbottom | htop
    · rcases hleft with ⟨hedge, ha, hb⟩
      fin_cases first
      · fin_cases second
        · refine ⟨candidateFace, 1, ?_, Or.inr ?_⟩
          · rcases edge with ⟨raw, edgeMember⟩
            rcases raw with radial | boundary
            · exact hedge.symm
            · cases hedge
          · have hcolumn : column = rxRadialGridZero S := by
              apply Fin.ext
              simpa [gridEndpoint, lowerGridIndex, rxRadialGridZero] using ha
            have hrow : row = rxStarEdgeInteriorNextIndex S index := by
              apply Fin.ext
              simpa [gridEndpoint, lowerGridIndex,
                rxStarEdgeInteriorNextIndex] using hb
            rw [hcolumn, hrow]
            rw [hedge]
            rfl
        · refine ⟨candidateFace, 1, ?_, Or.inl ?_⟩
          · rcases edge with ⟨raw, edgeMember⟩
            rcases raw with radial | boundary
            · exact hedge.symm
            · cases hedge
          · have hcolumn : column = rxRadialGridZero S := by
              apply Fin.ext
              simpa [gridEndpoint, lowerGridIndex, rxRadialGridZero] using ha
            have hrow : row = rxStarEdgeInteriorPreviousIndex S index := by
              apply Fin.ext
              change row.1 = index.1
              have := hb
              simp [gridEndpoint, upperGridIndex] at this
              omega
            rw [hcolumn, hrow]
            rw [hedge]
            rfl
      · have := ha
        simp [gridEndpoint, upperGridIndex] at this
    · rcases hright with ⟨hedge, ha, hb⟩
      fin_cases first
      · have hhalf := S.half_pos
        have := ha
        simp [gridEndpoint, lowerGridIndex] at this
        omega
      · fin_cases second
        · refine ⟨candidateFace, 0, ?_, Or.inr ?_⟩
          · rcases edge with ⟨raw, edgeMember⟩
            rcases raw with radial | boundary
            · cases hedge
            · exact hedge.symm
          · have hcolumn : column = rxStarEdgeInteriorLastIndex S := by
              apply Fin.ext
              change column.1 = S.half - 1
              have := ha
              simp [gridEndpoint, upperGridIndex] at this
              omega
            have hrow : row = rxStarEdgeInteriorNextIndex S index := by
              apply Fin.ext
              simpa [gridEndpoint, lowerGridIndex,
                rxStarEdgeInteriorNextIndex] using hb
            rw [hcolumn, hrow]
            rw [hedge]
            rfl
        · refine ⟨candidateFace, 0, ?_, Or.inl ?_⟩
          · rcases edge with ⟨raw, edgeMember⟩
            rcases raw with radial | boundary
            · cases hedge
            · exact hedge.symm
          · have hcolumn : column = rxStarEdgeInteriorLastIndex S := by
              apply Fin.ext
              change column.1 = S.half - 1
              have := ha
              simp [gridEndpoint, upperGridIndex] at this
              omega
            have hrow : row = rxStarEdgeInteriorPreviousIndex S index := by
              apply Fin.ext
              change row.1 = index.1
              have := hb
              simp [gridEndpoint, upperGridIndex] at this
              omega
            rw [hcolumn, hrow]
            rw [hedge]
            rfl
    · rcases hbottom with ⟨hedge, ha, hb⟩
      fin_cases second
      · fin_cases first
        · refine ⟨candidateFace, 0, ?_, Or.inr ?_⟩
          · rcases edge with ⟨raw, edgeMember⟩
            rcases raw with radial | boundary
            · exact hedge.symm
            · cases hedge
          · have hcolumn : column = rxStarEdgeInteriorNextIndex S index := by
              apply Fin.ext
              simpa [gridEndpoint, lowerGridIndex,
                rxStarEdgeInteriorNextIndex] using ha
            have hrow : row = rxRadialGridZero S := by
              apply Fin.ext
              simpa [gridEndpoint, lowerGridIndex, rxRadialGridZero] using hb
            rw [hcolumn, hrow]
            rw [hedge]
            rfl
        · refine ⟨candidateFace, 0, ?_, Or.inl ?_⟩
          · rcases edge with ⟨raw, edgeMember⟩
            rcases raw with radial | boundary
            · exact hedge.symm
            · cases hedge
          · have hcolumn : column = rxStarEdgeInteriorPreviousIndex S index := by
              apply Fin.ext
              change column.1 = index.1
              have := ha
              simp [gridEndpoint, upperGridIndex] at this
              omega
            have hrow : row = rxRadialGridZero S := by
              apply Fin.ext
              simpa [gridEndpoint, lowerGridIndex, rxRadialGridZero] using hb
            rw [hcolumn, hrow]
            rw [hedge]
            rfl
      · have := hb
        simp [gridEndpoint, upperGridIndex] at this
    · rcases htop with ⟨hedge, ha, hb⟩
      fin_cases second
      · have hhalf := S.half_pos
        have := hb
        simp [gridEndpoint, lowerGridIndex] at this
        omega
      · fin_cases first
        · refine ⟨candidateFace, 1, ?_, Or.inr ?_⟩
          · rcases edge with ⟨raw, edgeMember⟩
            rcases raw with radial | boundary
            · cases hedge
            · exact hedge.symm
          · have hcolumn : column = rxStarEdgeInteriorNextIndex S index := by
              apply Fin.ext
              simpa [gridEndpoint, lowerGridIndex,
                rxStarEdgeInteriorNextIndex] using ha
            have hrow : row = rxStarEdgeInteriorLastIndex S := by
              apply Fin.ext
              change row.1 = S.half - 1
              have := hb
              simp [gridEndpoint, upperGridIndex] at this
              omega
            rw [hcolumn, hrow]
            rw [hedge]
            rfl
        · refine ⟨candidateFace, 1, ?_, Or.inl ?_⟩
          · rcases edge with ⟨raw, edgeMember⟩
            rcases raw with radial | boundary
            · cases hedge
            · exact hedge.symm
          · have hcolumn : column = rxStarEdgeInteriorPreviousIndex S index := by
              apply Fin.ext
              change column.1 = index.1
              have := ha
              simp [gridEndpoint, upperGridIndex] at this
              omega
            have hrow : row = rxStarEdgeInteriorLastIndex S := by
              apply Fin.ext
              change row.1 = S.half - 1
              have := hb
              simp [gridEndpoint, upperGridIndex] at this
              omega
            rw [hcolumn, hrow]
            rw [hedge]
            rfl
  · rcases hsmall with ⟨copyFace, hcopyFace⟩
    cases hcopyFace
theorem rxStarEdgeInteriorRectangleFace_cases
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1))
    (rectangle : SubdivisionBoundaryEdge P x S) (material : Two × Two)
    (hx : localFaceX P S ⟨x, Sum.inr rectangle, material⟩ =
      rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inr edge, member⟩ index) :
    (⟨x, Sum.inr rectangle, material⟩ : RXLocalFace P S) =
        rxStarEdgeInteriorRectangleBeforeLocalFace
          P S x copy edge member index ∨
      (⟨x, Sum.inr rectangle, material⟩ : RXLocalFace P S) =
        rxStarEdgeInteriorRectangleAfterLocalFace
          P S x copy edge member index := by
  rcases material with ⟨materialCopy, endpoint⟩
  have hvertex : doubleCylinderRectangleCorner P x S rectangle
      (materialCopy, endpoint) =
      (copy, Sum.inr (Sum.inl (⟨Sum.inr edge, member⟩, index))) :=
    eq_of_heq (Sigma.mk.inj_iff.mp hx).2
  have hcopy : materialCopy = copy := congrArg Prod.fst hvertex
  subst materialCopy
  rcases rectangle with ⟨raw, boundaryMember⟩
  rcases raw with original | interior
  · rcases original with ⟨starEdge, segment⟩
    fin_cases endpoint
    · right
      have hsubdivision := congrArg Prod.snd hvertex
      by_cases hzero : segment.1 = 0
      · have himpossible :
            (Sum.inl (xStarEdgeStart P x starEdge) :
              SubdivisionVertex P x S) =
              Sum.inr (Sum.inl
                ((⟨Sum.inr edge, member⟩ : XStarEdge P x), index)) := by
          simpa [doubleCylinderRectangleCorner,
            subdivisionBoundaryEdgeStart, subdivisionEdgeStart,
            subdivisionSegmentStart, hzero] using hsubdivision
        cases himpossible
      · have hpair :
            (starEdge, ⟨segment.1 - 1, by have := segment.2; omega⟩) =
              ((⟨Sum.inr edge, member⟩ : XStarEdge P x), index) := by
          simpa [doubleCylinderRectangleCorner,
            subdivisionBoundaryEdgeStart, subdivisionEdgeStart,
            subdivisionSegmentStart, hzero] using hsubdivision
        have hedge : starEdge = ⟨Sum.inr edge, member⟩ :=
          congrArg Prod.fst hpair
        have hsegment : segment = rxStarEdgeInteriorNextIndex S index := by
          apply Fin.ext
          have hindex := congrArg (fun pair => pair.2.1) hpair
          simp only at hindex
          change segment.1 - 1 = index.1 at hindex
          simp [rxStarEdgeInteriorNextIndex]
          omega
        subst starEdge
        rw [hsegment]
        rfl
    · left
      have hsubdivision := congrArg Prod.snd hvertex
      by_cases hlast : segment.1 + 1 = S.half
      · have himpossible :
            (Sum.inl (xStarEdgeEnd P x starEdge) :
              SubdivisionVertex P x S) =
              Sum.inr (Sum.inl
                ((⟨Sum.inr edge, member⟩ : XStarEdge P x), index)) := by
          simpa [doubleCylinderRectangleCorner,
            subdivisionBoundaryEdgeEnd, subdivisionEdgeEnd,
            subdivisionSegmentEnd, hlast] using hsubdivision
        cases himpossible
      · have hpair :
            (starEdge, ⟨segment.1, by have := segment.2; omega⟩) =
            ((⟨Sum.inr edge, member⟩ : XStarEdge P x), index) := by
          simpa [doubleCylinderRectangleCorner,
            subdivisionBoundaryEdgeEnd, subdivisionEdgeEnd,
            subdivisionSegmentEnd, hlast] using hsubdivision
        have hedge : starEdge = ⟨Sum.inr edge, member⟩ :=
          congrArg Prod.fst hpair
        have hsegment : segment =
            rxStarEdgeInteriorPreviousIndex S index := by
          apply Fin.ext
          exact congrArg (fun pair => pair.2.1) hpair
        subst starEdge
        rw [hsegment]
        rfl
  · simp [subdivisionBoundaryEdgeMember] at boundaryMember
theorem rxStarEdgeInteriorGlueFace_cases
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) (candidate : RXXQGlueFace P S)
    (hx : glueFaceX P S candidate =
      rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inr edge, member⟩ index) :
    candidate = rxStarEdgeInteriorGlueBefore
        P A4 S x copy edge member index ∨
      candidate = rxStarEdgeInteriorGlueAfter
        P A4 S x copy edge member index := by
  rcases candidate with ⟨⟨⟨oldX, q⟩, hxq⟩, qEdge, endpoint⟩
  have howner : oldX = x := congrArg Sigma.fst hx
  subst oldX
  have hvertex : edgeEndpoint
        (tannerDoubleCylinderEdgeStart P x S)
        (tannerDoubleCylinderEdgeEnd P x S)
        (qToXDoubleCylinderEdgeRaw P q x hxq S qEdge) endpoint =
      (copy, Sum.inr (Sum.inl
        ((⟨Sum.inr edge, member⟩ : XStarEdge P x), index))) :=
    eq_of_heq (Sigma.mk.inj_iff.mp hx).2
  rcases qEdge with copyEdge | vertical
  · rcases copyEdge with ⟨edgeCopy, qSegment⟩
    rcases qSegment with ⟨qStarEdge, segment⟩
    fin_cases endpoint
    · right
      have hcopy : edgeCopy = copy := by
        simpa [edgeEndpoint, qToXDoubleCylinderEdgeRaw,
          tannerDoubleCylinderEdgeStart] using congrArg Prod.fst hvertex
      subst edgeCopy
      have hsubdivision := congrArg Prod.snd hvertex
      by_cases hzero : segment.1 = 0
      · have himpossible :
            (Sum.inl (xStarEdgeStart P x
              (xStarBoundaryEdgeToStar P x
                (qToXBoundaryEdge P q x hxq qStarEdge))) :
              SubdivisionVertex P x S) =
            Sum.inr (Sum.inl
              ((⟨Sum.inr edge, member⟩ : XStarEdge P x), index)) := by
          simpa [edgeEndpoint, qToXDoubleCylinderEdgeRaw,
            qToXSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge,
            tannerDoubleCylinderEdgeStart, subdivisionEdgeStart,
            subdivisionSegmentStart, hzero] using hsubdivision
        cases himpossible
      · have hpair :
            (xStarBoundaryEdgeToStar P x
                (qToXBoundaryEdge P q x hxq qStarEdge),
              ⟨segment.1 - 1, by have := segment.2; omega⟩) =
            ((⟨Sum.inr edge, member⟩ : XStarEdge P x), index) := by
          simpa [edgeEndpoint, qToXDoubleCylinderEdgeRaw,
            qToXSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge,
            tannerDoubleCylinderEdgeStart, subdivisionEdgeStart,
            subdivisionSegmentStart, hzero] using hsubdivision
        have hmapped : xStarBoundaryEdgeToStar P x
            (qToXBoundaryEdge P q x hxq qStarEdge) =
              ⟨Sum.inr edge, member⟩ := congrArg Prod.fst hpair
        have hraw := congrArg Subtype.val hmapped
        have hqz : (⟨(q, qStarEdge.1), qStarEdge.2⟩ : QZEdge P) = edge :=
          Sum.inr.inj hraw
        have hq : q = edge.1.1 :=
          congrArg (fun selected : QZEdge P => selected.1.1) hqz
        subst q
        have hqStar : qStarEdge =
            rxStarEdgeInteriorBoundaryQStarEdge P edge := by
          apply Subtype.ext
          exact congrArg (fun selected : QZEdge P => selected.1.2) hqz
        have hsegment : segment = rxStarEdgeInteriorNextIndex S index := by
          apply Fin.ext
          have hindex := congrArg (fun pair => pair.2.1) hpair
          change segment.1 - 1 = index.1 at hindex
          simp [rxStarEdgeInteriorNextIndex]
          omega
        have ha :
            (⟨(x, edge.1.1), hxq⟩ : XQEdge P) =
              rxStarEdgeInteriorBoundaryXQEdge P A4 x edge member := by
          apply Subtype.ext
          rfl
        apply Sigma.ext
        · exact ha
        · apply heq_of_eq
          rw [hqStar, hsegment]
          rfl
    · left
      have hcopy : edgeCopy = copy := by
        simpa [edgeEndpoint, qToXDoubleCylinderEdgeRaw,
          tannerDoubleCylinderEdgeEnd] using congrArg Prod.fst hvertex
      subst edgeCopy
      have hsubdivision := congrArg Prod.snd hvertex
      by_cases hlast : segment.1 + 1 = S.half
      · have himpossible :
            (Sum.inl (xStarEdgeEnd P x
              (xStarBoundaryEdgeToStar P x
                (qToXBoundaryEdge P q x hxq qStarEdge))) :
              SubdivisionVertex P x S) =
            Sum.inr (Sum.inl
              ((⟨Sum.inr edge, member⟩ : XStarEdge P x), index)) := by
          simpa [edgeEndpoint, qToXDoubleCylinderEdgeRaw,
            qToXSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge,
            tannerDoubleCylinderEdgeEnd, subdivisionEdgeEnd,
            subdivisionSegmentEnd, hlast] using hsubdivision
        cases himpossible
      · have hpair :
            (xStarBoundaryEdgeToStar P x
                (qToXBoundaryEdge P q x hxq qStarEdge),
              ⟨segment.1, by have := segment.2; omega⟩) =
            ((⟨Sum.inr edge, member⟩ : XStarEdge P x), index) := by
          simpa [edgeEndpoint, qToXDoubleCylinderEdgeRaw,
            qToXSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge,
            tannerDoubleCylinderEdgeEnd, subdivisionEdgeEnd,
            subdivisionSegmentEnd, hlast] using hsubdivision
        have hmapped : xStarBoundaryEdgeToStar P x
            (qToXBoundaryEdge P q x hxq qStarEdge) =
              ⟨Sum.inr edge, member⟩ := congrArg Prod.fst hpair
        have hraw := congrArg Subtype.val hmapped
        have hqz : (⟨(q, qStarEdge.1), qStarEdge.2⟩ : QZEdge P) = edge :=
          Sum.inr.inj hraw
        have hq : q = edge.1.1 :=
          congrArg (fun selected : QZEdge P => selected.1.1) hqz
        subst q
        have hqStar : qStarEdge =
            rxStarEdgeInteriorBoundaryQStarEdge P edge := by
          apply Subtype.ext
          exact congrArg (fun selected : QZEdge P => selected.1.2) hqz
        have hsegment : segment =
            rxStarEdgeInteriorPreviousIndex S index := by
          apply Fin.ext
          exact congrArg (fun pair => pair.2.1) hpair
        have ha :
            (⟨(x, edge.1.1), hxq⟩ : XQEdge P) =
              rxStarEdgeInteriorBoundaryXQEdge P A4 x edge member := by
          apply Subtype.ext
          rfl
        apply Sigma.ext
        · exact ha
        · apply heq_of_eq
          rw [hqStar, hsegment]
          rfl
  · have hsubdivision := congrArg Prod.snd hvertex
    fin_cases endpoint <;>
      simp [edgeEndpoint, qToXDoubleCylinderEdgeRaw,
        tannerDoubleCylinderEdgeStart, tannerDoubleCylinderEdgeEnd,
        subdivisionOriginalBoundaryVertex] at hsubdivision
def RXStarEdgeInteriorIncidentFace
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1)) (candidate : RXFace P S) : Prop :=
  (∃ face : XStarFace P x, ∃ corner : Two,
      (match edge.1 with
        | Sum.inl _ => xStarFaceXQEdge P x face corner = edge
        | Sum.inr _ => xStarFaceQZEdge P x face corner = edge) ∧
      (candidate = Sum.inl (rxStarEdgeInteriorBeforeLocalFaceAt
          P S x copy edge index face corner) ∨
        candidate = Sum.inl (rxStarEdgeInteriorAfterLocalFaceAt
          P S x copy edge index face corner))) ∨
    (∃ boundary : QZEdge P,
      ∃ member : xStarEdgeMember P x (Sum.inr boundary) = true,
        edge = ⟨Sum.inr boundary, member⟩ ∧
          RXStarEdgeInteriorOuterFace
            P A4 S x copy boundary member index candidate)
theorem rxStarEdgeInteriorIncidentFace_cases
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1)) (candidate : RXFace P S)
    (hx : rxFaceX P S candidate =
      rxStarEdgeInteriorXCoordinate P S x copy edge index) :
    RXStarEdgeInteriorIncidentFace
      P A4 S x copy edge index candidate := by
  classical
  rcases candidate with candidateLocal | glue | old
  · rcases candidateLocal with ⟨oldX, localCell, material⟩
    rcases localCell with copyFace | rectangle
    · have howner : oldX = x := by
        simpa [rxFaceX, localFaceX, rxStarEdgeInteriorXCoordinate] using congrArg Sigma.fst hx
      subst oldX
      left
      rcases rxStarEdgeInteriorLocalFace_cases P S x copy edge index
          ⟨x, Sum.inl copyFace, material⟩ (by simpa [rxFaceX] using hx)
          ⟨copyFace, rfl⟩ with ⟨face, corner, hedge, hbefore | hafter⟩
      · exact ⟨face, corner, hedge, Or.inl (congrArg Sum.inl hbefore)⟩
      · exact ⟨face, corner, hedge, Or.inr (congrArg Sum.inl hafter)⟩
    · have howner : oldX = x := by
        simpa [rxFaceX, localFaceX, rxStarEdgeInteriorXCoordinate] using congrArg Sigma.fst hx
      subst oldX
      rcases edge with ⟨rawEdge, edgeMember⟩
      rcases rawEdge with radial | boundary
      · have hvertex : doubleCylinderRectangleCorner P x S rectangle material =
            (copy, Sum.inr (Sum.inl
              ((⟨Sum.inl radial, edgeMember⟩ : XStarEdge P x), index))) :=
          eq_of_heq (Sigma.mk.inj_iff.mp hx).2
        rcases material with ⟨materialCopy, endpoint⟩
        have hsubdivision := congrArg Prod.snd hvertex
        fin_cases endpoint
        · have hmember := (subdivisionBoundaryEdgeStart P x S rectangle).2
          rw [subdivisionBoundaryEdgeStart_value] at hmember
          have hvalue : subdivisionEdgeStart P x S rectangle.1 =
              Sum.inr (Sum.inl
                ((⟨Sum.inl radial, edgeMember⟩ : XStarEdge P x), index)) := by
            simpa [doubleCylinderRectangleCorner] using hsubdivision
          rw [hvalue] at hmember
          simp [subdivisionBoundaryVertexMember,
            xStarBoundaryEdgeMember] at hmember
        · have hmember := (subdivisionBoundaryEdgeEnd P x S rectangle).2
          rw [subdivisionBoundaryEdgeEnd_value] at hmember
          have hvalue : subdivisionEdgeEnd P x S rectangle.1 =
              Sum.inr (Sum.inl
                ((⟨Sum.inl radial, edgeMember⟩ : XStarEdge P x), index)) := by
            simpa [doubleCylinderRectangleCorner] using hsubdivision
          rw [hvalue] at hmember
          simp [subdivisionBoundaryVertexMember,
            xStarBoundaryEdgeMember] at hmember
      · right
        refine ⟨boundary, edgeMember, rfl, ?_⟩
        rcases rxStarEdgeInteriorRectangleFace_cases
            P S x copy boundary edgeMember index rectangle material
            (by simpa [rxFaceX] using hx) with hbefore | hafter
        · left; exact congrArg Sum.inl hbefore
        · right; left; exact congrArg Sum.inl hafter
  · rcases edge with ⟨rawEdge, edgeMember⟩
    rcases rawEdge with radial | boundary
    · rcases glue with ⟨a, qEdge, endpoint⟩
      have howner : a.1.1 = x := congrArg Sigma.fst hx
      subst x
      have hvertex : edgeEndpoint
            (tannerDoubleCylinderEdgeStart P a.1.1 S)
            (tannerDoubleCylinderEdgeEnd P a.1.1 S)
            (qToXDoubleCylinderEdgeRaw P a.1.2 a.1.1 a.2 S qEdge) endpoint =
          (copy, Sum.inr (Sum.inl
            ((⟨Sum.inl radial, edgeMember⟩ :
              XStarEdge P a.1.1), index))) :=
        eq_of_heq (Sigma.mk.inj_iff.mp hx).2
      rcases qEdge with copyEdge | vertical
      · rcases copyEdge with ⟨edgeCopy, qSegment⟩
        have hsubdivision := congrArg Prod.snd hvertex
        fin_cases endpoint
        · have hmember :=
              (subdivisionBoundaryEdgeStart P a.1.1 S
                (qToXSubdivisionBoundaryEdge P a.1.2 a.1.1 a.2 S qSegment)).2
          rw [subdivisionBoundaryEdgeStart_value] at hmember
          have hvalue : subdivisionEdgeStart P a.1.1 S
                (qToXSubdivisionBoundaryEdge P a.1.2 a.1.1 a.2 S qSegment).1 =
              Sum.inr (Sum.inl
                ((⟨Sum.inl radial, edgeMember⟩ :
                  XStarEdge P a.1.1), index)) := by
            simpa [edgeEndpoint, qToXDoubleCylinderEdgeRaw,
              tannerDoubleCylinderEdgeStart] using hsubdivision
          rw [hvalue] at hmember
          simp [subdivisionBoundaryVertexMember,
            xStarBoundaryEdgeMember] at hmember
        · have hmember :=
              (subdivisionBoundaryEdgeEnd P a.1.1 S
                (qToXSubdivisionBoundaryEdge P a.1.2 a.1.1 a.2 S qSegment)).2
          rw [subdivisionBoundaryEdgeEnd_value] at hmember
          have hvalue : subdivisionEdgeEnd P a.1.1 S
                (qToXSubdivisionBoundaryEdge P a.1.2 a.1.1 a.2 S qSegment).1 =
              Sum.inr (Sum.inl
                ((⟨Sum.inl radial, edgeMember⟩ :
                  XStarEdge P a.1.1), index)) := by
            simpa [edgeEndpoint, qToXDoubleCylinderEdgeRaw,
              tannerDoubleCylinderEdgeEnd] using hsubdivision
          rw [hvalue] at hmember
          simp [subdivisionBoundaryVertexMember,
            xStarBoundaryEdgeMember] at hmember
      · have hsubdivision := congrArg Prod.snd hvertex
        fin_cases endpoint <;>
          simp [edgeEndpoint, qToXDoubleCylinderEdgeRaw,
            tannerDoubleCylinderEdgeStart, tannerDoubleCylinderEdgeEnd,
            subdivisionOriginalBoundaryVertex] at hsubdivision
    · right
      refine ⟨boundary, edgeMember, rfl, ?_⟩
      rcases rxStarEdgeInteriorGlueFace_cases P A4 S x copy boundary
          edgeMember index glue (by simpa [rxFaceX] using hx) with
        hbefore | hafter
      · right; right; left; exact congrArg (fun face => Sum.inr (Sum.inl face)) hbefore
      · right; right; right
        exact congrArg (fun face => Sum.inr (Sum.inl face)) hafter
  · rcases old with ⟨oldFace, oldCopy⟩
    have howner : P.faceX oldFace = x := congrArg Sigma.fst hx
    subst x
    have hvertex :
        (oldCopy, Sum.inl
          (xStarFaceZVertex P (P.faceX oldFace) (oldFaceInXStar P oldFace))) =
        (copy, Sum.inr (Sum.inl (edge, index))) :=
      eq_of_heq (Sigma.mk.inj_iff.mp hx).2
    cases congrArg Prod.snd hvertex
noncomputable def rxStarEdgeInteriorBeforeXStarFaceAt
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (edge : XStarEdge P x) (index : Fin (S.half - 1))
    (face : XStarFace P x) (corner : Two)
    (hedge : match edge.1 with
      | Sum.inl _ => xStarFaceXQEdge P x face corner = edge
      | Sum.inr _ => xStarFaceQZEdge P x face corner = edge) :
    XStarFace (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy edge index) :=
  ⟨Sum.inl (rxStarEdgeInteriorBeforeLocalFaceAt
      P S x copy edge index face corner), by
    simp only [xStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    exact rxStarEdgeInteriorBeforeLocalFaceAt_x
      P S x copy edge index face corner hedge⟩
noncomputable def rxStarEdgeInteriorAfterXStarFaceAt
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (edge : XStarEdge P x) (index : Fin (S.half - 1))
    (face : XStarFace P x) (corner : Two)
    (hedge : match edge.1 with
      | Sum.inl _ => xStarFaceXQEdge P x face corner = edge
      | Sum.inr _ => xStarFaceQZEdge P x face corner = edge) :
    XStarFace (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy edge index) :=
  ⟨Sum.inl (rxStarEdgeInteriorAfterLocalFaceAt
      P S x copy edge index face corner), by
    simp only [xStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    exact rxStarEdgeInteriorAfterLocalFaceAt_x
      P S x copy edge index face corner hedge⟩
theorem rxStarEdgeInteriorBeforeAlongBoundaryQEqAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1)) (face : XStarFace P x) (corner : Two)
    (hedge : match edge.1 with
      | Sum.inl _ => xStarFaceXQEdge P x face corner = edge
      | Sum.inr _ => xStarFaceQZEdge P x face corner = edge) :
    xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxStarEdgeInteriorXCoordinate P S x copy edge index)
          (rxStarEdgeInteriorBeforeXStarFace P A4 S x copy edge index)
          (rxStarEdgeInteriorAlongCornerAt edge
            (rxStarEdgeInteriorOwner P A4 x edge).1.2)) =
      xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxStarEdgeInteriorXCoordinate P S x copy edge index)
          (rxStarEdgeInteriorBeforeXStarFaceAt
            P S x copy edge index face corner hedge)
          (rxStarEdgeInteriorAlongCornerAt edge corner)) := by
  apply Subtype.ext
  apply congrArg Vertex.q
  exact (rxStarEdgeInteriorBeforeAlongQAt P S x copy edge index
    (rxStarEdgeInteriorOwner P A4 x edge).1.1
    (rxStarEdgeInteriorOwner P A4 x edge).1.2
    (rxStarEdgeInteriorOwner P A4 x edge).2).trans
    (rxStarEdgeInteriorBeforeAlongQAt
      P S x copy edge index face corner hedge).symm
theorem rxStarEdgeInteriorAfterAlongBoundaryQEqAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1)) (face : XStarFace P x) (corner : Two)
    (hedge : match edge.1 with
      | Sum.inl _ => xStarFaceXQEdge P x face corner = edge
      | Sum.inr _ => xStarFaceQZEdge P x face corner = edge) :
    xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxStarEdgeInteriorXCoordinate P S x copy edge index)
          (rxStarEdgeInteriorAfterXStarFace P A4 S x copy edge index)
          (rxStarEdgeInteriorAlongCornerAt edge
            (rxStarEdgeInteriorOwner P A4 x edge).1.2)) =
      xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxStarEdgeInteriorXCoordinate P S x copy edge index)
          (rxStarEdgeInteriorAfterXStarFaceAt
            P S x copy edge index face corner hedge)
          (rxStarEdgeInteriorAlongCornerAt edge corner)) := by
  apply Subtype.ext
  apply congrArg Vertex.q
  exact (rxStarEdgeInteriorAfterAlongQAt P S x copy edge index
    (rxStarEdgeInteriorOwner P A4 x edge).1.1
    (rxStarEdgeInteriorOwner P A4 x edge).1.2
    (rxStarEdgeInteriorOwner P A4 x edge).2).trans
    (rxStarEdgeInteriorAfterAlongQAt
      P S x copy edge index face corner hedge).symm
noncomputable def rxStarEdgeInteriorBoundaryPathBeforeAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1)) (face : XStarFace P x) (corner : Two)
    (hedge : match edge.1 with
      | Sum.inl _ => xStarFaceXQEdge P x face corner = edge
      | Sum.inr _ => xStarFaceQZEdge P x face corner = edge)
    (qCorner : Two) := by
  let alongOwner := rxStarEdgeInteriorAlongCornerAt edge
    (rxStarEdgeInteriorOwner P A4 x edge).1.2
  let alongCandidate := rxStarEdgeInteriorAlongCornerAt edge corner
  let first := rxStarEdgeInteriorBoundaryPathBefore
    P A4 S x copy edge index alongOwner
  let bridge := (xStarFaceBoundaryPathToQ (rxReplacementPresentation P S)
    (rxStarEdgeInteriorXCoordinate P S x copy edge index)
    (rxStarEdgeInteriorBeforeXStarFaceAt
      P S x copy edge index face corner hedge) alongCandidate).reverse
  let last := xStarFaceBoundaryPathToQ (rxReplacementPresentation P S)
    (rxStarEdgeInteriorXCoordinate P S x copy edge index)
    (rxStarEdgeInteriorBeforeXStarFaceAt
      P S x copy edge index face corner hedge) qCorner
  exact first.append
    (((rxStarEdgeInteriorBeforeAlongBoundaryQEqAt
      P A4 S x copy edge index face corner hedge).symm ▸ bridge).append last)
noncomputable def rxStarEdgeInteriorBoundaryPathAfterAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1)) (face : XStarFace P x) (corner : Two)
    (hedge : match edge.1 with
      | Sum.inl _ => xStarFaceXQEdge P x face corner = edge
      | Sum.inr _ => xStarFaceQZEdge P x face corner = edge)
    (qCorner : Two) := by
  let alongOwner := rxStarEdgeInteriorAlongCornerAt edge
    (rxStarEdgeInteriorOwner P A4 x edge).1.2
  let alongCandidate := rxStarEdgeInteriorAlongCornerAt edge corner
  let first := rxStarEdgeInteriorBoundaryPathAfter
    P A4 S x copy edge index alongOwner
  let bridge := (xStarFaceBoundaryPathToQ (rxReplacementPresentation P S)
    (rxStarEdgeInteriorXCoordinate P S x copy edge index)
    (rxStarEdgeInteriorAfterXStarFaceAt
      P S x copy edge index face corner hedge) alongCandidate).reverse
  let last := xStarFaceBoundaryPathToQ (rxReplacementPresentation P S)
    (rxStarEdgeInteriorXCoordinate P S x copy edge index)
    (rxStarEdgeInteriorAfterXStarFaceAt
      P S x copy edge index face corner hedge) qCorner
  exact first.append
    (((rxStarEdgeInteriorAfterAlongBoundaryQEqAt
      P A4 S x copy edge index face corner hedge).symm ▸ bridge).append last)
noncomputable def rxStarEdgeInteriorBoundaryPathToZBeforeAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1)) (face : XStarFace P x) (corner : Two)
    (hedge : match edge.1 with
      | Sum.inl _ => xStarFaceXQEdge P x face corner = edge
      | Sum.inr _ => xStarFaceQZEdge P x face corner = edge) :=
  (rxStarEdgeInteriorBoundaryPathBeforeAt
    P A4 S x copy edge index face corner hedge 0).append
    (xStarFaceBoundaryPathToZ _ _
      (rxStarEdgeInteriorBeforeXStarFaceAt
        P S x copy edge index face corner hedge))
noncomputable def rxStarEdgeInteriorBoundaryPathToZAfterAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1)) (face : XStarFace P x) (corner : Two)
    (hedge : match edge.1 with
      | Sum.inl _ => xStarFaceXQEdge P x face corner = edge
      | Sum.inr _ => xStarFaceQZEdge P x face corner = edge) :=
  (rxStarEdgeInteriorBoundaryPathAfterAt
    P A4 S x copy edge index face corner hedge 0).append
    (xStarFaceBoundaryPathToZ _ _
      (rxStarEdgeInteriorAfterXStarFaceAt
        P S x copy edge index face corner hedge))
inductive RXStarEdgeInteriorSmallTarget
    (P : TannerSquarePresentation) (x : P.X) (edge : XStarEdge P x)
  | beforeQ (face : XStarFace P x) (side : Two)
      (hedge : match edge.1 with
        | Sum.inl _ => xStarFaceXQEdge P x face side = edge
        | Sum.inr _ => xStarFaceQZEdge P x face side = edge)
      (corner : Two)
  | afterQ (face : XStarFace P x) (side : Two)
      (hedge : match edge.1 with
        | Sum.inl _ => xStarFaceXQEdge P x face side = edge
        | Sum.inr _ => xStarFaceQZEdge P x face side = edge)
      (corner : Two)
  | beforeZ (face : XStarFace P x) (side : Two)
      (hedge : match edge.1 with
        | Sum.inl _ => xStarFaceXQEdge P x face side = edge
        | Sum.inr _ => xStarFaceQZEdge P x face side = edge)
  | afterZ (face : XStarFace P x) (side : Two)
      (hedge : match edge.1 with
        | Sum.inl _ => xStarFaceXQEdge P x face side = edge
        | Sum.inr _ => xStarFaceQZEdge P x face side = edge)
noncomputable def rxStarEdgeInteriorSmallBoundaryVertex
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (edge : XStarEdge P x) (index : Fin (S.half - 1)) :
    RXStarEdgeInteriorSmallTarget P x edge →
      XStarBoundaryVertex (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index)
  | .beforeQ face side hedge corner =>
      xBoundaryEdgeStart (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxStarEdgeInteriorBeforeXStarFaceAt
            P S x copy edge index face side hedge) corner)
  | .afterQ face side hedge corner =>
      xBoundaryEdgeStart (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxStarEdgeInteriorAfterXStarFaceAt
            P S x copy edge index face side hedge) corner)
  | .beforeZ face side hedge =>
      xBoundaryEdgeEnd (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxStarEdgeInteriorBeforeXStarFaceAt
            P S x copy edge index face side hedge) 0)
  | .afterZ face side hedge =>
      xBoundaryEdgeEnd (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxStarEdgeInteriorAfterXStarFaceAt
            P S x copy edge index face side hedge) 0)
noncomputable def rxStarEdgeInteriorSmallBoundaryPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1))
    (target : RXStarEdgeInteriorSmallTarget P x edge) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index))
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxStarEdgeInteriorXCoordinate P S x copy edge index)
          (rxStarEdgeInteriorBeforeXStarFace P A4 S x copy edge index) 0))
      (rxStarEdgeInteriorSmallBoundaryVertex
        P S x copy edge index target) := by
  rcases target with
    ⟨face, side, hedge, corner⟩ |
    ⟨face, side, hedge, corner⟩ |
    ⟨face, side, hedge⟩ |
    ⟨face, side, hedge⟩
  · exact rxStarEdgeInteriorBoundaryPathBeforeAt
      P A4 S x copy edge index face side hedge corner
  · exact rxStarEdgeInteriorBoundaryPathAfterAt
      P A4 S x copy edge index face side hedge corner
  · exact rxStarEdgeInteriorBoundaryPathToZBeforeAt
      P A4 S x copy edge index face side hedge
  · exact rxStarEdgeInteriorBoundaryPathToZAfterAt
      P A4 S x copy edge index face side hedge
inductive RXStarEdgeInteriorTarget
    (P : TannerSquarePresentation) (x : P.X) : XStarEdge P x → Type
  | small (edge : XStarEdge P x)
      (target : RXStarEdgeInteriorSmallTarget P x edge) :
      RXStarEdgeInteriorTarget P x edge
  | rectangle (edge : QZEdge P)
      (member : xStarEdgeMember P x (Sum.inr edge) = true)
      (target : RXStarEdgeInteriorRectangleTarget) :
      RXStarEdgeInteriorTarget P x ⟨Sum.inr edge, member⟩
  | glue (edge : QZEdge P)
      (member : xStarEdgeMember P x (Sum.inr edge) = true)
      (target : RXStarEdgeInteriorGlueTarget) :
      RXStarEdgeInteriorTarget P x ⟨Sum.inr edge, member⟩
noncomputable def rxStarEdgeInteriorTargetBoundaryVertex
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1)) :
    RXStarEdgeInteriorTarget P x edge →
      XStarBoundaryVertex (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index)
  | .small _ target =>
      rxStarEdgeInteriorSmallBoundaryVertex
        P S x copy edge index target
  | .rectangle boundary member target =>
      rxStarEdgeInteriorRectangleBoundaryVertex
        P S x copy boundary member index target
  | .glue boundary member target =>
      rxStarEdgeInteriorGlueBoundaryVertex
        P A4 S x copy boundary member index target
noncomputable def rxStarEdgeInteriorTargetBoundaryPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1))
    (target : RXStarEdgeInteriorTarget P x edge) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index))
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxStarEdgeInteriorXCoordinate P S x copy edge index)
          (rxStarEdgeInteriorBeforeXStarFace P A4 S x copy edge index) 0))
      (rxStarEdgeInteriorTargetBoundaryVertex
        P A4 S x copy edge index target) := by
  rcases target with
    ⟨edge, target⟩ |
    ⟨boundary, member, target⟩ |
    ⟨boundary, member, target⟩
  · exact rxStarEdgeInteriorSmallBoundaryPath
      P A4 S x copy edge index target
  · exact rxStarEdgeInteriorRectangleBoundaryPath
      P A4 S x copy boundary member index target
  · exact rxStarEdgeInteriorGlueBoundaryPath
      P A4 S x copy boundary member index target
noncomputable def rxStarEdgeInteriorIncidentXStarFace
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (edge : XStarEdge P x) (index : Fin (S.half - 1))
    (candidate : RXFace P S)
    (hx : rxFaceX P S candidate =
      rxStarEdgeInteriorXCoordinate P S x copy edge index) :
    XStarFace (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy edge index) :=
  ⟨candidate, by
    simp only [xStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    exact hx⟩
def rxStarEdgeInteriorFaceEdgeAt
    (P : TannerSquarePresentation) (x : P.X) (edge : XStarEdge P x)
    (face : XStarFace P x) (side : Two) : XStarEdge P x :=
  match edge.1 with
  | Sum.inl _ => xStarFaceXQEdge P x face side
  | Sum.inr _ => xStarFaceQZEdge P x face side
theorem rxStarEdgeInteriorFaceEdgeAt_injective
    (P : TannerSquarePresentation) (x : P.X) (edge : XStarEdge P x)
    (face : XStarFace P x) :
    Function.Injective (rxStarEdgeInteriorFaceEdgeAt P x edge face) := by
  intro first second h
  unfold rxStarEdgeInteriorFaceEdgeAt at h
  rcases edge with ⟨radial | boundary, edgeMember⟩
  · apply P.faceQ_injective face.1
    have hvalue := congrArg Subtype.val h
    have hedge := Sum.inl.inj hvalue
    exact congrArg (fun candidate : XQEdge P => candidate.1.2) hedge
  · apply P.faceQ_injective face.1
    have hvalue := congrArg Subtype.val h
    have hedge := Sum.inr.inj hvalue
    exact congrArg (fun candidate : QZEdge P => candidate.1.1) hedge
theorem rxStarEdgeInteriorFaceEdgeAt_eq_of_match
    (P : TannerSquarePresentation) (x : P.X) (edge : XStarEdge P x)
    (face : XStarFace P x) (side : Two)
    (hedge : match edge.1 with
      | Sum.inl _ => xStarFaceXQEdge P x face side = edge
      | Sum.inr _ => xStarFaceQZEdge P x face side = edge) :
    rxStarEdgeInteriorFaceEdgeAt P x edge face side = edge := by
  rcases edge with ⟨radial | boundary, edgeMember⟩ <;> exact hedge
theorem rxStarEdgeInteriorFaceEdgeAt_match_of_eq
    (P : TannerSquarePresentation) (x : P.X) (edge : XStarEdge P x)
    (face : XStarFace P x) (side : Two)
    (hedge : rxStarEdgeInteriorFaceEdgeAt P x edge face side = edge) :
    match edge.1 with
    | Sum.inl _ => xStarFaceXQEdge P x face side = edge
    | Sum.inr _ => xStarFaceQZEdge P x face side = edge := by
  rcases edge with ⟨radial | boundary, edgeMember⟩ <;> exact hedge
noncomputable def rxStarEdgeInteriorRawSide
    (P : TannerSquarePresentation) (x : P.X) (edge : XStarEdge P x)
    (face : XStarFace P x) : Two :=
  if rxStarEdgeInteriorFaceEdgeAt P x edge face 0 = edge then 0 else 1
theorem rxStarEdgeInteriorRawSide_edge
    (P : TannerSquarePresentation) (x : P.X) (edge : XStarEdge P x)
    (face : XStarFace P x) (side : Two)
    (hedge : rxStarEdgeInteriorFaceEdgeAt P x edge face side = edge) :
    rxStarEdgeInteriorFaceEdgeAt P x edge face
        (rxStarEdgeInteriorRawSide P x edge face) = edge := by
  unfold rxStarEdgeInteriorRawSide
  split <;> rename_i hzero
  · exact hzero
  · fin_cases side
    · exact False.elim (hzero hedge)
    · exact hedge
theorem rxStarEdgeInteriorRawSide_eq
    (P : TannerSquarePresentation) (x : P.X) (edge : XStarEdge P x)
    (face : XStarFace P x) (side : Two)
    (hedge : rxStarEdgeInteriorFaceEdgeAt P x edge face side = edge) :
    rxStarEdgeInteriorRawSide P x edge face = side := by
  unfold rxStarEdgeInteriorRawSide
  split <;> rename_i hzero
  · exact rxStarEdgeInteriorFaceEdgeAt_injective P x edge face
      (hzero.trans hedge.symm)
  · fin_cases side
    · exact False.elim (hzero hedge)
    · rfl
def rxStarEdgeInteriorRawLocalOldFace?
    (P : TannerSquarePresentation) (S : OddScale) :
    RXLocalFace P S → Option P.Face
  | ⟨_, Sum.inl (_, (face, _, _)), _⟩ => some face.1
  | ⟨_, Sum.inr _, _⟩ => none
theorem rxStarEdgeInteriorRawSmallZ_normalize
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (edge : XStarEdge P x) (index : Fin (S.half - 1))
    (candidateX : P.X) (candidateCopy : Two)
    (face : XStarFace P candidateX) (column row : Fin S.half)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy edge index)
      (Vertex.z (Sum.inl (Sum.inl
        ⟨candidateX, Sum.inl (candidateCopy, (face, column, row))⟩))) = true) :
    candidateX = x ∧
      ∀ howner : candidateX = x,
        let transportedFace : XStarFace P x := howner ▸ face
        let side := rxStarEdgeInteriorRawSide P x edge transportedFace
        rxStarEdgeInteriorFaceEdgeAt P x edge transportedFace side = edge ∧
          ((Sum.inl (Sum.inl
              ⟨candidateX, Sum.inl
                (candidateCopy, (face, column, row))⟩) : RX2 P S) =
              localFaceZ P S
                (rxStarEdgeInteriorBeforeLocalFaceAt
                  P S x copy edge index transportedFace side) ∨
            (Sum.inl (Sum.inl
              ⟨candidateX, Sum.inl
                (candidateCopy, (face, column, row))⟩) : RX2 P S) =
              localFaceZ P S
                (rxStarEdgeInteriorAfterLocalFaceAt
                  P S x copy edge index transportedFace side)) := by
  classical
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl]
    at member
  rw [decide_eq_true_eq] at member
  obtain ⟨candidate, hx, hzTag⟩ := member
  have hx' : rxFaceX P S candidate =
      rxStarEdgeInteriorXCoordinate P S x copy edge index := by
    simp only [xStarFaceMember, decide_eq_true_eq] at hx
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
    exact hx
  rcases candidate with candidateLocal | candidateGlue | candidateOld
  · rcases candidateLocal with ⟨ownerX, localCell, material⟩
    have hcore :
        (⟨candidateX,
          Sum.inl (candidateCopy, (face, column, row))⟩ :
            Σ ownerX : P.X, DoubleCylinderFace P ownerX S) =
        ⟨ownerX, localCell⟩ := by
      exact Sum.inl.inj (Sum.inl.inj hzTag)
    cases hcore
    have howner : candidateX = x := by
      simpa [rxFaceX, localFaceX, rxStarEdgeInteriorXCoordinate] using congrArg Sigma.fst hx'
    subst candidateX
    refine ⟨rfl, ?_⟩
    intro howner'
    have hproof : howner' = (rfl : x = x) := Subsingleton.elim _ _
    cases hproof
    obtain ⟨targetFace, targetSide, hedge, hbefore | hafter⟩ :=
      rxStarEdgeInteriorLocalFace_cases P S x copy edge index
        ⟨x, Sum.inl (candidateCopy, (face, column, row)), material⟩
        (by simpa [rxFaceX] using hx')
        ⟨(candidateCopy, (face, column, row)), rfl⟩
    · have hfaceValue : face.1 = targetFace.1 := by
        have hfaceOption := congrArg
          (rxStarEdgeInteriorRawLocalOldFace? P S) hbefore
        rcases edge with ⟨radial | boundary, edgeMember⟩ <;>
          fin_cases targetSide <;>
          simpa [rxStarEdgeInteriorRawLocalOldFace?,
            rxStarEdgeInteriorBeforeLocalFaceAt, rxTwoElim] using hfaceOption
      have hface : face = targetFace := Subtype.ext hfaceValue
      subst targetFace
      have hedge' : rxStarEdgeInteriorFaceEdgeAt
          P x edge face targetSide = edge := by
        exact rxStarEdgeInteriorFaceEdgeAt_eq_of_match
          P x edge face targetSide hedge
      have hside := rxStarEdgeInteriorRawSide_edge
        P x edge face targetSide hedge'
      refine ⟨hside, Or.inl ?_⟩
      have hsideEq := rxStarEdgeInteriorRawSide_eq
        P x edge face targetSide hedge'
      rw [hsideEq]
      simpa only [localFaceZ] using
        congrArg (localFaceZ P S) hbefore
    · have hfaceValue : face.1 = targetFace.1 := by
        have hfaceOption := congrArg
          (rxStarEdgeInteriorRawLocalOldFace? P S) hafter
        rcases edge with ⟨radial | boundary, edgeMember⟩ <;>
          fin_cases targetSide <;>
          simpa [rxStarEdgeInteriorRawLocalOldFace?,
            rxStarEdgeInteriorAfterLocalFaceAt, rxTwoElim] using hfaceOption
      have hface : face = targetFace := Subtype.ext hfaceValue
      subst targetFace
      have hedge' : rxStarEdgeInteriorFaceEdgeAt
          P x edge face targetSide = edge := by
        exact rxStarEdgeInteriorFaceEdgeAt_eq_of_match
          P x edge face targetSide hedge
      have hside := rxStarEdgeInteriorRawSide_edge
        P x edge face targetSide hedge'
      refine ⟨hside, Or.inr ?_⟩
      have hsideEq := rxStarEdgeInteriorRawSide_eq
        P x edge face targetSide hedge'
      rw [hsideEq]
      simpa only [localFaceZ] using
        congrArg (localFaceZ P S) hafter
  · cases hzTag
  · cases hzTag
noncomputable def rxStarEdgeInteriorRawSmallZPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : XStarEdge P x) (index : Fin (S.half - 1))
    (candidateX : P.X) (candidateCopy : Two)
    (face : XStarFace P candidateX) (column row : Fin S.half)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy edge index)
      (Vertex.z (Sum.inl (Sum.inl
        ⟨candidateX, Sum.inl (candidateCopy, (face, column, row))⟩))) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index))
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxStarEdgeInteriorXCoordinate P S x copy edge index)
          (rxStarEdgeInteriorBeforeXStarFace P A4 S x copy edge index) 0))
      ⟨Vertex.z (Sum.inl (Sum.inl
        ⟨candidateX, Sum.inl (candidateCopy, (face, column, row))⟩)),
        member⟩ := by
  obtain ⟨howner, hnormalize⟩ := rxStarEdgeInteriorRawSmallZ_normalize
    P S x copy edge index candidateX candidateCopy face column row member
  subst candidateX
  let side := rxStarEdgeInteriorRawSide P x edge face
  have hedge := (hnormalize rfl).1
  have hedge' :
      (match edge.1 with
        | Sum.inl _ => xStarFaceXQEdge P x face side = edge
        | Sum.inr _ => xStarFaceQZEdge P x face side = edge) := by
    simpa only [side] using
      (rxStarEdgeInteriorFaceEdgeAt_match_of_eq
        P x edge face (rxStarEdgeInteriorRawSide P x edge face) hedge)
  by_cases hbefore :
      (Sum.inl (Sum.inl
        ⟨x, Sum.inl (candidateCopy, (face, column, row))⟩) : RX2 P S) =
        localFaceZ P S
          (rxStarEdgeInteriorBeforeLocalFaceAt
            P S x copy edge index face side)
  · let target : RXStarEdgeInteriorTarget P x edge :=
      .small edge (.beforeZ face side hedge')
    let path := rxStarEdgeInteriorTargetBoundaryPath
      P A4 S x copy edge index target
    have htarget : rxStarEdgeInteriorTargetBoundaryVertex
          P A4 S x copy edge index target =
        ⟨Vertex.z (Sum.inl (Sum.inl
          ⟨x, Sum.inl (candidateCopy, (face, column, row))⟩)), member⟩ := by
      apply Subtype.ext
      exact congrArg Vertex.z hbefore.symm
    exact htarget ▸ path
  · have hafter :
        (Sum.inl (Sum.inl
          ⟨x, Sum.inl (candidateCopy, (face, column, row))⟩) : RX2 P S) =
          localFaceZ P S
            (rxStarEdgeInteriorAfterLocalFaceAt
              P S x copy edge index face side) := by
      rcases (hnormalize rfl).2 with hbefore' | hafter
      · exact False.elim (hbefore hbefore')
      · exact hafter
    let target : RXStarEdgeInteriorTarget P x edge :=
      .small edge (.afterZ face side hedge')
    let path := rxStarEdgeInteriorTargetBoundaryPath
      P A4 S x copy edge index target
    have htarget : rxStarEdgeInteriorTargetBoundaryVertex
          P A4 S x copy edge index target =
        ⟨Vertex.z (Sum.inl (Sum.inl
          ⟨x, Sum.inl (candidateCopy, (face, column, row))⟩)), member⟩ := by
      apply Subtype.ext
      exact congrArg Vertex.z hafter.symm
    exact htarget ▸ path
def rxStarEdgeInteriorRawLocalQZEdge?
    (P : TannerSquarePresentation) (S : OddScale) :
    RXLocalFace P S → Option (QZEdge P)
  | ⟨_, Sum.inr ⟨Sum.inl (⟨Sum.inr edge, _⟩, _), _⟩, _⟩ => some edge
  | _ => none
def rxStarEdgeInteriorRawLocalIsRectangle
    (P : TannerSquarePresentation) (S : OddScale) :
    RXLocalFace P S → Bool
  | ⟨_, Sum.inl _, _⟩ => false
  | ⟨_, Sum.inr _, _⟩ => true
theorem rxStarEdgeInteriorRawRectangleZ_normalize
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) (candidateX : P.X)
    (candidateEdge : QZEdge P)
    (candidateMember : xStarEdgeMember P candidateX
      (Sum.inr candidateEdge) = true)
    (segment : Fin S.half)
    (boundaryMember : subdivisionBoundaryEdgeMember P candidateX S
      (Sum.inl (⟨Sum.inr candidateEdge, candidateMember⟩, segment)) = true)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inr edge, edgeMember⟩ index)
      (Vertex.z (Sum.inl (Sum.inl
        ⟨candidateX, Sum.inr
          ⟨Sum.inl (⟨Sum.inr candidateEdge, candidateMember⟩, segment),
            boundaryMember⟩⟩))) = true) :
    candidateX = x ∧
      ∀ howner : candidateX = x,
        let transportedMember : xStarEdgeMember P x
            (Sum.inr candidateEdge) = true := howner ▸ candidateMember
        candidateEdge = edge ∧
          ((Sum.inl (Sum.inl
            ⟨candidateX, Sum.inr
              ⟨Sum.inl (⟨Sum.inr candidateEdge, candidateMember⟩, segment),
                boundaryMember⟩⟩) : RX2 P S) =
              localFaceZ P S
                (rxStarEdgeInteriorRectangleBeforeLocalFace
                  P S x copy edge edgeMember index) ∨
            (Sum.inl (Sum.inl
              ⟨candidateX, Sum.inr
                ⟨Sum.inl (⟨Sum.inr candidateEdge, candidateMember⟩, segment),
                  boundaryMember⟩⟩) : RX2 P S) =
              localFaceZ P S
                (rxStarEdgeInteriorRectangleAfterLocalFace
                  P S x copy edge edgeMember index)) := by
  classical
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl]
    at member
  rw [decide_eq_true_eq] at member
  obtain ⟨candidate, hx, hzTag⟩ := member
  have hx' : rxFaceX P S candidate =
      rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inr edge, edgeMember⟩ index := by
    simp only [xStarFaceMember, decide_eq_true_eq] at hx
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
    exact hx
  rcases candidate with candidateLocal | candidateGlue | candidateOld
  · rcases candidateLocal with ⟨ownerX, localCell, material⟩
    have hcell :
        (⟨candidateX, Sum.inr
          ⟨Sum.inl (⟨Sum.inr candidateEdge, candidateMember⟩, segment),
            boundaryMember⟩⟩ :
          Σ ownerX : P.X, DoubleCylinderFace P ownerX S) =
        ⟨ownerX, localCell⟩ := by
      exact Sum.inl.inj (Sum.inl.inj hzTag)
    cases hcell
    have howner : candidateX = x := by
      simpa [rxFaceX, localFaceX, rxStarEdgeInteriorXCoordinate] using congrArg Sigma.fst hx'
    subst candidateX
    refine ⟨rfl, ?_⟩
    intro howner'
    have hproof : howner' = (rfl : x = x) := Subsingleton.elim _ _
    cases hproof
    rcases rxStarEdgeInteriorRectangleFace_cases
        P S x copy edge edgeMember index
        ⟨Sum.inl (⟨Sum.inr candidateEdge, candidateMember⟩, segment),
          boundaryMember⟩ material (by simpa [rxFaceX] using hx') with
      hbefore | hafter
    · have hedgeOption := congrArg
        (rxStarEdgeInteriorRawLocalQZEdge? P S) hbefore
      have hedge : candidateEdge = edge := by
        simpa [rxStarEdgeInteriorRawLocalQZEdge?,
          rxStarEdgeInteriorRectangleBeforeLocalFace,
          rxStarEdgeInteriorRectangleBefore,
          subdivisionOriginalBoundaryEdge,
          rxStarEdgeInteriorBoundaryEdge,
          xStarBoundaryEdgeToStar] using hedgeOption
      subst candidateEdge
      cases Subsingleton.elim candidateMember edgeMember
      exact ⟨rfl, Or.inl (by
        simpa only [localFaceZ] using congrArg (localFaceZ P S) hbefore)⟩
    · have hedgeOption := congrArg
        (rxStarEdgeInteriorRawLocalQZEdge? P S) hafter
      have hedge : candidateEdge = edge := by
        simpa [rxStarEdgeInteriorRawLocalQZEdge?,
          rxStarEdgeInteriorRectangleAfterLocalFace,
          rxStarEdgeInteriorRectangleAfter,
          subdivisionOriginalBoundaryEdge,
          rxStarEdgeInteriorBoundaryEdge,
          xStarBoundaryEdgeToStar] using hedgeOption
      subst candidateEdge
      cases Subsingleton.elim candidateMember edgeMember
      exact ⟨rfl, Or.inr (by
        simpa only [localFaceZ] using congrArg (localFaceZ P S) hafter)⟩
  · cases hzTag
  · cases hzTag
noncomputable def rxStarEdgeInteriorRawRectangleZPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) (candidateX : P.X)
    (candidateEdge : QZEdge P)
    (candidateMember : xStarEdgeMember P candidateX
      (Sum.inr candidateEdge) = true)
    (segment : Fin S.half)
    (boundaryMember : subdivisionBoundaryEdgeMember P candidateX S
      (Sum.inl (⟨Sum.inr candidateEdge, candidateMember⟩, segment)) = true)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inr edge, edgeMember⟩ index)
      (Vertex.z (Sum.inl (Sum.inl
        ⟨candidateX, Sum.inr
          ⟨Sum.inl (⟨Sum.inr candidateEdge, candidateMember⟩, segment),
            boundaryMember⟩⟩))) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy
          ⟨Sum.inr edge, edgeMember⟩ index))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy
          ⟨Sum.inr edge, edgeMember⟩ index))
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy
          ⟨Sum.inr edge, edgeMember⟩ index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxStarEdgeInteriorBeforeXStarFace P A4 S x copy
            ⟨Sum.inr edge, edgeMember⟩ index) 0))
      ⟨Vertex.z (Sum.inl (Sum.inl
        ⟨candidateX, Sum.inr
          ⟨Sum.inl (⟨Sum.inr candidateEdge, candidateMember⟩, segment),
            boundaryMember⟩⟩)), member⟩ := by
  obtain ⟨howner, hnormalize⟩ :=
    rxStarEdgeInteriorRawRectangleZ_normalize
      P S x copy edge edgeMember index candidateX candidateEdge
        candidateMember segment boundaryMember member
  subst candidateX
  obtain ⟨hedge, hraw⟩ := hnormalize rfl
  subst candidateEdge
  cases Subsingleton.elim candidateMember edgeMember
  by_cases hbefore :
      (Sum.inl (Sum.inl
        ⟨x, Sum.inr
          ⟨Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment),
            boundaryMember⟩⟩) : RX2 P S) =
        localFaceZ P S
          (rxStarEdgeInteriorRectangleBeforeLocalFace
            P S x copy edge edgeMember index)
  · let target : RXStarEdgeInteriorTarget P x ⟨Sum.inr edge, edgeMember⟩ :=
      .rectangle edge edgeMember .beforeZ
    let path := rxStarEdgeInteriorTargetBoundaryPath
      P A4 S x copy ⟨Sum.inr edge, edgeMember⟩ index target
    have htarget : rxStarEdgeInteriorTargetBoundaryVertex
          P A4 S x copy ⟨Sum.inr edge, edgeMember⟩ index target =
        ⟨Vertex.z (Sum.inl (Sum.inl
          ⟨x, Sum.inr
            ⟨Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment),
              boundaryMember⟩⟩)), member⟩ := by
      apply Subtype.ext
      exact congrArg Vertex.z hbefore.symm
    exact htarget ▸ path
  · have hafter :
        (Sum.inl (Sum.inl
          ⟨x, Sum.inr
            ⟨Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment),
              boundaryMember⟩⟩) : RX2 P S) =
          localFaceZ P S
            (rxStarEdgeInteriorRectangleAfterLocalFace
              P S x copy edge edgeMember index) := by
      rcases hraw with hbefore' | hafter
      · exact False.elim (hbefore hbefore')
      · exact hafter
    let target : RXStarEdgeInteriorTarget P x ⟨Sum.inr edge, edgeMember⟩ :=
      .rectangle edge edgeMember .afterZ
    let path := rxStarEdgeInteriorTargetBoundaryPath
      P A4 S x copy ⟨Sum.inr edge, edgeMember⟩ index target
    have htarget : rxStarEdgeInteriorTargetBoundaryVertex
          P A4 S x copy ⟨Sum.inr edge, edgeMember⟩ index target =
        ⟨Vertex.z (Sum.inl (Sum.inl
          ⟨x, Sum.inr
            ⟨Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment),
              boundaryMember⟩⟩)), member⟩ := by
      apply Subtype.ext
      exact congrArg Vertex.z hafter.symm
    exact htarget ▸ path
def rxStarEdgeInteriorRawGlueCopied
    (P : TannerSquarePresentation) (S : OddScale) :
    RXXQGlueFace P S → Bool
  | ⟨_, Sum.inl _, _⟩ => true
  | ⟨_, Sum.inr _, _⟩ => false
theorem rxStarEdgeInteriorRawGlueZ_normalize
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) (candidateQ : P.Q)
    (candidateCopy : Two) (candidateEdge : QStarEdge P candidateQ)
    (segment : Fin S.half)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inr edge, edgeMember⟩ index)
      (Vertex.z (Sum.inl (Sum.inr
        ⟨candidateQ, Sum.inl
          (candidateCopy, (candidateEdge, segment))⟩))) = true) :
    (Sum.inl (Sum.inr
      ⟨candidateQ, Sum.inl
        (candidateCopy, (candidateEdge, segment))⟩) : RX2 P S) =
        glueFaceZ P S
          (rxStarEdgeInteriorGlueBefore
            P A4 S x copy edge edgeMember index) ∨
      (Sum.inl (Sum.inr
        ⟨candidateQ, Sum.inl
          (candidateCopy, (candidateEdge, segment))⟩) : RX2 P S) =
        glueFaceZ P S
          (rxStarEdgeInteriorGlueAfter
            P A4 S x copy edge edgeMember index) := by
  classical
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl]
    at member
  rw [decide_eq_true_eq] at member
  obtain ⟨candidate, hx, hzTag⟩ := member
  have hx' : rxFaceX P S candidate =
      rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inr edge, edgeMember⟩ index := by
    simp only [xStarFaceMember, decide_eq_true_eq] at hx
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
    exact hx
  rcases candidate with candidateLocal | candidateGlue | candidateOld
  · cases hzTag
  · rcases candidateGlue with ⟨a, qEdge, endpoint⟩
    have hqEdge : (⟨candidateQ,
          Sum.inl (candidateCopy, (candidateEdge, segment))⟩ :
          Σ q : P.Q, QDoubleCylinderEdge P q S) =
        ⟨a.1.2, qEdge⟩ := by
      exact Sum.inr.inj (Sum.inl.inj hzTag)
    cases hqEdge
    rcases rxStarEdgeInteriorGlueFace_cases
        P A4 S x copy edge edgeMember index
          ⟨a, Sum.inl (candidateCopy, (candidateEdge, segment)), endpoint⟩
          (by simpa [rxFaceX] using hx') with hbefore | hafter
    · exact Or.inl (by
        simpa only [glueFaceZ] using congrArg (glueFaceZ P S) hbefore)
    · exact Or.inr (by
        simpa only [glueFaceZ] using congrArg (glueFaceZ P S) hafter)
  · cases hzTag
noncomputable def rxStarEdgeInteriorRawGlueZPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) (candidateQ : P.Q)
    (candidateCopy : Two) (candidateEdge : QStarEdge P candidateQ)
    (segment : Fin S.half)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inr edge, edgeMember⟩ index)
      (Vertex.z (Sum.inl (Sum.inr
        ⟨candidateQ, Sum.inl
          (candidateCopy, (candidateEdge, segment))⟩))) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy
          ⟨Sum.inr edge, edgeMember⟩ index))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy
          ⟨Sum.inr edge, edgeMember⟩ index))
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy
          ⟨Sum.inr edge, edgeMember⟩ index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxStarEdgeInteriorBeforeXStarFace P A4 S x copy
            ⟨Sum.inr edge, edgeMember⟩ index) 0))
      ⟨Vertex.z (Sum.inl (Sum.inr
        ⟨candidateQ, Sum.inl
          (candidateCopy, (candidateEdge, segment))⟩)), member⟩ := by
  have hraw := rxStarEdgeInteriorRawGlueZ_normalize
    P A4 S x copy edge edgeMember index candidateQ candidateCopy
      candidateEdge segment member
  by_cases hbefore :
      (Sum.inl (Sum.inr
        ⟨candidateQ, Sum.inl
          (candidateCopy, (candidateEdge, segment))⟩) : RX2 P S) =
        glueFaceZ P S
          (rxStarEdgeInteriorGlueBefore
            P A4 S x copy edge edgeMember index)
  · let target : RXStarEdgeInteriorTarget P x ⟨Sum.inr edge, edgeMember⟩ :=
      .glue edge edgeMember .beforeZ
    let path := rxStarEdgeInteriorTargetBoundaryPath
      P A4 S x copy ⟨Sum.inr edge, edgeMember⟩ index target
    have htarget : rxStarEdgeInteriorTargetBoundaryVertex
          P A4 S x copy ⟨Sum.inr edge, edgeMember⟩ index target =
        ⟨Vertex.z (Sum.inl (Sum.inr
          ⟨candidateQ, Sum.inl
            (candidateCopy, (candidateEdge, segment))⟩)), member⟩ := by
      apply Subtype.ext
      exact congrArg Vertex.z hbefore.symm
    exact htarget ▸ path
  · have hafter :
        (Sum.inl (Sum.inr
          ⟨candidateQ, Sum.inl
            (candidateCopy, (candidateEdge, segment))⟩) : RX2 P S) =
          glueFaceZ P S
            (rxStarEdgeInteriorGlueAfter
              P A4 S x copy edge edgeMember index) := by
      rcases hraw with hbefore' | hafter
      · exact False.elim (hbefore hbefore')
      · exact hafter
    let target : RXStarEdgeInteriorTarget P x ⟨Sum.inr edge, edgeMember⟩ :=
      .glue edge edgeMember .afterZ
    let path := rxStarEdgeInteriorTargetBoundaryPath
      P A4 S x copy ⟨Sum.inr edge, edgeMember⟩ index target
    have htarget : rxStarEdgeInteriorTargetBoundaryVertex
          P A4 S x copy ⟨Sum.inr edge, edgeMember⟩ index target =
        ⟨Vertex.z (Sum.inl (Sum.inr
          ⟨candidateQ, Sum.inl
            (candidateCopy, (candidateEdge, segment))⟩)), member⟩ := by
      apply Subtype.ext
      exact congrArg Vertex.z hafter.symm
    exact htarget ▸ path
theorem rxStarEdgeInteriorRawRectangleZ_radial_false
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : XQEdge P) (edgeMember : xStarEdgeMember P x (Sum.inl edge) = true)
    (index : Fin (S.half - 1)) (candidateX : P.X)
    (candidateEdge : QZEdge P)
    (candidateMember : xStarEdgeMember P candidateX
      (Sum.inr candidateEdge) = true)
    (segment : Fin S.half)
    (boundaryMember : subdivisionBoundaryEdgeMember P candidateX S
      (Sum.inl (⟨Sum.inr candidateEdge, candidateMember⟩, segment)) = true)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inl edge, edgeMember⟩ index)
      (Vertex.z (Sum.inl (Sum.inl
        ⟨candidateX, Sum.inr
          ⟨Sum.inl (⟨Sum.inr candidateEdge, candidateMember⟩, segment),
            boundaryMember⟩⟩))) = true) : False := by
  classical
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl]
    at member
  rw [decide_eq_true_eq] at member
  obtain ⟨candidate, hx, hzTag⟩ := member
  have hx' : rxFaceX P S candidate =
      rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inl edge, edgeMember⟩ index := by
    simp only [xStarFaceMember, decide_eq_true_eq] at hx
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
    exact hx
  rcases candidate with candidateLocal | candidateGlue | candidateOld
  · rcases candidateLocal with ⟨ownerX, localCell, material⟩
    have hcell :
        (⟨candidateX, Sum.inr
          ⟨Sum.inl (⟨Sum.inr candidateEdge, candidateMember⟩, segment),
            boundaryMember⟩⟩ :
          Σ ownerX : P.X, DoubleCylinderFace P ownerX S) =
        ⟨ownerX, localCell⟩ := by
      exact Sum.inl.inj (Sum.inl.inj hzTag)
    cases hcell
    rcases rxStarEdgeInteriorIncidentFace_cases
        P A4 S x copy ⟨Sum.inl edge, edgeMember⟩ index
        (Sum.inl ⟨candidateX, Sum.inr
          ⟨Sum.inl (⟨Sum.inr candidateEdge, candidateMember⟩, segment),
            boundaryMember⟩, material⟩) hx' with
      ⟨face, side, hedge, hbefore | hafter⟩ |
      ⟨boundary, boundaryMember', hedge, houter⟩
    · have hlocal := Sum.inl.inj hbefore
      have hshape := congrArg
        (rxStarEdgeInteriorRawLocalIsRectangle P S) hlocal
      fin_cases side <;>
        simp [rxStarEdgeInteriorRawLocalIsRectangle,
          rxStarEdgeInteriorBeforeLocalFaceAt, rxTwoElim] at hshape
    · have hlocal := Sum.inl.inj hafter
      have hshape := congrArg
        (rxStarEdgeInteriorRawLocalIsRectangle P S) hlocal
      fin_cases side <;>
        simp [rxStarEdgeInteriorRawLocalIsRectangle,
          rxStarEdgeInteriorAfterLocalFaceAt, rxTwoElim] at hshape
    · have hraw := congrArg Subtype.val hedge
      cases hraw
  · have himpossible := Sum.inl.inj hzTag
    cases himpossible
  · simp [rxFaceZ, oldZFaceZ] at hzTag
theorem rxStarEdgeInteriorRawGlueZ_radial_false
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : XQEdge P) (edgeMember : xStarEdgeMember P x (Sum.inl edge) = true)
    (index : Fin (S.half - 1)) (candidateQ : P.Q)
    (candidateEdge : QDoubleCylinderEdge P candidateQ S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inl edge, edgeMember⟩ index)
      (Vertex.z (Sum.inl (Sum.inr ⟨candidateQ, candidateEdge⟩))) = true) :
    False := by
  classical
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl]
    at member
  rw [decide_eq_true_eq] at member
  obtain ⟨candidate, hx, hzTag⟩ := member
  have hx' : rxFaceX P S candidate =
      rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inl edge, edgeMember⟩ index := by
    simp only [xStarFaceMember, decide_eq_true_eq] at hx
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
    exact hx
  rcases candidate with candidateLocal | candidateGlue | candidateOld
  · cases hzTag
  · rcases candidateGlue with ⟨a, qEdge, endpoint⟩
    have hqEdge : (⟨candidateQ, candidateEdge⟩ :
          Σ q : P.Q, QDoubleCylinderEdge P q S) = ⟨a.1.2, qEdge⟩ := by
      exact Sum.inr.inj (Sum.inl.inj hzTag)
    cases hqEdge
    rcases rxStarEdgeInteriorIncidentFace_cases
        P A4 S x copy ⟨Sum.inl edge, edgeMember⟩ index
        (Sum.inr (Sum.inl ⟨a, qEdge, endpoint⟩)) hx' with
      ⟨face, side, hedge, hbefore | hafter⟩ |
      ⟨boundary, boundaryMember, hedge, houter⟩
    · cases hbefore
    · cases hafter
    · have hraw := congrArg Subtype.val hedge
      cases hraw
  · cases hzTag
theorem rxStarEdgeInteriorRawVerticalGlueZ_false
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) (candidateQ : P.Q)
    (candidateEdge : QStarEdge P candidateQ)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inr edge, edgeMember⟩ index)
      (Vertex.z (Sum.inl (Sum.inr
        ⟨candidateQ, Sum.inr candidateEdge⟩))) = true) : False := by
  classical
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl]
    at member
  rw [decide_eq_true_eq] at member
  obtain ⟨candidate, hx, hzTag⟩ := member
  have hx' : rxFaceX P S candidate =
      rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inr edge, edgeMember⟩ index := by
    simp only [xStarFaceMember, decide_eq_true_eq] at hx
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
    exact hx
  rcases candidate with candidateLocal | candidateGlue | candidateOld
  · cases hzTag
  · rcases candidateGlue with ⟨a, qEdge, endpoint⟩
    have hqEdge : (⟨candidateQ, Sum.inr candidateEdge⟩ :
          Σ q : P.Q, QDoubleCylinderEdge P q S) =
        ⟨a.1.2, qEdge⟩ := by
      exact Sum.inr.inj (Sum.inl.inj hzTag)
    cases hqEdge
    rcases rxStarEdgeInteriorGlueFace_cases
        P A4 S x copy edge edgeMember index
          ⟨a, Sum.inr candidateEdge, endpoint⟩
          (by simpa [rxFaceX] using hx') with hbefore | hafter
    · have himpossible := congrArg
        (rxStarEdgeInteriorRawGlueCopied P S) hbefore
      simp [rxStarEdgeInteriorRawGlueCopied,
        rxStarEdgeInteriorGlueBefore] at himpossible
    · have himpossible := congrArg
        (rxStarEdgeInteriorRawGlueCopied P S) hafter
      simp [rxStarEdgeInteriorRawGlueCopied,
        rxStarEdgeInteriorGlueAfter] at himpossible
  · cases hzTag
theorem rxStarEdgeInteriorRawOldZ_false
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (edge : XStarEdge P x) (index : Fin (S.half - 1))
    (candidateZ : P.Z) (candidateCopy : Two)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy edge index)
      (Vertex.z (Sum.inr (candidateZ, candidateCopy))) = true) : False := by
  classical
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl]
    at member
  rw [decide_eq_true_eq] at member
  obtain ⟨candidate, hx, hzTag⟩ := member
  have hx' : rxFaceX P S candidate =
      rxStarEdgeInteriorXCoordinate P S x copy edge index := by
    simp only [xStarFaceMember, decide_eq_true_eq] at hx
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
    exact hx
  rcases candidate with candidateLocal | candidateGlue | candidateOld
  · cases hzTag
  · cases hzTag
  · rcases candidateOld with ⟨oldFace, oldCopy⟩
    have howner : P.faceX oldFace = x := congrArg Sigma.fst hx'
    subst x
    have hvertex :
        (oldCopy, Sum.inl
          (xStarFaceZVertex P (P.faceX oldFace) (oldFaceInXStar P oldFace))) =
        (copy, Sum.inr (Sum.inl (edge, index))) :=
      eq_of_heq (Sigma.mk.inj_iff.mp hx').2
    cases congrArg Prod.snd hvertex
noncomputable def rxStarEdgeInteriorRawZPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : XStarEdge P x) (index : Fin (S.half - 1))
    (newZ : RX2 P S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy edge index)
      (Vertex.z newZ) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index))
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxStarEdgeInteriorXCoordinate P S x copy edge index)
          (rxStarEdgeInteriorBeforeXStarFace P A4 S x copy edge index) 0))
      ⟨Vertex.z newZ, member⟩ := by
  rcases newZ with localOrGlue | old
  · rcases localOrGlue with localZ | glue
    · rcases localZ with ⟨candidateX, cell⟩
      rcases cell with small | rectangle
      · rcases small with ⟨candidateCopy, face, column, row⟩
        exact rxStarEdgeInteriorRawSmallZPath
          P A4 S x copy edge index candidateX candidateCopy
            face column row member
      · rcases rectangle with ⟨raw, boundaryMember⟩
        rcases raw with original | interior
        · rcases original with ⟨candidateStarEdge, segment⟩
          rcases candidateStarEdge with
            ⟨candidateRadial | candidateBoundary, candidateMember⟩
          · simp [subdivisionBoundaryEdgeMember,
              xStarBoundaryEdgeMember] at boundaryMember
          · rcases edge with ⟨storedRadial | storedBoundary, storedMember⟩
            · exact False.elim
                (rxStarEdgeInteriorRawRectangleZ_radial_false
                  P A4 S x copy storedRadial storedMember index
                    candidateX candidateBoundary candidateMember
                    segment boundaryMember member)
            · exact rxStarEdgeInteriorRawRectangleZPath
                P A4 S x copy storedBoundary storedMember index
                  candidateX candidateBoundary candidateMember
                  segment boundaryMember member
        · simp [subdivisionBoundaryEdgeMember] at boundaryMember
    · rcases glue with ⟨candidateQ, candidateEdge⟩
      rcases candidateEdge with copied | vertical
      · rcases copied with ⟨candidateCopy, qSegment⟩
        rcases qSegment with ⟨candidateStarEdge, segment⟩
        rcases edge with ⟨storedRadial | storedBoundary, storedMember⟩
        · exact False.elim
            (rxStarEdgeInteriorRawGlueZ_radial_false
              P A4 S x copy storedRadial storedMember index candidateQ
                (Sum.inl (candidateCopy, (candidateStarEdge, segment))) member)
        · exact rxStarEdgeInteriorRawGlueZPath
            P A4 S x copy storedBoundary storedMember index candidateQ
              candidateCopy candidateStarEdge segment member
      · rcases edge with ⟨storedRadial | storedBoundary, storedMember⟩
        · exact False.elim
            (rxStarEdgeInteriorRawGlueZ_radial_false
              P A4 S x copy storedRadial storedMember index candidateQ
                (Sum.inr vertical) member)
        · exact False.elim
            (rxStarEdgeInteriorRawVerticalGlueZ_false
              P A4 S x copy storedBoundary storedMember index
                candidateQ vertical member)
  · rcases old with ⟨candidateZ, candidateCopy⟩
    exact False.elim (rxStarEdgeInteriorRawOldZ_false
      P S x copy edge index candidateZ candidateCopy member)
theorem rxStarEdgeInteriorRawLocalQ_endpoint
    (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1)) (candidateX : P.X)
    (candidateEdge : DoubleCylinderEdge P candidateX S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy edge index)
      (Vertex.q (Sum.inl ⟨candidateX, candidateEdge⟩)) = true) :
    candidateX = x ∧
      ∀ howner : candidateX = x,
        let transportedEdge : DoubleCylinderEdge P x S := howner ▸ candidateEdge
        tannerDoubleCylinderEdgeStart P x S transportedEdge =
            (copy, Sum.inr (Sum.inl (edge, index))) ∨
          tannerDoubleCylinderEdgeEnd P x S transportedEdge =
            (copy, Sum.inr (Sum.inl (edge, index))) := by
  classical
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceQ = rxFaceQ P S from rfl]
    at member
  rw [decide_eq_true_eq] at member
  obtain ⟨candidate, hx, hqTag⟩ := member
  have hx' : rxFaceX P S candidate =
      rxStarEdgeInteriorXCoordinate P S x copy edge index := by
    simp only [xStarFaceMember, decide_eq_true_eq] at hx
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
    exact hx
  have handle : ∀ corner : Two,
      rxFaceQ P S candidate corner = Sum.inl ⟨candidateX, candidateEdge⟩ →
        candidateX = x ∧
          ∀ howner : candidateX = x,
            let transportedEdge : DoubleCylinderEdge P x S :=
              howner ▸ candidateEdge
            tannerDoubleCylinderEdgeStart P x S transportedEdge =
                (copy, Sum.inr (Sum.inl (edge, index))) ∨
              tannerDoubleCylinderEdgeEnd P x S transportedEdge =
                (copy, Sum.inr (Sum.inl (edge, index))) := by
    intro corner hqTag'
    obtain ⟨endpoint, hendpoint⟩ :=
      rxFaceX_eq_endpoint_of_faceQ_eq_xEdge
        P S candidate corner candidateX candidateEdge hqTag'
    have hcoordinate :
        (⟨candidateX,
          edgeEndpoint (tannerDoubleCylinderEdgeStart P candidateX S)
            (tannerDoubleCylinderEdgeEnd P candidateX S)
            candidateEdge endpoint⟩ : RX0 P S) =
          rxStarEdgeInteriorXCoordinate P S x copy edge index :=
      hendpoint.symm.trans hx'
    have howner : candidateX = x := congrArg Sigma.fst hcoordinate
    subst candidateX
    refine ⟨rfl, ?_⟩
    intro howner'
    have hproof : howner' = (rfl : x = x) := Subsingleton.elim _ _
    cases hproof
    have hvertex := eq_of_heq (Sigma.mk.inj_iff.mp hcoordinate).2
    fin_cases endpoint
    · left
      simpa [edgeEndpoint] using hvertex
    · right
      simpa [edgeEndpoint] using hvertex
  rcases hqTag with hqTag | hqTag
  · exact handle 0 hqTag.symm
  · exact handle 1 hqTag.symm
theorem rxStarEdgeInteriorRawCopiedQ_normalize
    (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1)) (candidateX : P.X)
    (candidateCopy : Two) (candidateEdge : XStarEdge P candidateX)
    (segment : Fin S.half)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy edge index)
      (Vertex.q (Sum.inl ⟨candidateX,
        Sum.inl (candidateCopy, Sum.inl (candidateEdge, segment))⟩)) = true) :
    candidateX = x ∧
      ∀ howner : candidateX = x,
        let transportedEdge : XStarEdge P x := howner ▸ candidateEdge
        candidateCopy = copy ∧ transportedEdge = edge ∧
          (segment = rxStarEdgeInteriorPreviousIndex S index ∨
            segment = rxStarEdgeInteriorNextIndex S index) := by
  obtain ⟨howner, hendpoint⟩ := rxStarEdgeInteriorRawLocalQ_endpoint
    P S x copy edge index candidateX
      (Sum.inl (candidateCopy, Sum.inl (candidateEdge, segment))) member
  subst candidateX
  refine ⟨rfl, ?_⟩
  intro howner'
  have hproof : howner' = (rfl : x = x) := Subsingleton.elim _ _
  cases hproof
  rcases hendpoint rfl with hstart | hend
  · have hcopy : candidateCopy = copy := by
      simpa [tannerDoubleCylinderEdgeStart] using congrArg Prod.fst hstart
    subst candidateCopy
    have hsubdivision := congrArg Prod.snd hstart
    by_cases hzero : segment.1 = 0
    · have himpossible :
          (Sum.inl (xStarEdgeStart P x candidateEdge) :
            SubdivisionVertex P x S) =
          Sum.inr (Sum.inl (edge, index)) := by
        simpa [tannerDoubleCylinderEdgeStart, subdivisionEdgeStart,
          subdivisionSegmentStart, hzero] using hsubdivision
      cases himpossible
    · have hpair :
          (candidateEdge, ⟨segment.1 - 1, by have := segment.2; omega⟩) =
            (edge, index) := by
        simpa [tannerDoubleCylinderEdgeStart, subdivisionEdgeStart,
          subdivisionSegmentStart, hzero] using hsubdivision
      have hedge : candidateEdge = edge := congrArg Prod.fst hpair
      have hsegment : segment = rxStarEdgeInteriorNextIndex S index := by
        apply Fin.ext
        have hindex := congrArg (fun pair => pair.2.1) hpair
        change segment.1 - 1 = index.1 at hindex
        simp [rxStarEdgeInteriorNextIndex]
        omega
      exact ⟨rfl, hedge, Or.inr hsegment⟩
  · have hcopy : candidateCopy = copy := by
      simpa [tannerDoubleCylinderEdgeEnd] using congrArg Prod.fst hend
    subst candidateCopy
    have hsubdivision := congrArg Prod.snd hend
    by_cases hlast : segment.1 + 1 = S.half
    · have himpossible :
          (Sum.inl (xStarEdgeEnd P x candidateEdge) :
            SubdivisionVertex P x S) =
          Sum.inr (Sum.inl (edge, index)) := by
        simpa [tannerDoubleCylinderEdgeEnd, subdivisionEdgeEnd,
          subdivisionSegmentEnd, hlast] using hsubdivision
      cases himpossible
    · have hpair : (candidateEdge, ⟨segment.1, by
            have := segment.2
            omega⟩) = (edge, index) := by
        simpa [tannerDoubleCylinderEdgeEnd, subdivisionEdgeEnd,
          subdivisionSegmentEnd, hlast] using hsubdivision
      have hedge : candidateEdge = edge := congrArg Prod.fst hpair
      have hsegment : segment = rxStarEdgeInteriorPreviousIndex S index := by
        apply Fin.ext
        exact congrArg (fun pair => pair.2.1) hpair
      exact ⟨rfl, hedge, Or.inl hsegment⟩
noncomputable def rxStarEdgeInteriorRawCopiedQPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : XStarEdge P x) (index : Fin (S.half - 1))
    (candidateX : P.X) (candidateCopy : Two)
    (candidateEdge : XStarEdge P candidateX) (segment : Fin S.half)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy edge index)
      (Vertex.q (Sum.inl ⟨candidateX,
        Sum.inl (candidateCopy, Sum.inl (candidateEdge, segment))⟩)) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index))
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxStarEdgeInteriorBeforeXStarFace P A4 S x copy edge index) 0))
      ⟨Vertex.q (Sum.inl ⟨candidateX,
        Sum.inl (candidateCopy, Sum.inl (candidateEdge, segment))⟩), member⟩ := by
  obtain ⟨howner, hnormalize⟩ := rxStarEdgeInteriorRawCopiedQ_normalize
    P S x copy edge index candidateX candidateCopy candidateEdge segment member
  subst candidateX
  obtain ⟨hcopy, hedge, hsegment⟩ := hnormalize rfl
  subst candidateCopy
  have hedge' : candidateEdge = edge := by simpa using hedge
  subst candidateEdge
  let owner := rxStarEdgeInteriorOwner P A4 x edge
  let corner := rxStarEdgeInteriorAlongCornerAt edge owner.1.2
  by_cases hbefore : segment = rxStarEdgeInteriorPreviousIndex S index
  · let target : RXStarEdgeInteriorTarget P x edge :=
      .small edge (.beforeQ owner.1.1 owner.1.2 owner.2 corner)
    let path := rxStarEdgeInteriorTargetBoundaryPath
      P A4 S x copy edge index target
    have hraw := rxStarEdgeInteriorBeforeAlongQAt
      P S x copy edge index owner.1.1 owner.1.2 owner.2
    have hraw' : localFaceQAt P S
          (rxStarEdgeInteriorBeforeLocalFaceAt
            P S x copy edge index owner.1.1 owner.1.2) corner =
        Sum.inl ⟨x, Sum.inl (copy, Sum.inl (edge, segment))⟩ := by
      rw [hbefore]
      exact hraw
    have htarget : rxStarEdgeInteriorTargetBoundaryVertex
          P A4 S x copy edge index target =
        ⟨Vertex.q (Sum.inl ⟨x,
          Sum.inl (copy, Sum.inl (edge, segment))⟩), member⟩ := by
      apply Subtype.ext
      exact congrArg Vertex.q hraw'
    exact htarget ▸ path
  · have hafter : segment = rxStarEdgeInteriorNextIndex S index := by
      rcases hsegment with hbefore' | hafter
      · exact False.elim (hbefore hbefore')
      · exact hafter
    let target : RXStarEdgeInteriorTarget P x edge :=
      .small edge (.afterQ owner.1.1 owner.1.2 owner.2 corner)
    let path := rxStarEdgeInteriorTargetBoundaryPath
      P A4 S x copy edge index target
    have hraw := rxStarEdgeInteriorAfterAlongQAt
      P S x copy edge index owner.1.1 owner.1.2 owner.2
    have hraw' : localFaceQAt P S
          (rxStarEdgeInteriorAfterLocalFaceAt
            P S x copy edge index owner.1.1 owner.1.2) corner =
        Sum.inl ⟨x, Sum.inl (copy, Sum.inl (edge, segment))⟩ := by
      rw [hafter]
      exact hraw
    have htarget : rxStarEdgeInteriorTargetBoundaryVertex
          P A4 S x copy edge index target =
        ⟨Vertex.q (Sum.inl ⟨x,
          Sum.inl (copy, Sum.inl (edge, segment))⟩), member⟩ := by
      apply Subtype.ext
      exact congrArg Vertex.q hraw'
    exact htarget ▸ path
theorem rxStarEdgeInteriorRawGlueQ_normalize
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1))
    (newQ : Σ q : P.Q, QDoubleCylinderVertex P q S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inr edge, edgeMember⟩ index)
      (Vertex.q (Sum.inr newQ)) = true) :
    (Sum.inr newQ : RX1 P S) = glueFaceQ1 P S
        (rxStarEdgeInteriorGlueBefore
          P A4 S x copy edge edgeMember index) ∨
      (Sum.inr newQ : RX1 P S) = glueFaceQ1 P S
        (rxStarEdgeInteriorGlueAfter
          P A4 S x copy edge edgeMember index) := by
  classical
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceQ = rxFaceQ P S from rfl]
    at member
  rw [decide_eq_true_eq] at member
  obtain ⟨candidate, hx, hqTag⟩ := member
  have hx' : rxFaceX P S candidate =
      rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inr edge, edgeMember⟩ index := by
    simp only [xStarFaceMember, decide_eq_true_eq] at hx
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
    exact hx
  rcases candidate with candidateLocal | candidateGlue | candidateOld
  · rcases hqTag with hqTag | hqTag <;>
      simp [rxFaceQ, localFaceQ0, localFaceQ1,
        localFaceQAt] at hqTag
  · rcases candidateGlue with ⟨a, qEdge, endpoint⟩
    rcases hqTag with hqTag | hqTag
    · simp [rxFaceQ, glueFaceQ0] at hqTag
    · rcases rxStarEdgeInteriorGlueFace_cases
          P A4 S x copy edge edgeMember index
            ⟨a, qEdge, endpoint⟩ (by simpa [rxFaceX] using hx') with
        hbefore | hafter
      · exact Or.inl (hqTag.trans
          (congrArg (glueFaceQ1 P S) hbefore))
      · exact Or.inr (hqTag.trans
          (congrArg (glueFaceQ1 P S) hafter))
  · rcases rxStarEdgeInteriorIncidentFace_cases
        P A4 S x copy ⟨Sum.inr edge, edgeMember⟩ index
          (Sum.inr (Sum.inr candidateOld)) hx' with
      ⟨face, side, hedge, hbefore | hafter⟩ |
      ⟨boundary, boundaryMember, hedge, houter⟩
    · cases hbefore
    · cases hafter
    · rcases houter with hbefore | houter
      · cases hbefore
      · rcases houter with hafter | houter
        · cases hafter
        · rcases houter with hbeforeGlue | hafterGlue
          · cases hbeforeGlue
          · cases hafterGlue
noncomputable def rxStarEdgeInteriorRawGlueQPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1))
    (newQ : Σ q : P.Q, QDoubleCylinderVertex P q S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inr edge, edgeMember⟩ index)
      (Vertex.q (Sum.inr newQ)) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy
          ⟨Sum.inr edge, edgeMember⟩ index))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy
          ⟨Sum.inr edge, edgeMember⟩ index))
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy
          ⟨Sum.inr edge, edgeMember⟩ index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxStarEdgeInteriorBeforeXStarFace P A4 S x copy
            ⟨Sum.inr edge, edgeMember⟩ index) 0))
      ⟨Vertex.q (Sum.inr newQ), member⟩ := by
  have hraw := rxStarEdgeInteriorRawGlueQ_normalize
    P A4 S x copy edge edgeMember index newQ member
  by_cases hbefore : (Sum.inr newQ : RX1 P S) = glueFaceQ1 P S
      (rxStarEdgeInteriorGlueBefore
        P A4 S x copy edge edgeMember index)
  · let target : RXStarEdgeInteriorTarget P x ⟨Sum.inr edge, edgeMember⟩ :=
      .glue edge edgeMember (.beforeQ 1)
    let path := rxStarEdgeInteriorTargetBoundaryPath
      P A4 S x copy ⟨Sum.inr edge, edgeMember⟩ index target
    have htarget : rxStarEdgeInteriorTargetBoundaryVertex
          P A4 S x copy ⟨Sum.inr edge, edgeMember⟩ index target =
        ⟨Vertex.q (Sum.inr newQ), member⟩ := by
      apply Subtype.ext
      exact congrArg Vertex.q hbefore.symm
    exact htarget ▸ path
  · have hafter : (Sum.inr newQ : RX1 P S) = glueFaceQ1 P S
        (rxStarEdgeInteriorGlueAfter
          P A4 S x copy edge edgeMember index) := by
      rcases hraw with hbefore' | hafter
      · exact False.elim (hbefore hbefore')
      · exact hafter
    let target : RXStarEdgeInteriorTarget P x ⟨Sum.inr edge, edgeMember⟩ :=
      .glue edge edgeMember (.afterQ 1)
    let path := rxStarEdgeInteriorTargetBoundaryPath
      P A4 S x copy ⟨Sum.inr edge, edgeMember⟩ index target
    have htarget : rxStarEdgeInteriorTargetBoundaryVertex
          P A4 S x copy ⟨Sum.inr edge, edgeMember⟩ index target =
        ⟨Vertex.q (Sum.inr newQ), member⟩ := by
      apply Subtype.ext
      exact congrArg Vertex.q hafter.symm
    exact htarget ▸ path
theorem rxStarEdgeInteriorRawGlueQ_radial_false
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : XQEdge P) (edgeMember : xStarEdgeMember P x (Sum.inl edge) = true)
    (index : Fin (S.half - 1))
    (newQ : Σ q : P.Q, QDoubleCylinderVertex P q S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inl edge, edgeMember⟩ index)
      (Vertex.q (Sum.inr newQ)) = true) : False := by
  classical
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceQ = rxFaceQ P S from rfl]
    at member
  rw [decide_eq_true_eq] at member
  obtain ⟨candidate, hx, hqTag⟩ := member
  have hx' : rxFaceX P S candidate =
      rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inl edge, edgeMember⟩ index := by
    simp only [xStarFaceMember, decide_eq_true_eq] at hx
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
    exact hx
  rcases rxStarEdgeInteriorIncidentFace_cases
      P A4 S x copy ⟨Sum.inl edge, edgeMember⟩ index candidate hx' with
    ⟨face, side, hedge, hbefore | hafter⟩ |
    ⟨boundary, boundaryMember, hedge, houter⟩
  · subst candidate
    rcases hqTag with hqTag | hqTag <;>
      simp [rxFaceQ, localFaceQ0, localFaceQ1,
        localFaceQAt] at hqTag
  · subst candidate
    rcases hqTag with hqTag | hqTag <;>
      simp [rxFaceQ, localFaceQ0, localFaceQ1,
        localFaceQAt] at hqTag
  · have hraw := congrArg Subtype.val hedge
    cases hraw
theorem rxStarEdgeInteriorRawVerticalQ_normalize
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) (candidateX : P.X)
    (boundaryVertex : SubdivisionBoundaryVertex P candidateX S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inr edge, edgeMember⟩ index)
      (Vertex.q (Sum.inl ⟨candidateX, Sum.inr boundaryVertex⟩)) = true) :
    candidateX = x ∧
      ∀ howner : candidateX = x,
        let transportedVertex : SubdivisionBoundaryVertex P x S :=
          howner ▸ boundaryVertex
        let rawQ : RX1 P S := Sum.inl ⟨x, Sum.inr transportedVertex⟩
        rawQ = localFaceQAt P S
            (rxStarEdgeInteriorRectangleBeforeLocalFace
              P S x copy edge edgeMember index) 0 ∨
          rawQ = localFaceQAt P S
            (rxStarEdgeInteriorRectangleBeforeLocalFace
              P S x copy edge edgeMember index) 1 ∨
          rawQ = localFaceQAt P S
            (rxStarEdgeInteriorRectangleAfterLocalFace
              P S x copy edge edgeMember index) 0 ∨
          rawQ = localFaceQAt P S
            (rxStarEdgeInteriorRectangleAfterLocalFace
              P S x copy edge edgeMember index) 1 ∨
          rawQ = glueFaceQ0 P S
            (rxStarEdgeInteriorGlueBefore
              P A4 S x copy edge edgeMember index) ∨
          rawQ = glueFaceQ1 P S
            (rxStarEdgeInteriorGlueBefore
              P A4 S x copy edge edgeMember index) ∨
          rawQ = glueFaceQ0 P S
            (rxStarEdgeInteriorGlueAfter
              P A4 S x copy edge edgeMember index) ∨
        rawQ = glueFaceQ1 P S
            (rxStarEdgeInteriorGlueAfter
              P A4 S x copy edge edgeMember index) := by
  classical
  obtain ⟨howner, hendpoint⟩ := rxStarEdgeInteriorRawLocalQ_endpoint
    P S x copy ⟨Sum.inr edge, edgeMember⟩ index
      candidateX (Sum.inr boundaryVertex) member
  subst candidateX
  refine ⟨rfl, ?_⟩
  intro howner'
  have hproof : howner' = (rfl : x = x) := Subsingleton.elim _ _
  cases hproof
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceQ = rxFaceQ P S from rfl]
    at member
  rw [decide_eq_true_eq] at member
  obtain ⟨candidate, hx, hqTag⟩ := member
  have hx' : rxFaceX P S candidate =
      rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inr edge, edgeMember⟩ index := by
    simp only [xStarFaceMember, decide_eq_true_eq] at hx
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
    exact hx
  rcases candidate with candidateLocal | candidateGlue | candidateOld
  · rcases candidateLocal with ⟨ownerX, localCell, material⟩
    have hownerX : ownerX = x := by
      rcases localCell with small | rectangle <;>
        simpa [rxFaceX, localFaceX, rxStarEdgeInteriorXCoordinate] using congrArg Sigma.fst hx'
    subst ownerX
    rcases localCell with small | rectangle
    · rcases hqTag with hqTag | hqTag
      · simp [rxFaceQ, localFaceQ0, localFaceQAt,
          localFaceQ0Edge, localFaceQ0EdgeAt] at hqTag
        have hsigma := Sum.inl.inj hqTag
        have hedge : (Sum.inr boundaryVertex : DoubleCylinderEdge P x S) =
            Sum.inl (small.1,
              subdivisionFaceBoundaryEdge P x S small.2 (0, material.2)) :=
          eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2
        cases hedge
      · simp [rxFaceQ, localFaceQ1, localFaceQAt,
          localFaceQ1Edge, localFaceQ1EdgeAt] at hqTag
        have hsigma := Sum.inl.inj hqTag
        have hedge : (Sum.inr boundaryVertex : DoubleCylinderEdge P x S) =
            Sum.inl (small.1,
              subdivisionFaceBoundaryEdge P x S small.2 (1, material.1)) :=
          eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2
        cases hedge
    · rcases rxStarEdgeInteriorRectangleFace_cases
          P S x copy edge edgeMember index rectangle material
            (by simpa [rxFaceX] using hx') with hbefore | hafter
      · rcases hqTag with hqTag | hqTag
        · left
          simp only [rxFaceQ] at hqTag
          exact hqTag.trans
            (congrArg (fun face => localFaceQAt P S face 0) hbefore)
        · right; left
          simp only [rxFaceQ] at hqTag
          exact hqTag.trans
            (congrArg (fun face => localFaceQAt P S face 1) hbefore)
      · rcases hqTag with hqTag | hqTag
        · right; right; left
          simp only [rxFaceQ] at hqTag
          exact hqTag.trans
            (congrArg (fun face => localFaceQAt P S face 0) hafter)
        · right; right; right; left
          simp only [rxFaceQ] at hqTag
          exact hqTag.trans
            (congrArg (fun face => localFaceQAt P S face 1) hafter)
  · rcases candidateGlue with ⟨⟨⟨ownerX, q⟩, hxq⟩, qEdge, endpoint⟩
    have hownerX : ownerX = x := congrArg Sigma.fst hx'
    subst ownerX
    rcases rxStarEdgeInteriorGlueFace_cases
        P A4 S x copy edge edgeMember index
          ⟨⟨(x, q), hxq⟩, qEdge, endpoint⟩
          (by simpa [rxFaceX] using hx') with hbefore | hafter
    · rcases hqTag with hqTag | hqTag
      · right; right; right; right; left
        simp only [rxFaceQ] at hqTag
        exact hqTag.trans
          (congrArg (glueFaceQ0 P S) hbefore)
      · simp [rxFaceQ, glueFaceQ1] at hqTag
    · rcases hqTag with hqTag | hqTag
      · right; right; right; right; right; right; left
        simp only [rxFaceQ] at hqTag
        exact hqTag.trans
          (congrArg (glueFaceQ0 P S) hafter)
      · simp [rxFaceQ, glueFaceQ1] at hqTag
  · rcases rxStarEdgeInteriorIncidentFace_cases
        P A4 S x copy ⟨Sum.inr edge, edgeMember⟩ index
          (Sum.inr (Sum.inr candidateOld)) hx' with
      ⟨face, side, hedge, hbefore | hafter⟩ |
      ⟨boundary, boundaryMember, hedge, houter⟩
    · cases hbefore
    · cases hafter
    · rcases houter with hbefore | houter
      · cases hbefore
      · rcases houter with hafter | houter
        · cases hafter
        · rcases houter with hbeforeGlue | hafterGlue
          · cases hbeforeGlue
          · cases hafterGlue
noncomputable def rxStarEdgeInteriorRawVerticalQTarget
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) (rawQ : RX1 P S) :
    RXStarEdgeInteriorTarget P x ⟨Sum.inr edge, edgeMember⟩ := by
  classical
  exact if rawQ = localFaceQAt P S
      (rxStarEdgeInteriorRectangleBeforeLocalFace
        P S x copy edge edgeMember index) 0 then
    .rectangle edge edgeMember (.beforeQ 0)
  else if rawQ = localFaceQAt P S
      (rxStarEdgeInteriorRectangleBeforeLocalFace
        P S x copy edge edgeMember index) 1 then
    .rectangle edge edgeMember (.beforeQ 1)
  else if rawQ = localFaceQAt P S
      (rxStarEdgeInteriorRectangleAfterLocalFace
        P S x copy edge edgeMember index) 0 then
    .rectangle edge edgeMember (.afterQ 0)
  else if rawQ = localFaceQAt P S
      (rxStarEdgeInteriorRectangleAfterLocalFace
        P S x copy edge edgeMember index) 1 then
    .rectangle edge edgeMember (.afterQ 1)
  else if rawQ = glueFaceQ0 P S
      (rxStarEdgeInteriorGlueBefore
        P A4 S x copy edge edgeMember index) then
    .glue edge edgeMember (.beforeQ 0)
  else if rawQ = glueFaceQ1 P S
      (rxStarEdgeInteriorGlueBefore
        P A4 S x copy edge edgeMember index) then
    .glue edge edgeMember (.beforeQ 1)
  else if rawQ = glueFaceQ0 P S
      (rxStarEdgeInteriorGlueAfter
        P A4 S x copy edge edgeMember index) then
    .glue edge edgeMember (.afterQ 0)
  else
    .glue edge edgeMember (.afterQ 1)
theorem rxStarEdgeInteriorRawVerticalQTarget_eq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1))
    (boundaryVertex : SubdivisionBoundaryVertex P x S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inr edge, edgeMember⟩ index)
      (Vertex.q (Sum.inl ⟨x, Sum.inr boundaryVertex⟩)) = true) :
    rxStarEdgeInteriorTargetBoundaryVertex P A4 S x copy
        ⟨Sum.inr edge, edgeMember⟩ index
        (rxStarEdgeInteriorRawVerticalQTarget P A4 S x copy
          edge edgeMember index (Sum.inl ⟨x, Sum.inr boundaryVertex⟩)) =
      ⟨Vertex.q (Sum.inl ⟨x, Sum.inr boundaryVertex⟩), member⟩ := by
  have hcases := (rxStarEdgeInteriorRawVerticalQ_normalize
    P A4 S x copy edge edgeMember index x boundaryVertex member).2 rfl
  unfold rxStarEdgeInteriorRawVerticalQTarget
  split <;> rename_i h0
  · apply Subtype.ext
    exact congrArg Vertex.q h0.symm
  · split <;> rename_i h1
    · apply Subtype.ext
      exact congrArg Vertex.q h1.symm
    · split <;> rename_i h2
      · apply Subtype.ext
        exact congrArg Vertex.q h2.symm
      · split <;> rename_i h3
        · apply Subtype.ext
          exact congrArg Vertex.q h3.symm
        · split <;> rename_i h4
          · apply Subtype.ext
            exact congrArg Vertex.q h4.symm
          · split <;> rename_i h5
            · apply Subtype.ext
              exact congrArg Vertex.q h5.symm
            · split <;> rename_i h6
              · apply Subtype.ext
                exact congrArg Vertex.q h6.symm
              · have h7 : (Sum.inl ⟨x, Sum.inr boundaryVertex⟩ : RX1 P S) =
                    glueFaceQ1 P S (rxStarEdgeInteriorGlueAfter
                      P A4 S x copy edge edgeMember index) := by
                  rcases hcases with h | h | h | h | h | h | h | h
                  · exact False.elim (h0 h)
                  · exact False.elim (h1 h)
                  · exact False.elim (h2 h)
                  · exact False.elim (h3 h)
                  · exact False.elim (h4 h)
                  · exact False.elim (h5 h)
                  · exact False.elim (h6 h)
                  · exact h
                apply Subtype.ext
                exact congrArg Vertex.q h7.symm
noncomputable def rxStarEdgeInteriorRawVerticalQPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) (candidateX : P.X)
    (boundaryVertex : SubdivisionBoundaryVertex P candidateX S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inr edge, edgeMember⟩ index)
      (Vertex.q (Sum.inl ⟨candidateX, Sum.inr boundaryVertex⟩)) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy
          ⟨Sum.inr edge, edgeMember⟩ index))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy
          ⟨Sum.inr edge, edgeMember⟩ index))
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy
          ⟨Sum.inr edge, edgeMember⟩ index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxStarEdgeInteriorBeforeXStarFace P A4 S x copy
            ⟨Sum.inr edge, edgeMember⟩ index) 0))
      ⟨Vertex.q (Sum.inl ⟨candidateX, Sum.inr boundaryVertex⟩), member⟩ := by
  obtain ⟨howner, hendpoint⟩ := rxStarEdgeInteriorRawLocalQ_endpoint
    P S x copy ⟨Sum.inr edge, edgeMember⟩ index
      candidateX (Sum.inr boundaryVertex) member
  subst candidateX
  let target := rxStarEdgeInteriorRawVerticalQTarget
    P A4 S x copy edge edgeMember index
      (Sum.inl ⟨x, Sum.inr boundaryVertex⟩)
  let path := rxStarEdgeInteriorTargetBoundaryPath
    P A4 S x copy ⟨Sum.inr edge, edgeMember⟩ index target
  exact (rxStarEdgeInteriorRawVerticalQTarget_eq
    P A4 S x copy edge edgeMember index boundaryVertex member) ▸ path
theorem rxStarEdgeInteriorRawVerticalQ_false
    (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (copy : Two) (edge : XQEdge P)
    (edgeMember : xStarEdgeMember P x (Sum.inl edge) = true)
    (index : Fin (S.half - 1)) (candidateX : P.X)
    (boundaryVertex : SubdivisionBoundaryVertex P candidateX S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy
        ⟨Sum.inl edge, edgeMember⟩ index)
      (Vertex.q (Sum.inl ⟨candidateX, Sum.inr boundaryVertex⟩)) = true) :
    False := by
  obtain ⟨howner, hendpoint⟩ := rxStarEdgeInteriorRawLocalQ_endpoint
    P S x copy ⟨Sum.inl edge, edgeMember⟩ index
      candidateX (Sum.inr boundaryVertex) member
  subst candidateX
  rcases hendpoint rfl with hstart | hend
  · have hsubdivision := congrArg Prod.snd hstart
    simp [tannerDoubleCylinderEdgeStart,
      subdivisionOriginalBoundaryVertex] at hsubdivision
    have hboundary := boundaryVertex.2
    rw [hsubdivision] at hboundary
    simp [subdivisionBoundaryVertexMember,
      xStarBoundaryEdgeMember] at hboundary
  · have hsubdivision := congrArg Prod.snd hend
    simp [tannerDoubleCylinderEdgeEnd,
      subdivisionOriginalBoundaryVertex] at hsubdivision
    have hboundary := boundaryVertex.2
    rw [hsubdivision] at hboundary
    simp [subdivisionBoundaryVertexMember,
      xStarBoundaryEdgeMember] at hboundary
def rxStarEdgeInteriorRawInteriorFace
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) :
    ((XStarFace P x × Fin S.half × Fin (S.half - 1)) ⊕
      (XStarFace P x × Fin (S.half - 1) × Fin S.half)) →
        XStarFace P x
  | Sum.inl horizontal => horizontal.1
  | Sum.inr vertical => vertical.1
def rxStarEdgeInteriorRawInteriorQCorner
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) :
    ((XStarFace P x × Fin S.half × Fin (S.half - 1)) ⊕
      (XStarFace P x × Fin (S.half - 1) × Fin S.half)) → Two
  | Sum.inl _ => 0
  | Sum.inr _ => 1
noncomputable def rxStarEdgeInteriorRawInteriorQOwner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (candidateCopy : Two)
    (interior :
      (XStarFace P x × Fin S.half × Fin (S.half - 1)) ⊕
        (XStarFace P x × Fin (S.half - 1) × Fin S.half)) :
    {owned : RXLocalFace P S × Two //
      localFaceQAt P S owned.1 owned.2 =
          Sum.inl ⟨x, Sum.inl (candidateCopy, Sum.inr interior)⟩ ∧
        rxStarEdgeInteriorRawLocalOldFace? P S owned.1 =
          some (rxStarEdgeInteriorRawInteriorFace P S x interior).1 ∧
        owned.2 = rxStarEdgeInteriorRawInteriorQCorner P S x interior} := by
  rcases interior with horizontal | vertical
  · let owner := rxLocalEdgeCornerOwner P
      A4.toTannerSquareAdmissibleV3 S x
        (Sum.inl (candidateCopy, Sum.inr (Sum.inl horizontal)))
    refine ⟨owner.1, owner.2, ?_, ?_⟩
    · simp [owner, rxLocalEdgeCornerOwner,
        rxStarEdgeInteriorRawLocalOldFace?,
        rxStarEdgeInteriorRawInteriorFace]
    · simp [owner, rxLocalEdgeCornerOwner,
        rxStarEdgeInteriorRawInteriorQCorner]
  · let owner := rxLocalEdgeCornerOwner P
      A4.toTannerSquareAdmissibleV3 S x
        (Sum.inl (candidateCopy, Sum.inr (Sum.inr vertical)))
    refine ⟨owner.1, owner.2, ?_, ?_⟩
    · simp [owner, rxLocalEdgeCornerOwner,
        rxStarEdgeInteriorRawLocalOldFace?,
        rxStarEdgeInteriorRawInteriorFace]
    · simp [owner, rxLocalEdgeCornerOwner,
        rxStarEdgeInteriorRawInteriorQCorner]
theorem rxStarEdgeInteriorRawInteriorQ_normalize
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1)) (candidateX : P.X)
    (candidateCopy : Two)
    (interior :
      (XStarFace P candidateX × Fin S.half × Fin (S.half - 1)) ⊕
        (XStarFace P candidateX × Fin (S.half - 1) × Fin S.half))
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy edge index)
      (Vertex.q (Sum.inl ⟨candidateX,
        Sum.inl (candidateCopy, Sum.inr interior)⟩)) = true) :
    candidateX = x ∧
      ∀ howner : candidateX = x,
        let transportedInterior := howner ▸ interior
        let face := rxStarEdgeInteriorRawInteriorFace
          P S x transportedInterior
        let side := rxStarEdgeInteriorRawSide P x edge face
        let corner := rxStarEdgeInteriorRawInteriorQCorner
          P S x transportedInterior
        rxStarEdgeInteriorFaceEdgeAt P x edge face side = edge ∧
          ((Sum.inl ⟨x,
              Sum.inl (candidateCopy, Sum.inr transportedInterior)⟩ :
                RX1 P S) =
              localFaceQAt P S
                (rxStarEdgeInteriorBeforeLocalFaceAt
                  P S x copy edge index face side) corner ∨
            (Sum.inl ⟨x,
              Sum.inl (candidateCopy, Sum.inr transportedInterior)⟩ :
                RX1 P S) =
              localFaceQAt P S
                (rxStarEdgeInteriorAfterLocalFaceAt
                  P S x copy edge index face side) corner) := by
  classical
  obtain ⟨howner, hendpoint⟩ := rxStarEdgeInteriorRawLocalQ_endpoint
    P S x copy edge index candidateX
      (Sum.inl (candidateCopy, Sum.inr interior)) member
  subst candidateX
  refine ⟨rfl, ?_⟩
  intro howner'
  have hproof : howner' = (rfl : x = x) := Subsingleton.elim _ _
  cases hproof
  let rawEdge : DoubleCylinderEdge P x S :=
    Sum.inl (candidateCopy, Sum.inr interior)
  let coordinate : DoubleCylinderVertex P x S :=
    (copy, Sum.inr (Sum.inl (edge, index)))
  let endpoint : Two :=
    if tannerDoubleCylinderEdgeStart P x S rawEdge = coordinate then 0 else 1
  have hselectedEndpoint : edgeEndpoint
      (tannerDoubleCylinderEdgeStart P x S)
      (tannerDoubleCylinderEdgeEnd P x S) rawEdge endpoint = coordinate := by
    unfold endpoint
    split <;> rename_i hstart
    · simpa [edgeEndpoint] using hstart
    · have hend : tannerDoubleCylinderEdgeEnd P x S rawEdge =
          coordinate := by
        rcases hendpoint rfl with hstart' | hend
        · exact False.elim (hstart hstart')
        · exact hend
      simpa [edgeEndpoint] using hend
  generalize howned : rxStarEdgeInteriorRawInteriorQOwner
    P A4 S x candidateCopy interior = owned
  rcases owned with
    ⟨⟨⟨ownerX, localCell, materialCorner⟩, qCorner⟩,
      hq, holdFace, hqCorner⟩
  have hsigma : (⟨ownerX,
      if qCorner = 0 then
        localFaceQ0EdgeAt P ownerX S localCell materialCorner
      else localFaceQ1EdgeAt P ownerX S localCell materialCorner⟩ :
        Σ ownerX : P.X, DoubleCylinderEdge P ownerX S) =
      ⟨x, rawEdge⟩ := by
    fin_cases qCorner
    · simpa [localFaceQAt, localFaceQ0, localFaceQ0Edge,
        rawEdge] using hq
    · simpa [localFaceQAt, localFaceQ1, localFaceQ1Edge,
        rawEdge] using hq
  have hownerX : ownerX = x := congrArg Sigma.fst hsigma
  subst ownerX
  change qCorner =
    rxStarEdgeInteriorRawInteriorQCorner P S x interior at hqCorner
  have hsmallCell : ∃ small : Two × SubdivisionFace P x S,
      localCell = Sum.inl small := by
    rcases localCell with small | rectangle
    · exact ⟨small, rfl⟩
    · simp [rxStarEdgeInteriorRawLocalOldFace?] at holdFace
  obtain ⟨small, rfl⟩ := hsmallCell
  have hedge :
      (if qCorner = 0 then
        localFaceQ0EdgeAt P x S (Sum.inl small) materialCorner
      else localFaceQ1EdgeAt P x S (Sum.inl small) materialCorner) = rawEdge :=
    eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2
  let selected : RXLocalFace P S :=
    ⟨x, Sum.inl small, localMaterialCornerAtEndpoint
      P x S (Sum.inl small) materialCorner qCorner endpoint⟩
  have hselectedX : localFaceX P S selected =
      rxStarEdgeInteriorXCoordinate P S x copy edge index := by
    rw [show localFaceX P S selected =
        ⟨x, edgeEndpoint (tannerDoubleCylinderEdgeStart P x S)
          (tannerDoubleCylinderEdgeEnd P x S)
          (if qCorner = 0 then
            localFaceQ0EdgeAt P x S (Sum.inl small) materialCorner
          else localFaceQ1EdgeAt P x S (Sum.inl small) materialCorner) endpoint⟩ by
      exact localFaceX_atEndpoint
        P x S (Sum.inl small) materialCorner qCorner endpoint]
    rw [hedge]
    exact congrArg (fun vertex : DoubleCylinderVertex P x S =>
      (⟨x, vertex⟩ : RX0 P S)) hselectedEndpoint
  have hselectedQ : localFaceQAt P S selected qCorner =
      (Sum.inl ⟨x, rawEdge⟩ : RX1 P S) := by
    change localFaceQAt P S
        ⟨x, Sum.inl small, localMaterialCornerAtEndpoint
          P x S (Sum.inl small) materialCorner qCorner endpoint⟩ qCorner = _
    have hpreserved := localFaceQ_atEndpoint P x S (Sum.inl small)
      materialCorner qCorner endpoint
    simpa [localFaceQAt, rawEdge] using hpreserved.trans hq
  have hselectedOldFace :
      rxStarEdgeInteriorRawLocalOldFace? P S selected =
        some (rxStarEdgeInteriorRawInteriorFace P S x interior).1 := by
    simpa [selected, rxStarEdgeInteriorRawLocalOldFace?] using holdFace
  have hsmall : ∃ copyFace : Two × SubdivisionFace P x S,
      selected.2.1 = Sum.inl copyFace := by
    exact ⟨small, rfl⟩
  obtain ⟨targetFace, targetSide, hmatch, hbefore | hafter⟩ :=
    rxStarEdgeInteriorLocalFace_cases P S x copy edge index
      selected hselectedX hsmall
  · have hfaceValue :
        (rxStarEdgeInteriorRawInteriorFace P S x interior).1 =
          targetFace.1 := by
      have hfaceOption := congrArg
        (rxStarEdgeInteriorRawLocalOldFace? P S) hbefore
      rw [hselectedOldFace] at hfaceOption
      rcases edge with ⟨radial | boundary, edgeMember⟩ <;>
        fin_cases targetSide <;>
        simpa [rxStarEdgeInteriorRawLocalOldFace?,
          rxStarEdgeInteriorBeforeLocalFaceAt, rxTwoElim] using hfaceOption
    have hface : rxStarEdgeInteriorRawInteriorFace P S x interior =
        targetFace := Subtype.ext hfaceValue
    subst targetFace
    have hedge' := rxStarEdgeInteriorFaceEdgeAt_eq_of_match
      P x edge (rxStarEdgeInteriorRawInteriorFace P S x interior)
        targetSide hmatch
    have hside := rxStarEdgeInteriorRawSide_edge P x edge
      (rxStarEdgeInteriorRawInteriorFace P S x interior) targetSide hedge'
    refine ⟨hside, Or.inl ?_⟩
    have hsideEq := rxStarEdgeInteriorRawSide_eq P x edge
      (rxStarEdgeInteriorRawInteriorFace P S x interior) targetSide hedge'
    rw [hsideEq]
    rw [hqCorner] at hselectedQ
    exact hselectedQ.symm.trans
      (congrArg (fun candidate => localFaceQAt P S candidate
        (rxStarEdgeInteriorRawInteriorQCorner P S x interior)) hbefore)
  · have hfaceValue :
        (rxStarEdgeInteriorRawInteriorFace P S x interior).1 =
          targetFace.1 := by
      have hfaceOption := congrArg
        (rxStarEdgeInteriorRawLocalOldFace? P S) hafter
      rw [hselectedOldFace] at hfaceOption
      rcases edge with ⟨radial | boundary, edgeMember⟩ <;>
        fin_cases targetSide <;>
        simpa [rxStarEdgeInteriorRawLocalOldFace?,
          rxStarEdgeInteriorAfterLocalFaceAt, rxTwoElim] using hfaceOption
    have hface : rxStarEdgeInteriorRawInteriorFace P S x interior =
        targetFace := Subtype.ext hfaceValue
    subst targetFace
    have hedge' := rxStarEdgeInteriorFaceEdgeAt_eq_of_match
      P x edge (rxStarEdgeInteriorRawInteriorFace P S x interior)
        targetSide hmatch
    have hside := rxStarEdgeInteriorRawSide_edge P x edge
      (rxStarEdgeInteriorRawInteriorFace P S x interior) targetSide hedge'
    refine ⟨hside, Or.inr ?_⟩
    have hsideEq := rxStarEdgeInteriorRawSide_eq P x edge
      (rxStarEdgeInteriorRawInteriorFace P S x interior) targetSide hedge'
    rw [hsideEq]
    rw [hqCorner] at hselectedQ
    exact hselectedQ.symm.trans
      (congrArg (fun candidate => localFaceQAt P S candidate
        (rxStarEdgeInteriorRawInteriorQCorner P S x interior)) hafter)
noncomputable def rxStarEdgeInteriorRawInteriorQPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1)) (candidateX : P.X)
    (candidateCopy : Two)
    (interior :
      (XStarFace P candidateX × Fin S.half × Fin (S.half - 1)) ⊕
        (XStarFace P candidateX × Fin (S.half - 1) × Fin S.half))
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy edge index)
      (Vertex.q (Sum.inl ⟨candidateX,
        Sum.inl (candidateCopy, Sum.inr interior)⟩)) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index))
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxStarEdgeInteriorXCoordinate P S x copy edge index)
          (rxStarEdgeInteriorBeforeXStarFace
            P A4 S x copy edge index) 0))
      ⟨Vertex.q (Sum.inl ⟨candidateX,
        Sum.inl (candidateCopy, Sum.inr interior)⟩), member⟩ := by
  obtain ⟨howner, hnormalize⟩ :=
    rxStarEdgeInteriorRawInteriorQ_normalize
      P A4 S x copy edge index candidateX candidateCopy interior member
  subst candidateX
  let face := rxStarEdgeInteriorRawInteriorFace P S x interior
  let side := rxStarEdgeInteriorRawSide P x edge face
  let corner := rxStarEdgeInteriorRawInteriorQCorner P S x interior
  have hedge := (hnormalize rfl).1
  have hedge' :
      (match edge.1 with
        | Sum.inl _ => xStarFaceXQEdge P x face side = edge
        | Sum.inr _ => xStarFaceQZEdge P x face side = edge) := by
    exact rxStarEdgeInteriorFaceEdgeAt_match_of_eq
      P x edge face side hedge
  by_cases hbefore :
      (Sum.inl ⟨x, Sum.inl (candidateCopy, Sum.inr interior)⟩ :
          RX1 P S) =
        localFaceQAt P S
          (rxStarEdgeInteriorBeforeLocalFaceAt
            P S x copy edge index face side) corner
  · let target : RXStarEdgeInteriorTarget P x edge :=
      .small edge (.beforeQ face side hedge' corner)
    let path := rxStarEdgeInteriorTargetBoundaryPath
      P A4 S x copy edge index target
    have htarget : rxStarEdgeInteriorTargetBoundaryVertex
          P A4 S x copy edge index target =
        ⟨Vertex.q (Sum.inl ⟨x,
          Sum.inl (candidateCopy, Sum.inr interior)⟩), member⟩ := by
      apply Subtype.ext
      exact congrArg Vertex.q hbefore.symm
    exact htarget ▸ path
  · have hafter :
        (Sum.inl ⟨x, Sum.inl (candidateCopy, Sum.inr interior)⟩ :
            RX1 P S) =
          localFaceQAt P S
            (rxStarEdgeInteriorAfterLocalFaceAt
              P S x copy edge index face side) corner := by
      rcases (hnormalize rfl).2 with hbefore' | hafter
      · exact False.elim (hbefore hbefore')
      · exact hafter
    let target : RXStarEdgeInteriorTarget P x edge :=
      .small edge (.afterQ face side hedge' corner)
    let path := rxStarEdgeInteriorTargetBoundaryPath
      P A4 S x copy edge index target
    have htarget : rxStarEdgeInteriorTargetBoundaryVertex
          P A4 S x copy edge index target =
        ⟨Vertex.q (Sum.inl ⟨x,
          Sum.inl (candidateCopy, Sum.inr interior)⟩), member⟩ := by
      apply Subtype.ext
      exact congrArg Vertex.q hafter.symm
    exact htarget ▸ path
noncomputable def rxStarEdgeInteriorRawQPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1)) (newQ : RX1 P S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy edge index)
      (Vertex.q newQ) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index))
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxStarEdgeInteriorXCoordinate P S x copy edge index)
          (rxStarEdgeInteriorBeforeXStarFace
            P A4 S x copy edge index) 0))
      ⟨Vertex.q newQ, member⟩ := by
  rcases newQ with localEdge | qVertex
  · rcases localEdge with ⟨candidateX, candidateEdge⟩
    rcases candidateEdge with copied | boundaryVertex
    · rcases copied with ⟨candidateCopy, subdivisionEdge⟩
      rcases subdivisionEdge with original | interior
      · rcases original with ⟨candidateStarEdge, segment⟩
        exact rxStarEdgeInteriorRawCopiedQPath
          P A4 S x copy edge index candidateX candidateCopy
            candidateStarEdge segment member
      · exact rxStarEdgeInteriorRawInteriorQPath
          P A4 S x copy edge index candidateX candidateCopy interior member
    · rcases edge with ⟨storedRadial | storedBoundary, storedMember⟩
      · exact False.elim (rxStarEdgeInteriorRawVerticalQ_false
          P S x copy storedRadial storedMember index
            candidateX boundaryVertex member)
      · exact rxStarEdgeInteriorRawVerticalQPath
          P A4 S x copy storedBoundary storedMember index
            candidateX boundaryVertex member
  · rcases edge with ⟨storedRadial | storedBoundary, storedMember⟩
    · exact False.elim (rxStarEdgeInteriorRawGlueQ_radial_false
        P A4 S x copy storedRadial storedMember index qVertex member)
    · exact rxStarEdgeInteriorRawGlueQPath
        P A4 S x copy storedBoundary storedMember index qVertex member
noncomputable def rxStarEdgeInteriorBoundaryPathFromAnchor
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1))
    (vertex : XStarBoundaryVertex (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy edge index)) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index))
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxStarEdgeInteriorXCoordinate P S x copy edge index)
          (rxStarEdgeInteriorBeforeXStarFace
            P A4 S x copy edge index) 0))
      vertex := by
  rcases vertex with ⟨value, member⟩
  rcases value with newX | newQ | newZ
  · simp [xStarBoundaryVertexMember] at member
  · exact rxStarEdgeInteriorRawQPath
      P A4 S x copy edge index newQ member
  · exact rxStarEdgeInteriorRawZPath
      P A4 S x copy edge index newZ member
noncomputable def rxReplacementXBoundaryPathStarEdge
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : XStarEdge P x)
    (index : Fin (S.half - 1))
    (vertex : XStarBoundaryVertex (rxReplacementPresentation P S)
      (rxStarEdgeInteriorXCoordinate P S x copy edge index)) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxStarEdgeInteriorXCoordinate P S x copy edge index))
      (rxReplacementXBoundaryRoot P
        A4.toTannerSquareAdmissibleV3 S
        (rxStarEdgeInteriorXCoordinate P S x copy edge index))
      vertex := by
  let rootFromAnchor := rxStarEdgeInteriorBoundaryPathFromAnchor
    P A4 S x copy edge index
      (rxReplacementXBoundaryRoot P
        A4.toTannerSquareAdmissibleV3 S
        (rxStarEdgeInteriorXCoordinate P S x copy edge index))
  let targetFromAnchor := rxStarEdgeInteriorBoundaryPathFromAnchor
    P A4 S x copy edge index vertex
  exact rootFromAnchor.reverse.append targetFromAnchor
noncomputable def rxOriginalBoundaryQRootBoundaryEdge
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (x : P.X) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    XStarBoundaryEdge P x :=
  rxStarEdgeInteriorBoundaryEdge P x
    (rxOriginalBoundaryQRootOwner P A4 x q member).1.edge
    (rxOriginalBoundaryQRootOwner P A4 x q member).1.member
noncomputable def rxOriginalBoundaryQRootRectangle
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    SubdivisionBoundaryEdge P x S :=
  subdivisionOriginalBoundaryEdge P x S
    (rxOriginalBoundaryQRootBoundaryEdge P A4 x q member)
    (rxRadialGridZero S)
noncomputable def rxOriginalBoundaryQRootLocalFace
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    RXLocalFace P S :=
  ⟨x, Sum.inr (rxOriginalBoundaryQRootRectangle P A4 S x q member),
    (copy, 0)⟩
theorem rxOriginalBoundaryQRootLocalFace_x
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    localFaceX P S
        (rxOriginalBoundaryQRootLocalFace P A4 S x copy q member) =
      rxOriginalBoundaryQXCoordinate P S x copy q member := by
  simp [rxOriginalBoundaryQRootLocalFace,
    rxOriginalBoundaryQRootRectangle,
    rxOriginalBoundaryQRootBoundaryEdge,
    rxStarEdgeInteriorBoundaryEdge,
    subdivisionOriginalBoundaryEdge, localFaceX,
    doubleCylinderRectangleCorner, subdivisionBoundaryEdgeStart,
    subdivisionEdgeStart, subdivisionSegmentStart, rxRadialGridZero]
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Prod.ext
    · rfl
    · apply congrArg Sum.inl
      apply Subtype.ext
      change Vertex.q
          (rxOriginalBoundaryQRootOwner P A4 x q member).1.edge.1.1 =
        Vertex.q q
      exact congrArg Vertex.q
        (rxOriginalBoundaryQRootOwner P A4 x q member).2
noncomputable def rxOriginalBoundaryQRootXStarFace
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    XStarFace (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q member) :=
  ⟨Sum.inl (rxOriginalBoundaryQRootLocalFace P A4 S x copy q member), by
    simp only [xStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    exact rxOriginalBoundaryQRootLocalFace_x P A4 S x copy q member⟩
noncomputable def rxOriginalBoundaryQLocalFaceAt
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (face : XStarFace P x) (corner : Two) : RXLocalFace P S :=
  rxTwoElim (motive := fun _ => RXLocalFace P S)
    ⟨x, Sum.inl (copy, (face, rxStarEdgeInteriorLastIndex S,
      rxRadialGridZero S)), (1, 0)⟩
    ⟨x, Sum.inl (copy, (face, rxRadialGridZero S,
      rxStarEdgeInteriorLastIndex S)), (0, 1)⟩ corner
theorem rxOriginalBoundaryQLocalFaceAt_x
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (face : XStarFace P x) (corner : Two)
    (hq : P.faceQ face.1 corner = q) :
    localFaceX P S (rxOriginalBoundaryQLocalFaceAt
        P S x copy face corner) =
      rxOriginalBoundaryQXCoordinate P S x copy q member := by
  have hlast : S.half - 1 + 1 = S.half := by
    have := S.half_pos
    omega
  fin_cases corner <;>
    simp [rxOriginalBoundaryQLocalFaceAt, rxTwoElim, localFaceX,
      gridEndpoint, lowerGridIndex, upperGridIndex,
      rxStarEdgeInteriorLastIndex, rxRadialGridZero, hlast,
      rxOriginalBoundaryQXCoordinate] at hq ⊢
  all_goals
    simp only [subdivisionGridVertex]
    simp [Nat.ne_of_gt S.half_pos]
    apply Subtype.ext
    exact congrArg Vertex.q hq
noncomputable def rxOriginalBoundaryQOwnerLocalFace
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    RXLocalFace P S :=
  rxOriginalBoundaryQLocalFaceAt P S x copy
    (rxOriginalBoundaryQRootFace P A4 x q member)
    (rxOriginalBoundaryQRootCorner P A4 x q member)
theorem rxOriginalBoundaryQOwnerLocalFace_x
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    localFaceX P S
        (rxOriginalBoundaryQOwnerLocalFace P A4 S x copy q member) =
      rxOriginalBoundaryQXCoordinate P S x copy q member := by
  exact rxOriginalBoundaryQLocalFaceAt_x P S x copy q member _ _
    (rxOriginalBoundaryQRootFace_q P A4 x q member)
noncomputable def rxOriginalBoundaryQOwnerXStarFace
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    XStarFace (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q member) :=
  ⟨Sum.inl (rxOriginalBoundaryQOwnerLocalFace P A4 S x copy q member), by
    simp only [xStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    exact rxOriginalBoundaryQOwnerLocalFace_x P A4 S x copy q member⟩
theorem rxOriginalBoundaryQRootRectangleQ0
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    localFaceQAt P S
        (rxOriginalBoundaryQRootLocalFace P A4 S x copy q member) 0 =
      Sum.inl ⟨x, Sum.inl (copy, Sum.inl
        (⟨Sum.inr
          (rxOriginalBoundaryQRootOwner P A4 x q member).1.edge,
          (rxOriginalBoundaryQRootOwner P A4 x q member).1.member⟩,
          rxRadialGridZero S))⟩ := by
  simp [rxOriginalBoundaryQRootLocalFace, localFaceQAt,
    localFaceQ0, localFaceQ0Edge, localFaceQ0EdgeAt,
    rxOriginalBoundaryQRootRectangle,
    rxOriginalBoundaryQRootBoundaryEdge,
    rxStarEdgeInteriorBoundaryEdge, subdivisionOriginalBoundaryEdge]
  apply Subtype.ext
  rfl
theorem rxOriginalBoundaryQRootRectangleQ1
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    localFaceQAt P S
        (rxOriginalBoundaryQRootLocalFace P A4 S x copy q member) 1 =
      Sum.inl ⟨x, Sum.inr
        (subdivisionOriginalBoundaryVertex P x S ⟨Vertex.q q, member⟩)⟩ := by
  simp [rxOriginalBoundaryQRootLocalFace, localFaceQAt,
    localFaceQ1, localFaceQ1Edge, localFaceQ1EdgeAt,
    rxOriginalBoundaryQRootRectangle,
    rxOriginalBoundaryQRootBoundaryEdge,
    rxStarEdgeInteriorBoundaryEdge, subdivisionOriginalBoundaryEdge,
    subdivisionBoundaryEdgeStart, subdivisionEdgeStart,
    subdivisionSegmentStart, rxRadialGridZero]
  congr 4
  apply Subtype.ext
  change Vertex.q
      (rxOriginalBoundaryQRootOwner P A4 x q member).1.edge.1.1 = Vertex.q q
  exact congrArg Vertex.q
    (rxOriginalBoundaryQRootOwner P A4 x q member).2
theorem rxOriginalBoundaryQLocalFaceAtBoundaryQ
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (face : XStarFace P x) (corner : Two) (edge : XStarEdge P x)
    (hedge : xStarFaceQZEdge P x face corner = edge) :
    localFaceQAt P S
        (rxOriginalBoundaryQLocalFaceAt P S x copy face corner)
        (flipEndpoint corner) =
      Sum.inl ⟨x, Sum.inl (copy, Sum.inl
        (edge, rxRadialGridZero S))⟩ := by
  have hlast : S.half - 1 + 1 = S.half := by
    have := S.half_pos
    omega
  fin_cases corner
  · simp [rxOriginalBoundaryQLocalFaceAt, rxTwoElim_zero, rxTwoElim_one, flipEndpoint,
      localFaceQAt, localFaceQ1, localFaceQ1Edge, localFaceQ1EdgeAt,
      subdivisionFaceBoundaryEdge_one_one,
      subdivisionVerticalEdge, rxStarEdgeInteriorLastIndex,
      rxRadialGridZero, hlast] at hedge ⊢
    split <;> rename_i hzero
    · have hzeroValue := congrArg Fin.val hzero
      change S.half - 1 + 1 = 0 at hzeroValue
      omega
    · split <;> rename_i hboundary
      · exact congrArg (fun selected : XStarEdge P x =>
          (Sum.inl ⟨x, Sum.inl (copy, Sum.inl
            (selected, rxRadialGridZero S))⟩ : RX1 P S)) hedge
      · exfalso
        apply hboundary
        change S.half - 1 + 1 = S.half
        omega
  · simp [rxOriginalBoundaryQLocalFaceAt, rxTwoElim_zero, rxTwoElim_one, flipEndpoint,
      localFaceQAt, localFaceQ0, localFaceQ0Edge, localFaceQ0EdgeAt,
      subdivisionFaceBoundaryEdge_zero_one,
      subdivisionHorizontalEdge, rxStarEdgeInteriorLastIndex,
      rxRadialGridZero, hlast] at hedge ⊢
    split <;> rename_i hzero
    · have hzeroValue := congrArg Fin.val hzero
      change S.half - 1 + 1 = 0 at hzeroValue
      omega
    · split <;> rename_i hboundary
      · exact congrArg (fun selected : XStarEdge P x =>
          (Sum.inl ⟨x, Sum.inl (copy, Sum.inl
            (selected, rxRadialGridZero S))⟩ : RX1 P S)) hedge
      · exfalso
        apply hboundary
        change S.half - 1 + 1 = S.half
        omega
theorem rxOriginalBoundaryQOwnerBoundaryQ
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    localFaceQAt P S
        (rxOriginalBoundaryQOwnerLocalFace P A4 S x copy q member)
        (flipEndpoint (rxOriginalBoundaryQRootCorner P A4 x q member)) =
      localFaceQAt P S
        (rxOriginalBoundaryQRootLocalFace P A4 S x copy q member) 0 := by
  exact (rxOriginalBoundaryQLocalFaceAtBoundaryQ P S x copy
    (rxOriginalBoundaryQRootFace P A4 x q member)
    (rxOriginalBoundaryQRootCorner P A4 x q member)
    ⟨Sum.inr (rxOriginalBoundaryQRootOwner P A4 x q member).1.edge,
      (rxOriginalBoundaryQRootOwner P A4 x q member).1.member⟩
    (rxOriginalBoundaryQRootOwner P A4 x q member).1.edgeExact).trans
    (rxOriginalBoundaryQRootRectangleQ0 P A4 S x copy q member).symm
theorem rxOriginalBoundaryQOwnerBoundaryVertexEq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q member)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxOriginalBoundaryQXCoordinate P S x copy q member)
          (rxOriginalBoundaryQOwnerXStarFace P A4 S x copy q member)
          (flipEndpoint (rxOriginalBoundaryQRootCorner P A4 x q member))) =
      xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q member)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxOriginalBoundaryQXCoordinate P S x copy q member)
          (rxOriginalBoundaryQRootXStarFace P A4 S x copy q member) 0) := by
  apply Subtype.ext
  exact congrArg Vertex.q
    (rxOriginalBoundaryQOwnerBoundaryQ P A4 S x copy q member)
theorem rxOriginalBoundaryQLocalFaceAtRadialQ
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (face : XStarFace P x) (corner : Two)
    (hq : P.faceQ face.1 corner = q) :
    localFaceQAt P S
        (rxOriginalBoundaryQLocalFaceAt P S x copy face corner) corner =
      Sum.inl ⟨x, Sum.inl (copy, Sum.inl
        (rxOriginalXBoundaryRadialEdge P x q member,
          rxStarEdgeInteriorLastIndex S))⟩ := by
  have hlast : S.half - 1 + 1 = S.half := by
    have := S.half_pos
    omega
  fin_cases corner
  · simp [rxOriginalBoundaryQLocalFaceAt, rxTwoElim_zero, rxTwoElim_one, localFaceQAt,
      localFaceQ0, localFaceQ0Edge, localFaceQ0EdgeAt,
      subdivisionFaceBoundaryEdge_zero_zero,
      subdivisionHorizontalEdge, rxStarEdgeInteriorLastIndex,
      rxRadialGridZero, hlast, rxOriginalXBoundaryRadialEdge] at hq ⊢
    split <;> rename_i hzero
    · apply congrArg (fun edge : XStarEdge P x =>
        (Sum.inl (edge, rxStarEdgeInteriorLastIndex S) :
          SubdivisionEdge P x S))
      apply Subtype.ext
      apply congrArg Sum.inl
      apply Subtype.ext
      have hx : P.faceX face.1 = x := by
        simpa [xStarFaceMember] using face.2
      exact Prod.ext hx hq
    · exfalso
      apply hzero
      apply Fin.ext
      rfl
  · simp [rxOriginalBoundaryQLocalFaceAt, rxTwoElim_zero, rxTwoElim_one, localFaceQAt,
      localFaceQ1, localFaceQ1Edge, localFaceQ1EdgeAt,
      subdivisionFaceBoundaryEdge_one_zero,
      subdivisionVerticalEdge, rxStarEdgeInteriorLastIndex,
      rxRadialGridZero, hlast, rxOriginalXBoundaryRadialEdge] at hq ⊢
    split <;> rename_i hzero
    · apply congrArg (fun edge : XStarEdge P x =>
        (Sum.inl (edge, rxStarEdgeInteriorLastIndex S) :
          SubdivisionEdge P x S))
      apply Subtype.ext
      apply congrArg Sum.inl
      apply Subtype.ext
      have hx : P.faceX face.1 = x := by
        simpa [xStarFaceMember] using face.2
      exact Prod.ext hx hq
    · exfalso
      apply hzero
      apply Fin.ext
      rfl
noncomputable def rxOriginalBoundaryQLocalXStarFaceAt
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (face : XStarFace P x) (corner : Two)
    (hq : P.faceQ face.1 corner = q) :
    XStarFace (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q member) :=
  ⟨Sum.inl (rxOriginalBoundaryQLocalFaceAt P S x copy face corner), by
    simp only [xStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    exact rxOriginalBoundaryQLocalFaceAt_x
      P S x copy q member face corner hq⟩
noncomputable def rxOriginalBoundaryQRootBoundaryPathToQ
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (corner : Two) :=
  xStarFaceBoundaryPathToQ (rxReplacementPresentation P S)
    (rxOriginalBoundaryQXCoordinate P S x copy q member)
    (rxOriginalBoundaryQRootXStarFace P A4 S x copy q member) corner
noncomputable def rxOriginalBoundaryQRootBoundaryPathToZ
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :=
  (rxOriginalBoundaryQRootBoundaryPathToQ
    P A4 S x copy q member 0).append
    (xStarFaceBoundaryPathToZ _ _
      (rxOriginalBoundaryQRootXStarFace P A4 S x copy q member))
theorem rxOriginalBoundaryQOwnerRadialQ
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    localFaceQAt P S
        (rxOriginalBoundaryQOwnerLocalFace P A4 S x copy q member)
        (rxOriginalBoundaryQRootCorner P A4 x q member) =
      Sum.inl ⟨x, Sum.inl (copy, Sum.inl
        (rxOriginalXBoundaryRadialEdge P x q member,
          rxStarEdgeInteriorLastIndex S))⟩ :=
  rxOriginalBoundaryQLocalFaceAtRadialQ P S x copy q member
    (rxOriginalBoundaryQRootFace P A4 x q member)
    (rxOriginalBoundaryQRootCorner P A4 x q member)
    (rxOriginalBoundaryQRootFace_q P A4 x q member)
noncomputable def rxOriginalBoundaryQLocalBoundaryPathToQAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (face : XStarFace P x) (faceCorner : Two)
    (hq : P.faceQ face.1 faceCorner = q) (qCorner : Two) := by
  let ownerBoundaryCorner :=
    flipEndpoint (rxOriginalBoundaryQRootCorner P A4 x q member)
  let toOwnerQ0 :=
    (xStarFaceBoundaryPathToQ (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q member)
      (rxOriginalBoundaryQOwnerXStarFace P A4 S x copy q member)
      ownerBoundaryCorner).reverse
  let toOwnerRadial := xStarFaceBoundaryPathToQ
    (rxReplacementPresentation P S)
    (rxOriginalBoundaryQXCoordinate P S x copy q member)
    (rxOriginalBoundaryQOwnerXStarFace P A4 S x copy q member)
    (rxOriginalBoundaryQRootCorner P A4 x q member)
  let fromCandidateRadial :=
    (xStarFaceBoundaryPathToQ (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q member)
      (rxOriginalBoundaryQLocalXStarFaceAt
        P S x copy q member face faceCorner hq) faceCorner).reverse
  let toTarget := xStarFaceBoundaryPathToQ
    (rxReplacementPresentation P S)
    (rxOriginalBoundaryQXCoordinate P S x copy q member)
    (rxOriginalBoundaryQLocalXStarFaceAt
      P S x copy q member face faceCorner hq) qCorner
  let first :=
    ((rxOriginalBoundaryQOwnerBoundaryVertexEq
      P A4 S x copy q member).symm ▸ toOwnerQ0).append toOwnerRadial
  have hradial : localFaceQAt P S
        (rxOriginalBoundaryQOwnerLocalFace P A4 S x copy q member)
        (rxOriginalBoundaryQRootCorner P A4 x q member) =
      localFaceQAt P S
        (rxOriginalBoundaryQLocalFaceAt P S x copy face faceCorner)
        faceCorner :=
    (rxOriginalBoundaryQOwnerRadialQ P A4 S x copy q member).trans
      (rxOriginalBoundaryQLocalFaceAtRadialQ
        P S x copy q member face faceCorner hq).symm
  have hradialBoundary :
      xBoundaryEdgeStart (rxReplacementPresentation P S)
          (rxOriginalBoundaryQXCoordinate P S x copy q member)
          (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
            (rxOriginalBoundaryQXCoordinate P S x copy q member)
            (rxOriginalBoundaryQOwnerXStarFace P A4 S x copy q member)
            (rxOriginalBoundaryQRootCorner P A4 x q member)) =
        xBoundaryEdgeStart (rxReplacementPresentation P S)
          (rxOriginalBoundaryQXCoordinate P S x copy q member)
          (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
            (rxOriginalBoundaryQXCoordinate P S x copy q member)
            (rxOriginalBoundaryQLocalXStarFaceAt
              P S x copy q member face faceCorner hq) faceCorner) := by
    apply Subtype.ext
    exact congrArg Vertex.q hradial
  exact first.append
    ((hradialBoundary.symm ▸ fromCandidateRadial).append toTarget)
noncomputable def rxOriginalBoundaryQLocalBoundaryPathToZAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (face : XStarFace P x) (faceCorner : Two)
    (hq : P.faceQ face.1 faceCorner = q) :=
  (rxOriginalBoundaryQLocalBoundaryPathToQAt
    P A4 S x copy q member face faceCorner hq 0).append
    (xStarFaceBoundaryPathToZ _ _
      (rxOriginalBoundaryQLocalXStarFaceAt
        P S x copy q member face faceCorner hq))
def rxOriginalBoundaryQRectangleLocalFaceAt
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true) :
    RXLocalFace P S :=
  ⟨x, Sum.inr (subdivisionOriginalBoundaryEdge P x S
    (rxStarEdgeInteriorBoundaryEdge P x edge edgeMember)
    (rxRadialGridZero S)), (copy, 0)⟩
theorem rxOriginalBoundaryQRectangleLocalFaceAt_x
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (edge : QZEdge P) (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (hq : edge.1.1 = q) :
    localFaceX P S (rxOriginalBoundaryQRectangleLocalFaceAt
        P S x copy edge edgeMember) =
      rxOriginalBoundaryQXCoordinate P S x copy q member := by
  simp [rxOriginalBoundaryQRectangleLocalFaceAt,
    rxStarEdgeInteriorBoundaryEdge, subdivisionOriginalBoundaryEdge,
    localFaceX, doubleCylinderRectangleCorner,
    subdivisionBoundaryEdgeStart, subdivisionEdgeStart,
    subdivisionSegmentStart, rxRadialGridZero]
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Prod.ext
    · rfl
    · apply congrArg Sum.inl
      apply Subtype.ext
      exact congrArg Vertex.q hq
def rxOriginalBoundaryQRectangleXStarFaceAt
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (edge : QZEdge P) (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (hq : edge.1.1 = q) :
    XStarFace (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q member) :=
  ⟨Sum.inl (rxOriginalBoundaryQRectangleLocalFaceAt
      P S x copy edge edgeMember), by
    simp only [xStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    exact rxOriginalBoundaryQRectangleLocalFaceAt_x
      P S x copy q member edge edgeMember hq⟩
theorem rxOriginalBoundaryQRectangleVerticalQ
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (edge : QZEdge P) (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (hq : edge.1.1 = q) :
    localFaceQAt P S (rxOriginalBoundaryQRectangleLocalFaceAt
        P S x copy edge edgeMember) 1 =
      Sum.inl ⟨x, Sum.inr
        (subdivisionOriginalBoundaryVertex P x S ⟨Vertex.q q, member⟩)⟩ := by
  simp [rxOriginalBoundaryQRectangleLocalFaceAt,
    localFaceQAt, localFaceQ1, localFaceQ1Edge, localFaceQ1EdgeAt,
    rxStarEdgeInteriorBoundaryEdge, subdivisionOriginalBoundaryEdge,
    subdivisionBoundaryEdgeStart, subdivisionEdgeStart,
    subdivisionSegmentStart, rxRadialGridZero]
  congr 4
  apply Subtype.ext
  exact congrArg Vertex.q hq
theorem rxOriginalBoundaryQRectangleVerticalBoundaryEq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (edge : QZEdge P) (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (hq : edge.1.1 = q) :
    xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q member)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxOriginalBoundaryQXCoordinate P S x copy q member)
          (rxOriginalBoundaryQRootXStarFace P A4 S x copy q member) 1) =
      xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q member)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxOriginalBoundaryQXCoordinate P S x copy q member)
          (rxOriginalBoundaryQRectangleXStarFaceAt
            P S x copy q member edge edgeMember hq) 1) := by
  apply Subtype.ext
  exact congrArg Vertex.q
    ((rxOriginalBoundaryQRootRectangleQ1 P A4 S x copy q member).trans
      (rxOriginalBoundaryQRectangleVerticalQ
        P S x copy q member edge edgeMember hq).symm)
noncomputable def rxOriginalBoundaryQRectangleBoundaryPathToQAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (edge : QZEdge P) (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (hq : edge.1.1 = q) (corner : Two) := by
  let first := rxOriginalBoundaryQRootBoundaryPathToQ
    P A4 S x copy q member 1
  let bridge := (xStarFaceBoundaryPathToQ (rxReplacementPresentation P S)
    (rxOriginalBoundaryQXCoordinate P S x copy q member)
    (rxOriginalBoundaryQRectangleXStarFaceAt
      P S x copy q member edge edgeMember hq) 1).reverse
  let last := xStarFaceBoundaryPathToQ (rxReplacementPresentation P S)
    (rxOriginalBoundaryQXCoordinate P S x copy q member)
    (rxOriginalBoundaryQRectangleXStarFaceAt
      P S x copy q member edge edgeMember hq) corner
  exact first.append
    (((rxOriginalBoundaryQRectangleVerticalBoundaryEq
      P A4 S x copy q member edge edgeMember hq).symm ▸ bridge).append last)
noncomputable def rxOriginalBoundaryQRectangleBoundaryPathToZAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (edge : QZEdge P) (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (hq : edge.1.1 = q) :=
  (rxOriginalBoundaryQRectangleBoundaryPathToQAt
    P A4 S x copy q member edge edgeMember hq 0).append
    (xStarFaceBoundaryPathToZ _ _
      (rxOriginalBoundaryQRectangleXStarFaceAt
        P S x copy q member edge edgeMember hq))
theorem rxOriginalBoundaryQSmallFace_cases
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (candidate : RXLocalFace P S)
    (hx : localFaceX P S candidate =
      rxOriginalBoundaryQXCoordinate P S x copy q member)
    (hsmall : ∃ copyFace : Two × SubdivisionFace P candidate.1 S,
      candidate.2.1 = Sum.inl copyFace) :
    ∃ face : XStarFace P x, ∃ corner : Two,
      P.faceQ face.1 corner = q ∧
        candidate = rxOriginalBoundaryQLocalFaceAt
          P S x copy face corner := by
  rcases candidate with ⟨oldX, localCell, material⟩
  rcases localCell with copyFace | rectangle
  · rcases copyFace with ⟨candidateCopy, small⟩
    rcases small with ⟨candidateFace, column, row⟩
    rcases material with ⟨first, second⟩
    have howner : oldX = x := congrArg Sigma.fst hx
    subst oldX
    have hvertex :
        (candidateCopy, subdivisionGridVertex P x S candidateFace
          (gridEndpoint column first) (gridEndpoint row second)) =
        (copy, Sum.inl ⟨Vertex.q q, by
          simpa [xStarBoundaryVertexMember, xStarVertexMember] using member⟩) :=
      eq_of_heq (Sigma.mk.inj_iff.mp hx).2
    have hcopy : candidateCopy = copy := congrArg Prod.fst hvertex
    subst candidateCopy
    have hgrid := congrArg Prod.snd hvertex
    rcases subdivisionGridVertex_eq_originalQ_coordinates
        P S x candidateFace (gridEndpoint column first)
          (gridEndpoint row second) q _ hgrid with hq0 | hq1
    · fin_cases first
      · have := hq0.1
        simp [gridEndpoint, lowerGridIndex] at this
        have := column.2
        omega
      · fin_cases second
        · refine ⟨candidateFace, 0, hq0.2.2, ?_⟩
          have hcolumn : column = rxStarEdgeInteriorLastIndex S := by
            apply Fin.ext
            change column.1 = S.half - 1
            have := hq0.1
            simp [gridEndpoint, upperGridIndex] at this
            omega
          have hrow : row = rxRadialGridZero S := by
            apply Fin.ext
            simpa [gridEndpoint, lowerGridIndex,
              rxRadialGridZero] using hq0.2.1
          rw [hcolumn, hrow]
          rfl
        · have := hq0.2.1
          simp [gridEndpoint, upperGridIndex] at this
    · fin_cases first
      · fin_cases second
        · have := hq1.2.1
          simp [gridEndpoint, lowerGridIndex] at this
          have := row.2
          omega
        · refine ⟨candidateFace, 1, hq1.2.2, ?_⟩
          have hcolumn : column = rxRadialGridZero S := by
            apply Fin.ext
            simpa [gridEndpoint, lowerGridIndex,
              rxRadialGridZero] using hq1.1
          have hrow : row = rxStarEdgeInteriorLastIndex S := by
            apply Fin.ext
            change row.1 = S.half - 1
            have := hq1.2.1
            simp [gridEndpoint, upperGridIndex] at this
            omega
          rw [hcolumn, hrow]
          rfl
      · have := hq1.1
        simp [gridEndpoint, upperGridIndex] at this
  · rcases hsmall with ⟨copyFace, hcopyFace⟩
    cases hcopyFace
theorem rxOriginalBoundaryQRectangleFace_cases
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (candidate : RXLocalFace P S)
    (hx : localFaceX P S candidate =
      rxOriginalBoundaryQXCoordinate P S x copy q member)
    (hrectangle : ∃ rectangle : SubdivisionBoundaryEdge P candidate.1 S,
      candidate.2.1 = Sum.inr rectangle) :
    ∃ edge : QZEdge P,
      ∃ edgeMember : xStarEdgeMember P x (Sum.inr edge) = true,
        edge.1.1 = q ∧
          candidate = rxOriginalBoundaryQRectangleLocalFaceAt
            P S x copy edge edgeMember := by
  rcases candidate with ⟨oldX, localCell, material⟩
  rcases localCell with copyFace | rectangle
  · rcases hrectangle with ⟨rectangle, hrectangle⟩
    cases hrectangle
  · rcases material with ⟨materialCopy, endpoint⟩
    have howner : oldX = x := congrArg Sigma.fst hx
    subst oldX
    have hvertex : doubleCylinderRectangleCorner P x S rectangle
        (materialCopy, endpoint) =
        (copy, Sum.inl ⟨Vertex.q q, by
          simpa [xStarBoundaryVertexMember, xStarVertexMember] using member⟩) :=
      eq_of_heq (Sigma.mk.inj_iff.mp hx).2
    have hcopy : materialCopy = copy := congrArg Prod.fst hvertex
    subst materialCopy
    rcases rectangle with ⟨raw, boundaryMember⟩
    rcases raw with original | interior
    · rcases original with ⟨starEdge, segment⟩
      fin_cases endpoint
      · have hsubdivision := congrArg Prod.snd hvertex
        by_cases hzero : segment.1 = 0
        · have hstart : xStarEdgeStart P x starEdge =
              ⟨Vertex.q q, by
                simpa [xStarBoundaryVertexMember, xStarVertexMember]
                  using member⟩ := by
            have hinl :
                (Sum.inl (xStarEdgeStart P x starEdge) :
                    SubdivisionVertex P x S) =
                  Sum.inl ⟨Vertex.q q, by
                    simpa [xStarBoundaryVertexMember, xStarVertexMember]
                      using member⟩ := by
              simpa [doubleCylinderRectangleCorner,
                subdivisionBoundaryEdgeStart, subdivisionEdgeStart,
                subdivisionSegmentStart, hzero] using hsubdivision
            exact Sum.inl.inj hinl
          have hsegment : segment = rxRadialGridZero S := by
            apply Fin.ext
            simpa [rxRadialGridZero] using hzero
          rcases starEdge with ⟨rawEdge, starMember⟩
          rcases rawEdge with radial | boundary
          · simp [subdivisionBoundaryEdgeMember,
              xStarBoundaryEdgeMember] at boundaryMember
          · have hq : boundary.1.1 = q := by
              have hraw := congrArg Subtype.val hstart
              exact Vertex.q.inj hraw
            have edgeMember :
                xStarEdgeMember P x (Sum.inr boundary) = true := starMember
            refine ⟨boundary, edgeMember, hq, ?_⟩
            rw [hsegment]
            rfl
        · have himpossible :
              (Sum.inr (Sum.inl
                (starEdge, ⟨segment.1 - 1, by
                  have := segment.2
                  omega⟩)) : SubdivisionVertex P x S) =
                Sum.inl ⟨Vertex.q q, by
                  simpa [xStarBoundaryVertexMember, xStarVertexMember]
                    using member⟩ := by
            simpa [doubleCylinderRectangleCorner,
              subdivisionBoundaryEdgeStart, subdivisionEdgeStart,
              subdivisionSegmentStart, hzero] using hsubdivision
          cases himpossible
      · have hsubdivision := congrArg Prod.snd hvertex
        by_cases hlast : segment.1 + 1 = S.half
        · have hend : xStarEdgeEnd P x starEdge =
              ⟨Vertex.q q, by
                simpa [xStarBoundaryVertexMember, xStarVertexMember]
                  using member⟩ := by
            have hinl :
                (Sum.inl (xStarEdgeEnd P x starEdge) :
                    SubdivisionVertex P x S) =
                  Sum.inl ⟨Vertex.q q, by
                    simpa [xStarBoundaryVertexMember, xStarVertexMember]
                      using member⟩ := by
              simpa [doubleCylinderRectangleCorner,
                subdivisionBoundaryEdgeEnd, subdivisionEdgeEnd,
                subdivisionSegmentEnd, hlast] using hsubdivision
            exact Sum.inl.inj hinl
          rcases starEdge with ⟨rawEdge, starMember⟩
          rcases rawEdge with radial | boundary
          · simp [subdivisionBoundaryEdgeMember,
              xStarBoundaryEdgeMember] at boundaryMember
          · have hraw := congrArg Subtype.val hend
            change Vertex.z boundary.1.2 = Vertex.q q at hraw
            cases hraw
        · have himpossible :
              (Sum.inr (Sum.inl
                (starEdge, ⟨segment.1, by
                  have := segment.2
                  omega⟩)) : SubdivisionVertex P x S) =
                Sum.inl ⟨Vertex.q q, by
                  simpa [xStarBoundaryVertexMember, xStarVertexMember]
                    using member⟩ := by
            simpa [doubleCylinderRectangleCorner,
              subdivisionBoundaryEdgeEnd, subdivisionEdgeEnd,
              subdivisionSegmentEnd, hlast] using hsubdivision
          cases himpossible
    · simp [subdivisionBoundaryEdgeMember] at boundaryMember
inductive RXOriginalBoundaryQConstructorTarget
    (P : TannerSquarePresentation) (x : P.X) (q : P.Q)
  | smallQ (face : XStarFace P x) (faceCorner : Two)
      (hq : P.faceQ face.1 faceCorner = q) (corner : Two)
  | smallZ (face : XStarFace P x) (faceCorner : Two)
      (hq : P.faceQ face.1 faceCorner = q)
  | rectangleQ (edge : QZEdge P)
      (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
      (hq : edge.1.1 = q) (corner : Two)
  | rectangleZ (edge : QZEdge P)
      (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
      (hq : edge.1.1 = q)
noncomputable def rxOriginalBoundaryQConstructorBoundaryVertex
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    RXOriginalBoundaryQConstructorTarget P x q →
      XStarBoundaryVertex (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q member)
  | .smallQ face faceCorner hq corner =>
      xBoundaryEdgeStart (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxOriginalBoundaryQLocalXStarFaceAt
            P S x copy q member face faceCorner hq) corner)
  | .smallZ face faceCorner hq =>
      xBoundaryEdgeEnd (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxOriginalBoundaryQLocalXStarFaceAt
            P S x copy q member face faceCorner hq) 0)
  | .rectangleQ edge edgeMember hq corner =>
      xBoundaryEdgeStart (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxOriginalBoundaryQRectangleXStarFaceAt
            P S x copy q member edge edgeMember hq) corner)
  | .rectangleZ edge edgeMember hq =>
      xBoundaryEdgeEnd (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxOriginalBoundaryQRectangleXStarFaceAt
            P S x copy q member edge edgeMember hq) 0)
noncomputable def rxOriginalBoundaryQConstructorBoundaryPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (target : RXOriginalBoundaryQConstructorTarget P x q) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q member))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q member))
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q member)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxOriginalBoundaryQXCoordinate P S x copy q member)
          (rxOriginalBoundaryQRootXStarFace P A4 S x copy q member) 0))
      (rxOriginalBoundaryQConstructorBoundaryVertex
        P A4 S x copy q member target) := by
  rcases target with
    ⟨face, faceCorner, hq, corner⟩ |
    ⟨face, faceCorner, hq⟩ |
    ⟨edge, edgeMember, hq, corner⟩ |
    ⟨edge, edgeMember, hq⟩
  · exact rxOriginalBoundaryQLocalBoundaryPathToQAt
      P A4 S x copy q member face faceCorner hq corner
  · exact rxOriginalBoundaryQLocalBoundaryPathToZAt
      P A4 S x copy q member face faceCorner hq
  · exact rxOriginalBoundaryQRectangleBoundaryPathToQAt
      P A4 S x copy q member edge edgeMember hq corner
  · exact rxOriginalBoundaryQRectangleBoundaryPathToZAt
      P A4 S x copy q member edge edgeMember hq
def rxOriginalBoundaryQGlueFaceAt
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (edge : QStarEdge P q) : RXXQGlueFace P S :=
  ⟨⟨(x, q), rxOriginalXBoundaryQ_incidence P x q member⟩,
    Sum.inl (copy, (edge, rxRadialGridZero S)), 0⟩
theorem rxOriginalBoundaryQGlueFaceAt_x
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (edge : QStarEdge P q) :
    glueFaceX P S (rxOriginalBoundaryQGlueFaceAt
        P S x copy q member edge) =
      rxOriginalBoundaryQXCoordinate P S x copy q member := by
  simp [rxOriginalBoundaryQGlueFaceAt, glueFaceX, edgeEndpoint,
    qToXDoubleCylinderEdgeRaw, tannerDoubleCylinderEdgeStart,
    qToXSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge,
    subdivisionEdgeStart,
    subdivisionSegmentStart, qStarEdgeStart, rxRadialGridZero,
    qToXBoundaryVertexAtRoot, qToXBoundaryEdge,
    rxOriginalBoundaryQXCoordinate]
  rw [← xBoundaryEdgeStart_toStar]
  rfl
def rxOriginalBoundaryQGlueXStarFaceAt
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (edge : QStarEdge P q) :
    XStarFace (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q member) :=
  ⟨Sum.inr (Sum.inl
      (rxOriginalBoundaryQGlueFaceAt P S x copy q member edge)), by
    simp only [xStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    exact rxOriginalBoundaryQGlueFaceAt_x P S x copy q member edge⟩
def rxOriginalBoundaryQGlueQZEdge
    (P : TannerSquarePresentation) (q : P.Q) (edge : QStarEdge P q) :
    QZEdge P :=
  ⟨(q, edge.1), edge.2⟩
theorem rxOriginalBoundaryQGlueQZEdge_member
    (P : TannerSquarePresentation) (x : P.X) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (edge : QStarEdge P q) :
    xStarEdgeMember P x
        (Sum.inr (rxOriginalBoundaryQGlueQZEdge P q edge)) = true := by
  exact (xStarBoundaryEdgeToStar P x
    (qToXBoundaryEdge P q x
      (rxOriginalXBoundaryQ_incidence P x q member) edge)).2
theorem rxOriginalBoundaryQGlueQ0
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (edge : QStarEdge P q) :
    glueFaceQ0 P S
        (rxOriginalBoundaryQGlueFaceAt P S x copy q member edge) =
      localFaceQAt P S
        (rxOriginalBoundaryQRectangleLocalFaceAt P S x copy
          (rxOriginalBoundaryQGlueQZEdge P q edge)
          (rxOriginalBoundaryQGlueQZEdge_member P x q member edge)) 0 := by
  simp [rxOriginalBoundaryQGlueFaceAt, glueFaceQ0,
    rxOriginalBoundaryQGlueQZEdge,
    rxOriginalBoundaryQRectangleLocalFaceAt, localFaceQAt,
    localFaceQ0, localFaceQ0Edge, localFaceQ0EdgeAt,
    subdivisionOriginalBoundaryEdge,
    subdivisionFaceBoundaryEdge_zero_zero,
    doubleCylinderRectangleBoundaryEdge, qToXDoubleCylinderEdgeRaw,
    qToXSubdivisionBoundaryEdge, rxStarEdgeInteriorBoundaryEdge,
    subdivisionHorizontalEdge, rxRadialGridZero]
  apply Subtype.ext
  rfl
theorem rxOriginalBoundaryQGlueBoundaryQEq
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (edge : QStarEdge P q) :
    xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q member)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxOriginalBoundaryQXCoordinate P S x copy q member)
          (rxOriginalBoundaryQRectangleXStarFaceAt P S x copy q member
            (rxOriginalBoundaryQGlueQZEdge P q edge)
            (rxOriginalBoundaryQGlueQZEdge_member P x q member edge) rfl) 0) =
      xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q member)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxOriginalBoundaryQXCoordinate P S x copy q member)
          (rxOriginalBoundaryQGlueXStarFaceAt
            P S x copy q member edge) 0) := by
  apply Subtype.ext
  apply congrArg Vertex.q
  change localFaceQAt P S
      (rxOriginalBoundaryQRectangleLocalFaceAt P S x copy
        (rxOriginalBoundaryQGlueQZEdge P q edge)
        (rxOriginalBoundaryQGlueQZEdge_member P x q member edge)) 0 =
    glueFaceQ0 P S
      (rxOriginalBoundaryQGlueFaceAt P S x copy q member edge)
  exact (rxOriginalBoundaryQGlueQ0
    P S x copy q member edge).symm
noncomputable def rxOriginalBoundaryQGlueBoundaryPathToQAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (edge : QStarEdge P q) (corner : Two) := by
  let first := rxOriginalBoundaryQRectangleBoundaryPathToQAt
    P A4 S x copy q member
      (rxOriginalBoundaryQGlueQZEdge P q edge)
      (rxOriginalBoundaryQGlueQZEdge_member P x q member edge) rfl 0
  let last := xStarFaceBoundaryPathToQ (rxReplacementPresentation P S)
    (rxOriginalBoundaryQXCoordinate P S x copy q member)
    (rxOriginalBoundaryQGlueXStarFaceAt
      P S x copy q member edge) corner
  exact first.append ((rxOriginalBoundaryQGlueBoundaryQEq
    P S x copy q member edge).symm ▸ last)
noncomputable def rxOriginalBoundaryQGlueBoundaryPathToZAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (edge : QStarEdge P q) :=
  (rxOriginalBoundaryQGlueBoundaryPathToQAt
    P A4 S x copy q member edge 0).append
    (xStarFaceBoundaryPathToZ _ _
      (rxOriginalBoundaryQGlueXStarFaceAt
        P S x copy q member edge))
inductive RXOriginalBoundaryQGlueTarget
    (P : TannerSquarePresentation) (q : P.Q)
  | q (edge : QStarEdge P q) (corner : Two)
  | z (edge : QStarEdge P q)
noncomputable def rxOriginalBoundaryQGlueBoundaryVertex
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    RXOriginalBoundaryQGlueTarget P q →
      XStarBoundaryVertex (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q member)
  | .q edge corner =>
      xBoundaryEdgeStart (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxOriginalBoundaryQGlueXStarFaceAt
            P S x copy q member edge) corner)
  | .z edge =>
      xBoundaryEdgeEnd (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxOriginalBoundaryQGlueXStarFaceAt
            P S x copy q member edge) 0)
noncomputable def rxOriginalBoundaryQGlueBoundaryPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (target : RXOriginalBoundaryQGlueTarget P q) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q member))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q member))
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q member)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxOriginalBoundaryQXCoordinate P S x copy q member)
          (rxOriginalBoundaryQRootXStarFace P A4 S x copy q member) 0))
      (rxOriginalBoundaryQGlueBoundaryVertex
        P A4 S x copy q member target) := by
  rcases target with ⟨edge, corner⟩ | ⟨edge⟩
  · exact rxOriginalBoundaryQGlueBoundaryPathToQAt
      P A4 S x copy q member edge corner
  · exact rxOriginalBoundaryQGlueBoundaryPathToZAt
      P A4 S x copy q member edge
theorem rxOriginalBoundaryQGlueFace_cases
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (candidate : RXXQGlueFace P S)
    (hx : glueFaceX P S candidate =
      rxOriginalBoundaryQXCoordinate P S x copy q member) :
    ∃ edge : QStarEdge P q,
      candidate = rxOriginalBoundaryQGlueFaceAt
        P S x copy q member edge := by
  rcases candidate with ⟨⟨⟨oldX, candidateQ⟩, hxq⟩, qEdge, endpoint⟩
  have howner : oldX = x := congrArg Sigma.fst hx
  subst oldX
  have hvertex : edgeEndpoint
        (tannerDoubleCylinderEdgeStart P x S)
        (tannerDoubleCylinderEdgeEnd P x S)
        (qToXDoubleCylinderEdgeRaw P candidateQ x hxq S qEdge) endpoint =
      (copy, Sum.inl ⟨Vertex.q q, by
        simpa [xStarBoundaryVertexMember, xStarVertexMember] using member⟩) :=
    eq_of_heq (Sigma.mk.inj_iff.mp hx).2
  rcases qEdge with copyEdge | vertical
  · rcases copyEdge with ⟨edgeCopy, qSegment⟩
    rcases qSegment with ⟨qStarEdge, segment⟩
    fin_cases endpoint
    · have hcopy : edgeCopy = copy := by
        simpa [edgeEndpoint, qToXDoubleCylinderEdgeRaw,
          tannerDoubleCylinderEdgeStart] using congrArg Prod.fst hvertex
      subst edgeCopy
      have hsubdivision := congrArg Prod.snd hvertex
      by_cases hzero : segment.1 = 0
      · have hstart :
            xStarEdgeStart P x
                (xStarBoundaryEdgeToStar P x
                  (qToXBoundaryEdge P candidateQ x hxq qStarEdge)) =
              xStarBoundaryVertexToStar P x
                ⟨Vertex.q q, member⟩ := by
          simpa [edgeEndpoint, qToXDoubleCylinderEdgeRaw,
            qToXSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge,
            tannerDoubleCylinderEdgeStart, subdivisionEdgeStart,
            subdivisionSegmentStart, hzero,
            subdivisionOriginalBoundaryVertex, xStarBoundaryVertexToStar] using hsubdivision
        rw [← xBoundaryEdgeStart_toStar] at hstart
        have hraw := congrArg Subtype.val hstart
        have hcandidateQ : candidateQ = q := Vertex.q.inj hraw
        subst candidateQ
        have hsegment : segment = rxRadialGridZero S := by
          apply Fin.ext
          simpa [rxRadialGridZero] using hzero
        refine ⟨qStarEdge, ?_⟩
        apply Sigma.ext
        · apply Subtype.ext
          rfl
        · apply heq_of_eq
          rw [hsegment]
          rfl
      · have himpossible :
            (Sum.inr (Sum.inl
              (xStarBoundaryEdgeToStar P x
                (qToXBoundaryEdge P candidateQ x hxq qStarEdge),
                ⟨segment.1 - 1, by have := segment.2; omega⟩)) :
              SubdivisionVertex P x S) =
            Sum.inl ⟨Vertex.q q, by
              simpa [xStarBoundaryVertexMember, xStarVertexMember] using member⟩ := by
          simpa [edgeEndpoint, qToXDoubleCylinderEdgeRaw,
            qToXSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge,
            tannerDoubleCylinderEdgeStart, subdivisionEdgeStart,
            subdivisionSegmentStart, hzero] using hsubdivision
        cases himpossible
    · have hsubdivision := congrArg Prod.snd hvertex
      by_cases hlast : segment.1 + 1 = S.half
      · have himpossible :
            (Sum.inl (xStarEdgeEnd P x
              (xStarBoundaryEdgeToStar P x
                (qToXBoundaryEdge P candidateQ x hxq qStarEdge))) :
              SubdivisionVertex P x S) =
            Sum.inl ⟨Vertex.q q, by
              simpa [xStarBoundaryVertexMember, xStarVertexMember] using member⟩ := by
          simpa [edgeEndpoint, qToXDoubleCylinderEdgeRaw,
            qToXSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge,
            tannerDoubleCylinderEdgeEnd, subdivisionEdgeEnd,
            subdivisionSegmentEnd, hlast] using hsubdivision
        have hraw := congrArg Subtype.val (Sum.inl.inj himpossible)
        change Vertex.z qStarEdge.1 = Vertex.q q at hraw
        cases hraw
      · have himpossible :
            (Sum.inr (Sum.inl
              (xStarBoundaryEdgeToStar P x
                (qToXBoundaryEdge P candidateQ x hxq qStarEdge),
                ⟨segment.1, by have := segment.2; omega⟩)) :
              SubdivisionVertex P x S) =
            Sum.inl ⟨Vertex.q q, by
              simpa [xStarBoundaryVertexMember, xStarVertexMember] using member⟩ := by
          simpa [edgeEndpoint, qToXDoubleCylinderEdgeRaw,
            qToXSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge,
            tannerDoubleCylinderEdgeEnd, subdivisionEdgeEnd,
            subdivisionSegmentEnd, hlast] using hsubdivision
        cases himpossible
  · have hsubdivision := congrArg Prod.snd hvertex
    fin_cases endpoint <;>
      simp [edgeEndpoint, qToXDoubleCylinderEdgeRaw,
        tannerDoubleCylinderEdgeStart, tannerDoubleCylinderEdgeEnd,
        subdivisionOriginalBoundaryVertex] at hsubdivision
    all_goals
      have hraw := congrArg Subtype.val hsubdivision
      change Vertex.z vertical.1 = Vertex.q q at hraw
      cases hraw
inductive RXOriginalBoundaryQTarget
    (P : TannerSquarePresentation) (x : P.X) (q : P.Q)
  | constructor (target : RXOriginalBoundaryQConstructorTarget P x q)
  | glue (target : RXOriginalBoundaryQGlueTarget P q)
noncomputable def rxOriginalBoundaryQTargetBoundaryVertex
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    RXOriginalBoundaryQTarget P x q →
      XStarBoundaryVertex (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q member)
  | .constructor target =>
      rxOriginalBoundaryQConstructorBoundaryVertex
        P A4 S x copy q member target
  | .glue target =>
      rxOriginalBoundaryQGlueBoundaryVertex
        P A4 S x copy q member target
noncomputable def rxOriginalBoundaryQTargetBoundaryPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (target : RXOriginalBoundaryQTarget P x q) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q member))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q member))
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q member)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxOriginalBoundaryQXCoordinate P S x copy q member)
          (rxOriginalBoundaryQRootXStarFace P A4 S x copy q member) 0))
      (rxOriginalBoundaryQTargetBoundaryVertex
        P A4 S x copy q member target) := by
  rcases target with ⟨target⟩ | ⟨target⟩
  · exact rxOriginalBoundaryQConstructorBoundaryPath
      P A4 S x copy q member target
  · exact rxOriginalBoundaryQGlueBoundaryPath
      P A4 S x copy q member target
noncomputable def rxOriginalBoundaryQIncidentXStarFace
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (candidate : RXFace P S)
    (hx : rxFaceX P S candidate =
      rxOriginalBoundaryQXCoordinate P S x copy q member) :
    XStarFace (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q member) :=
  ⟨candidate, by
    simp only [xStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    exact hx⟩
def rxInteriorUpperFaceIndex (S : OddScale)
    (i : Fin (S.half - 1)) : Fin S.half :=
  ⟨i.1 + 1, by have := i.2; omega⟩
noncomputable def rxFaceInteriorLocalFaceSW
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (face : XStarFace P x)
    (i j : Fin (S.half - 1)) : RXLocalFace P S :=
  ⟨x, Sum.inl (copy,
    (face, rxInteriorFaceIndex S i, rxInteriorFaceIndex S j)), (1, 1)⟩
noncomputable def rxFaceInteriorLocalFaceSE
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (face : XStarFace P x)
    (i j : Fin (S.half - 1)) : RXLocalFace P S :=
  ⟨x, Sum.inl (copy,
    (face, rxInteriorUpperFaceIndex S i, rxInteriorFaceIndex S j)), (0, 1)⟩
noncomputable def rxFaceInteriorLocalFaceNW
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (face : XStarFace P x)
    (i j : Fin (S.half - 1)) : RXLocalFace P S :=
  ⟨x, Sum.inl (copy,
    (face, rxInteriorFaceIndex S i, rxInteriorUpperFaceIndex S j)), (1, 0)⟩
noncomputable def rxFaceInteriorLocalFaceNE
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (face : XStarFace P x)
    (i j : Fin (S.half - 1)) : RXLocalFace P S :=
  ⟨x, Sum.inl (copy,
    (face, rxInteriorUpperFaceIndex S i,
      rxInteriorUpperFaceIndex S j)), (0, 0)⟩
theorem rxFaceInteriorLocalFaceX_eq
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (face : XStarFace P x)
    (i j : Fin (S.half - 1)) :
    localFaceX P S (rxFaceInteriorLocalFaceSW P S x copy face i j) =
        ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ ∧
      localFaceX P S (rxFaceInteriorLocalFaceSE P S x copy face i j) =
        ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ ∧
      localFaceX P S (rxFaceInteriorLocalFaceNW P S x copy face i j) =
        ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ ∧
      localFaceX P S (rxFaceInteriorLocalFaceNE P S x copy face i j) =
        ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ := by
  have hi : i.1 + 1 < S.half := (Nat.lt_sub_iff_add_lt).1 i.2
  have hj : j.1 + 1 < S.half := (Nat.lt_sub_iff_add_lt).1 j.2
  constructor
  · simp [rxFaceInteriorLocalFaceSW, localFaceX, gridEndpoint,
      rxInteriorFaceIndex, subdivisionGridVertex, lowerGridIndex,
      upperGridIndex, hi.ne, hj.ne]
    constructor
    · apply Fin.ext
      change (i.1 + 1) - 1 = i.1
      omega
    · apply Fin.ext
      change (j.1 + 1) - 1 = j.1
      omega
  constructor
  · simp [rxFaceInteriorLocalFaceSE, localFaceX, gridEndpoint,
      rxInteriorFaceIndex, rxInteriorUpperFaceIndex,
      subdivisionGridVertex, lowerGridIndex, upperGridIndex, hi.ne, hj.ne]
    constructor
    · apply Fin.ext
      change (i.1 + 1) - 1 = i.1
      omega
    · apply Fin.ext
      change (j.1 + 1) - 1 = j.1
      omega
  constructor
  · simp [rxFaceInteriorLocalFaceNW, localFaceX, gridEndpoint,
      rxInteriorFaceIndex, rxInteriorUpperFaceIndex,
      subdivisionGridVertex, lowerGridIndex, upperGridIndex, hi.ne, hj.ne]
    constructor
    · apply Fin.ext
      change (i.1 + 1) - 1 = i.1
      omega
    · apply Fin.ext
      change (j.1 + 1) - 1 = j.1
      omega
  · simp [rxFaceInteriorLocalFaceNE, localFaceX, gridEndpoint,
      rxInteriorUpperFaceIndex, subdivisionGridVertex, lowerGridIndex,
      upperGridIndex, hi.ne, hj.ne]
    constructor
    · apply Fin.ext
      change (i.1 + 1) - 1 = i.1
      omega
    · apply Fin.ext
      change (j.1 + 1) - 1 = j.1
      omega
noncomputable def rxFaceInteriorXStarFaceSW
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (face : XStarFace P x) (i j : Fin (S.half - 1)) :
    XStarFace (rxReplacementPresentation P S)
      ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ :=
  ⟨Sum.inl (rxFaceInteriorLocalFaceSW P S x copy face i j), by
    simp only [xStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    exact (rxFaceInteriorLocalFaceX_eq P S x copy face i j).1⟩
noncomputable def rxFaceInteriorXStarFaceSE
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (face : XStarFace P x) (i j : Fin (S.half - 1)) :
    XStarFace (rxReplacementPresentation P S)
      ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ :=
  ⟨Sum.inl (rxFaceInteriorLocalFaceSE P S x copy face i j), by
    simp only [xStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    exact (rxFaceInteriorLocalFaceX_eq P S x copy face i j).2.1⟩
noncomputable def rxFaceInteriorXStarFaceNW
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (face : XStarFace P x) (i j : Fin (S.half - 1)) :
    XStarFace (rxReplacementPresentation P S)
      ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ :=
  ⟨Sum.inl (rxFaceInteriorLocalFaceNW P S x copy face i j), by
    simp only [xStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    exact (rxFaceInteriorLocalFaceX_eq P S x copy face i j).2.2.1⟩
noncomputable def rxFaceInteriorXStarFaceNE
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (face : XStarFace P x) (i j : Fin (S.half - 1)) :
    XStarFace (rxReplacementPresentation P S)
      ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ :=
  ⟨Sum.inl (rxFaceInteriorLocalFaceNE P S x copy face i j), by
    simp only [xStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    exact (rxFaceInteriorLocalFaceX_eq P S x copy face i j).2.2.2⟩
theorem rxFaceInteriorFace_cases
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (face : XStarFace P x) (i j : Fin (S.half - 1))
    (candidate : RXFace P S)
    (hx : rxFaceX P S candidate =
      ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩) :
    candidate = Sum.inl (rxFaceInteriorLocalFaceSW P S x copy face i j) ∨
      candidate = Sum.inl (rxFaceInteriorLocalFaceSE P S x copy face i j) ∨
      candidate = Sum.inl (rxFaceInteriorLocalFaceNW P S x copy face i j) ∨
      candidate = Sum.inl (rxFaceInteriorLocalFaceNE P S x copy face i j) := by
  classical
  rcases candidate with candidateLocal | glue | old
  · rcases candidateLocal with ⟨oldX, localCell, material⟩
    rcases localCell with copyFace | rectangle
    · rcases copyFace with ⟨candidateCopy, small⟩
      rcases small with ⟨candidateFace, column, row⟩
      rcases material with ⟨first, second⟩
      have howner : oldX = x := congrArg Sigma.fst hx
      subst oldX
      have hvertex :
          (candidateCopy,
            subdivisionGridVertex P x S candidateFace
              (gridEndpoint column first) (gridEndpoint row second)) =
            (copy, Sum.inr (Sum.inr (face, i, j))) :=
        eq_of_heq (Sigma.mk.inj_iff.mp hx).2
      have hcopy : candidateCopy = copy := congrArg Prod.fst hvertex
      subst candidateCopy
      have hgrid : subdivisionGridVertex P x S candidateFace
          (gridEndpoint column first) (gridEndpoint row second) =
          Sum.inr (Sum.inr (face, i, j)) := congrArg Prod.snd hvertex
      have hcoordinates := subdivisionGridVertex_eq_faceInterior_coordinates
        P x S candidateFace face (gridEndpoint column first)
          (gridEndpoint row second) i j hgrid
      have hface : candidateFace = face := hcoordinates.1
      subst candidateFace
      fin_cases first <;> fin_cases second
      · right; right; right
        have hcolumn : column = rxInteriorUpperFaceIndex S i := by
          apply Fin.ext
          simpa [gridEndpoint, lowerGridIndex, rxInteriorUpperFaceIndex] using
            hcoordinates.2.1
        have hrow : row = rxInteriorUpperFaceIndex S j := by
          apply Fin.ext
          simpa [gridEndpoint, lowerGridIndex, rxInteriorUpperFaceIndex] using
            hcoordinates.2.2
        rw [hcolumn, hrow]
        rfl
      · right; left
        have hcolumn : column = rxInteriorUpperFaceIndex S i := by
          apply Fin.ext
          simpa [gridEndpoint, lowerGridIndex, rxInteriorUpperFaceIndex] using
            hcoordinates.2.1
        have hrow : row = rxInteriorFaceIndex S j := by
          apply Fin.ext
          change row.1 = j.1
          have h := hcoordinates.2.2
          simp [gridEndpoint, upperGridIndex] at h
          omega
        rw [hcolumn, hrow]
        rfl
      · right; right; left
        have hcolumn : column = rxInteriorFaceIndex S i := by
          apply Fin.ext
          change column.1 = i.1
          have h := hcoordinates.2.1
          simp [gridEndpoint, upperGridIndex] at h
          omega
        have hrow : row = rxInteriorUpperFaceIndex S j := by
          apply Fin.ext
          simpa [gridEndpoint, lowerGridIndex, rxInteriorUpperFaceIndex] using
            hcoordinates.2.2
        rw [hcolumn, hrow]
        rfl
      · left
        have hcolumn : column = rxInteriorFaceIndex S i := by
          apply Fin.ext
          change column.1 = i.1
          have h := hcoordinates.2.1
          simp [gridEndpoint, upperGridIndex] at h
          omega
        have hrow : row = rxInteriorFaceIndex S j := by
          apply Fin.ext
          change row.1 = j.1
          have h := hcoordinates.2.2
          simp [gridEndpoint, upperGridIndex] at h
          omega
        rw [hcolumn, hrow]
        rfl
    · rcases material with ⟨materialCopy, endpoint⟩
      have howner : oldX = x := congrArg Sigma.fst hx
      subst oldX
      have hvertex : doubleCylinderRectangleCorner P x S rectangle
          (materialCopy, endpoint) =
          (copy, Sum.inr (Sum.inr (face, i, j))) :=
        eq_of_heq (Sigma.mk.inj_iff.mp hx).2
      have hsubdivision := congrArg Prod.snd hvertex
      fin_cases endpoint
      · have hmember := (subdivisionBoundaryEdgeStart P x S rectangle).2
        rw [subdivisionBoundaryEdgeStart_value] at hmember
        have himpossible : subdivisionEdgeStart P x S rectangle.1 =
            Sum.inr (Sum.inr (face, i, j)) := by
          simpa [doubleCylinderRectangleCorner] using hsubdivision
        rw [himpossible] at hmember
        simp [subdivisionBoundaryVertexMember] at hmember
      · have hmember := (subdivisionBoundaryEdgeEnd P x S rectangle).2
        rw [subdivisionBoundaryEdgeEnd_value] at hmember
        have himpossible : subdivisionEdgeEnd P x S rectangle.1 =
            Sum.inr (Sum.inr (face, i, j)) := by
          simpa [doubleCylinderRectangleCorner] using hsubdivision
        rw [himpossible] at hmember
        simp [subdivisionBoundaryVertexMember] at hmember
  · rcases glue with ⟨a, edge, endpoint⟩
    have howner : a.1.1 = x := congrArg Sigma.fst hx
    subst x
    have hvertex : edgeEndpoint
          (tannerDoubleCylinderEdgeStart P a.1.1 S)
          (tannerDoubleCylinderEdgeEnd P a.1.1 S)
          (qToXDoubleCylinderEdgeRaw P a.1.2 a.1.1 a.2 S edge) endpoint =
        (copy, Sum.inr (Sum.inr (face, i, j))) :=
      eq_of_heq (Sigma.mk.inj_iff.mp hx).2
    rcases edge with copyEdge | vertical
    · rcases copyEdge with ⟨edgeCopy, qEdge⟩
      fin_cases endpoint
      · have hmember :=
            (subdivisionBoundaryEdgeStart P a.1.1 S
              (qToXSubdivisionBoundaryEdge P a.1.2 a.1.1 a.2 S qEdge)).2
        rw [subdivisionBoundaryEdgeStart_value] at hmember
        have himpossible : subdivisionEdgeStart P a.1.1 S
              (qToXSubdivisionBoundaryEdge P a.1.2 a.1.1 a.2 S qEdge).1 =
            Sum.inr (Sum.inr (face, i, j)) := by
          simpa [edgeEndpoint, qToXDoubleCylinderEdgeRaw,
            tannerDoubleCylinderEdgeStart] using congrArg Prod.snd hvertex
        rw [himpossible] at hmember
        simp [subdivisionBoundaryVertexMember] at hmember
      · have hmember :=
            (subdivisionBoundaryEdgeEnd P a.1.1 S
              (qToXSubdivisionBoundaryEdge P a.1.2 a.1.1 a.2 S qEdge)).2
        rw [subdivisionBoundaryEdgeEnd_value] at hmember
        have himpossible : subdivisionEdgeEnd P a.1.1 S
              (qToXSubdivisionBoundaryEdge P a.1.2 a.1.1 a.2 S qEdge).1 =
            Sum.inr (Sum.inr (face, i, j)) := by
          simpa [edgeEndpoint, qToXDoubleCylinderEdgeRaw,
            tannerDoubleCylinderEdgeEnd] using congrArg Prod.snd hvertex
        rw [himpossible] at hmember
        simp [subdivisionBoundaryVertexMember] at hmember
    · let boundaryVertex := subdivisionOriginalBoundaryVertex P a.1.1 S
          (xBoundaryEdgeEnd P a.1.1
            (qToXBoundaryEdge P a.1.2 a.1.1 a.2 vertical))
      have hmember := boundaryVertex.2
      have himpossible : boundaryVertex.1 =
          Sum.inr (Sum.inr (face, i, j)) := by
        fin_cases endpoint <;>
          simpa [boundaryVertex, edgeEndpoint, qToXDoubleCylinderEdgeRaw,
            tannerDoubleCylinderEdgeStart, tannerDoubleCylinderEdgeEnd] using
            congrArg Prod.snd hvertex
      rw [himpossible] at hmember
      simp [subdivisionBoundaryVertexMember] at hmember
  · rcases old with ⟨oldFace, oldCopy⟩
    have howner : P.faceX oldFace = x := congrArg Sigma.fst hx
    subst x
    have hvertex :
        (oldCopy, Sum.inl
          (xStarFaceZVertex P (P.faceX oldFace) (oldFaceInXStar P oldFace))) =
          (copy, Sum.inr (Sum.inr (face, i, j))) :=
      eq_of_heq (Sigma.mk.inj_iff.mp hx).2
    cases congrArg Prod.snd hvertex
theorem rxFaceInteriorNeighborQ_eq
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (face : XStarFace P x) (i j : Fin (S.half - 1)) :
    localFaceQAt P S (rxFaceInteriorLocalFaceSW P S x copy face i j) 1 =
        localFaceQAt P S (rxFaceInteriorLocalFaceSE P S x copy face i j) 1 ∧
      localFaceQAt P S (rxFaceInteriorLocalFaceSW P S x copy face i j) 0 =
        localFaceQAt P S (rxFaceInteriorLocalFaceNW P S x copy face i j) 0 ∧
      localFaceQAt P S (rxFaceInteriorLocalFaceSE P S x copy face i j) 0 =
        localFaceQAt P S (rxFaceInteriorLocalFaceNE P S x copy face i j) 0 ∧
      localFaceQAt P S (rxFaceInteriorLocalFaceNW P S x copy face i j) 1 =
        localFaceQAt P S (rxFaceInteriorLocalFaceNE P S x copy face i j) 1 := by
  constructor
  · simp [rxFaceInteriorLocalFaceSW, rxFaceInteriorLocalFaceSE,
      localFaceQAt, localFaceQ1, localFaceQ1Edge, localFaceQ1EdgeAt,
      subdivisionFaceBoundaryEdge_one_one,
      subdivisionFaceBoundaryEdge_one_zero, rxInteriorFaceIndex,
      rxInteriorUpperFaceIndex]
    congr 4
  constructor
  · simp [rxFaceInteriorLocalFaceSW, rxFaceInteriorLocalFaceNW,
      localFaceQAt, localFaceQ0, localFaceQ0Edge, localFaceQ0EdgeAt,
      subdivisionFaceBoundaryEdge_zero_one,
      subdivisionFaceBoundaryEdge_zero_zero, rxInteriorFaceIndex,
      rxInteriorUpperFaceIndex]
    congr 4
  constructor
  · simp [rxFaceInteriorLocalFaceSE, rxFaceInteriorLocalFaceNE,
      localFaceQAt, localFaceQ0, localFaceQ0Edge, localFaceQ0EdgeAt,
      subdivisionFaceBoundaryEdge_zero_one,
      subdivisionFaceBoundaryEdge_zero_zero, rxInteriorFaceIndex,
      rxInteriorUpperFaceIndex]
    congr 4
  · simp [rxFaceInteriorLocalFaceNW, rxFaceInteriorLocalFaceNE,
      localFaceQAt, localFaceQ1, localFaceQ1Edge, localFaceQ1EdgeAt,
      subdivisionFaceBoundaryEdge_one_one,
      subdivisionFaceBoundaryEdge_one_zero, rxInteriorFaceIndex,
      rxInteriorUpperFaceIndex]
    congr 4
end BDL26RXLocalReplacement
end Coding
end QEC


