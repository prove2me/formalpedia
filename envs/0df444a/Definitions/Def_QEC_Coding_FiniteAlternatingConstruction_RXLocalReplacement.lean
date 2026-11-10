-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
-- name    : QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T00:02:18.617306+00:00
-- url     : https://prove2.me/theorems/ada3adc4-dc89-464e-9462-8fb0046a1f7c
-- title:
--   RXLocal Replacement
-- statement:
--   Definitions and structural lemmas for RXLocal Replacement, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement_Part1_QECert
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
theorem rxReplacementXBoundaryRoot_value
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (x : P.X) (vertex : DoubleCylinderVertex P x S) :
    (rxReplacementXBoundaryRoot P A3 S ⟨x, vertex⟩).1 =
      Vertex.q (Sum.inl ⟨x,
        (rxDoubleCylinderVertexIncidentEdge P A3 x S vertex).1.1⟩) := by
  classical
  generalize hincident : rxDoubleCylinderVertexIncidentEdge P A3 x S vertex =
    incident
  rcases incident with ⟨⟨edge, endpoint⟩, hendpoint⟩
  generalize howner : rxLocalEdgeCornerOwner P A3 S x edge = owner
  rcases owner with ⟨⟨⟨ownerX, localCell, materialCorner⟩, qCorner⟩, hq⟩
  have hsigma : (⟨ownerX,
      if qCorner = 0 then localFaceQ0EdgeAt P ownerX S localCell materialCorner
      else localFaceQ1EdgeAt P ownerX S localCell materialCorner⟩ :
        Σ ownerX : P.X, DoubleCylinderEdge P ownerX S) = ⟨x, edge⟩ := by
    fin_cases qCorner
    · simpa [localFaceQAt, localFaceQ0, localFaceQ0Edge] using hq
    · simpa [localFaceQAt, localFaceQ1, localFaceQ1Edge] using hq
  have hownerX : ownerX = x := congrArg Sigma.fst hsigma
  subst ownerX
  simp only [rxReplacementXBoundaryRoot]
  rw [hincident, howner]
theorem rxReplacementXBoundaryRoot_faceInterior
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (x : P.X) (copy : Two) (face : XStarFace P x)
    (i j : Fin (S.half - 1)) :
    rxReplacementXBoundaryRoot P A3 S
        ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ =
      xBoundaryEdgeStart (rxReplacementPresentation P S)
        ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
          (rxFaceInteriorXStarFaceSW P S x copy face i j) 0) := by
  apply Subtype.ext
  rw [rxReplacementXBoundaryRoot_value]
  congr 1
theorem rxOriginalBoundaryQIncidentEndpointZero
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (x : P.X) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    (A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2
      |>.xBoundaryIncidentEdge x ⟨Vertex.q q, member⟩).1.2 = 0 := by
  let A2 := A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2
  let vertex : XStarBoundaryVertex P x := ⟨Vertex.q q, member⟩
  generalize hselected : A2.xBoundaryIncidentEdge x vertex = selected
  rcases selected with ⟨⟨boundary, endpoint⟩, hendpoint⟩
  fin_cases endpoint
  · rfl
  · have hraw := congrArg Subtype.val hendpoint
    rcases boundary with ⟨raw, boundaryMember⟩
    rcases raw with impossible | edge
    · simp [xStarBoundaryEdgeMember] at boundaryMember
    · change Vertex.z edge.1.2 = Vertex.q q at hraw
      cases hraw
theorem rxOriginalBoundaryQRootBoundaryEdge_eq_selected
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (x : P.X) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    rxOriginalBoundaryQRootBoundaryEdge P A4 x q member =
      (A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2
        |>.xBoundaryIncidentEdge x ⟨Vertex.q q, member⟩).1.1 := by
  apply Subtype.ext
  exact rxOriginalBoundaryQRootOwnerFromIncident_edge P A4 x q member
    (A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2
      |>.xBoundaryIncidentEdge x ⟨Vertex.q q, member⟩)
theorem rxDoubleCylinderVertexIncidentEdge_originalQ
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    (rxDoubleCylinderVertexIncidentEdge P
      A4.toTannerSquareAdmissibleV3 x S
      (copy, Sum.inl ⟨Vertex.q q, by
        simpa [xStarBoundaryVertexMember, xStarVertexMember] using member⟩)).1 =
      (Sum.inl (copy,
        (rxOriginalBoundaryQRootRectangle P A4 S x q member).1), 0) := by
  classical
  let A2 := A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2
  let vertex : XStarBoundaryVertex P x := ⟨Vertex.q q, member⟩
  have hzero : (A2.xBoundaryIncidentEdge x vertex).1.2 = 0 :=
    rxOriginalBoundaryQIncidentEndpointZero P A4 x q member
  have hnormalized := subdivisionBoundaryIncidentEdge_original_zero
    P A2 x S vertex hzero
  have hnormalized' :
      (subdivisionBoundaryIncidentEdge P
        A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2 x S
        (subdivisionOriginalBoundaryVertex P x S ⟨Vertex.q q, member⟩)).1 =
        (subdivisionOriginalBoundaryEdge P x S
          (A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2
            |>.xBoundaryIncidentEdge x ⟨Vertex.q q, member⟩).1.1
          ⟨0, S.half_pos⟩, 0) := by
    simpa [A2, vertex] using hnormalized
  have hedge := congrArg (fun owned => owned.1.1) hnormalized'
  have hendpoint := congrArg Prod.snd hnormalized'
  simp only [rxDoubleCylinderVertexIncidentEdge,
    rxSubdivisionVertexIncidentEdge]
  rw [show
    (subdivisionBoundaryIncidentEdge P
      A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2 x S
      (subdivisionOriginalBoundaryVertex P x S ⟨Vertex.q q, by
        simpa [xStarBoundaryVertexMember, xStarVertexMember] using member⟩)).1.2 =
      0 by simpa using hendpoint]
  apply Prod.ext
  · apply congrArg Sum.inl
    apply Prod.ext
    · rfl
    · rw [show
        (subdivisionBoundaryIncidentEdge P
          A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2 x S
          (subdivisionOriginalBoundaryVertex P x S ⟨Vertex.q q, by
            simpa [xStarBoundaryVertexMember, xStarVertexMember] using member⟩)).1.1.1 =
          (subdivisionOriginalBoundaryEdge P x S
            (A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2
              |>.xBoundaryIncidentEdge x ⟨Vertex.q q, member⟩).1.1
            ⟨0, S.half_pos⟩).1 by simpa using hedge]
      simp only [rxOriginalBoundaryQRootRectangle,
        subdivisionOriginalBoundaryEdge]
      rw [rxOriginalBoundaryQRootBoundaryEdge_eq_selected
        P A4 x q member]
      simp [rxRadialGridZero]
  · rfl
theorem rxReplacementXBoundaryRoot_originalQ
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    rxReplacementXBoundaryRoot P A4.toTannerSquareAdmissibleV3 S
        (rxOriginalBoundaryQXCoordinate P S x copy q member) =
      xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q member)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxOriginalBoundaryQXCoordinate P S x copy q member)
          (rxOriginalBoundaryQRootXStarFace P A4 S x copy q member) 0) := by
  change rxReplacementXBoundaryRoot P A4.toTannerSquareAdmissibleV3 S
      ⟨x, (copy, Sum.inl ⟨Vertex.q q, by
        simpa [xStarBoundaryVertexMember, xStarVertexMember] using member⟩)⟩ = _
  apply Subtype.ext
  rw [rxReplacementXBoundaryRoot_value]
  rw [rxDoubleCylinderVertexIncidentEdge_originalQ
    P A4 S x copy q member]
  rfl
noncomputable def rxOriginalBoundaryQTargetBoundaryPathHistorical
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (target : RXOriginalBoundaryQTarget P x q) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q member))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q member))
      (rxReplacementXBoundaryRoot P
        A4.toTannerSquareAdmissibleV3 S
        (rxOriginalBoundaryQXCoordinate P S x copy q member))
      (rxOriginalBoundaryQTargetBoundaryVertex
        P A4 S x copy q member target) := by
  rw [rxReplacementXBoundaryRoot_originalQ P A4 S x copy q member]
  exact rxOriginalBoundaryQTargetBoundaryPath
    P A4 S x copy q member target
noncomputable def rxOriginalBoundaryQRawFaceCorner
    (P : TannerSquarePresentation) (face : P.Face) (q : P.Q) : Two :=
  if P.faceQ face 0 = q then 0 else 1
theorem rxOriginalBoundaryQRawFaceCorner_eq
    (P : TannerSquarePresentation) (face : P.Face) (q : P.Q)
    (corner : Two) (hq : P.faceQ face corner = q) :
    rxOriginalBoundaryQRawFaceCorner P face q = corner := by
  unfold rxOriginalBoundaryQRawFaceCorner
  split <;> rename_i hzero
  · exact P.faceQ_injective face (hzero.trans hq.symm)
  · fin_cases corner
    · exact False.elim (hzero hq)
    · rfl
def rxOriginalBoundaryQRawLocalOldFace?
    (P : TannerSquarePresentation) (S : OddScale) :
    RXLocalFace P S → Option P.Face
  | ⟨_, Sum.inl (_, (face, _, _)), _⟩ => some face.1
  | ⟨_, Sum.inr _, _⟩ => none
theorem rxOriginalBoundaryQRawSmallZ_normalize
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (q : P.Q)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (candidateX : P.X) (candidateCopy : Two)
    (face : XStarFace P candidateX) (column row : Fin S.half)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q oldMember)
      (Vertex.z (Sum.inl (Sum.inl
        ⟨candidateX, Sum.inl (candidateCopy, (face, column, row))⟩))) = true) :
    candidateX = x ∧
      ∀ howner : candidateX = x,
        let transportedFace : XStarFace P x := howner ▸ face
        let corner := rxOriginalBoundaryQRawFaceCorner P transportedFace.1 q
        P.faceQ transportedFace.1 corner = q ∧
          (Sum.inl (Sum.inl
            ⟨candidateX, Sum.inl (candidateCopy, (face, column, row))⟩) :
              RX2 P S) =
            localFaceZ P S
              (rxOriginalBoundaryQLocalFaceAt
                P S x copy transportedFace corner) := by
  classical
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl]
    at member
  rw [decide_eq_true_eq] at member
  obtain ⟨candidate, hx, hzTag⟩ := member
  have hx' : rxFaceX P S candidate =
      rxOriginalBoundaryQXCoordinate P S x copy q oldMember := by
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
      simpa [rxFaceX, localFaceX, rxOriginalBoundaryQXCoordinate] using congrArg Sigma.fst hx'
    subst candidateX
    refine ⟨rfl, ?_⟩
    intro howner'
    have hproof : howner' = (rfl : x = x) := Subsingleton.elim _ _
    cases hproof
    obtain ⟨targetFace, targetCorner, hq, hcandidate⟩ :=
      rxOriginalBoundaryQSmallFace_cases P S x copy q oldMember
        ⟨x, Sum.inl (candidateCopy, (face, column, row)), material⟩
        (by simpa [rxFaceX] using hx')
        ⟨(candidateCopy, (face, column, row)), rfl⟩
    have hfaceValue : face.1 = targetFace.1 := by
      have hfaceOption := congrArg
        (rxOriginalBoundaryQRawLocalOldFace? P S) hcandidate
      fin_cases targetCorner <;>
        simpa [rxOriginalBoundaryQRawLocalOldFace?,
          rxOriginalBoundaryQLocalFaceAt, rxTwoElim] using hfaceOption
    have hface : face = targetFace := by
      apply Subtype.ext
      exact hfaceValue
    subst targetFace
    have hcorner := rxOriginalBoundaryQRawFaceCorner_eq
      P face.1 q targetCorner hq
    subst targetCorner
    refine ⟨hq, ?_⟩
    simpa only [localFaceZ] using
      congrArg (localFaceZ P S) hcandidate
  · cases hzTag
  · cases hzTag
noncomputable def rxOriginalBoundaryQRawSmallZPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (candidateX : P.X) (candidateCopy : Two)
    (face : XStarFace P candidateX) (column row : Fin S.half)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q oldMember)
      (Vertex.z (Sum.inl (Sum.inl
        ⟨candidateX, Sum.inl (candidateCopy, (face, column, row))⟩))) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      (rxReplacementXBoundaryRoot P
        A4.toTannerSquareAdmissibleV3 S
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      ⟨Vertex.z (Sum.inl (Sum.inl
        ⟨candidateX, Sum.inl (candidateCopy, (face, column, row))⟩)),
        member⟩ := by
  obtain ⟨howner, hnormalize⟩ := rxOriginalBoundaryQRawSmallZ_normalize
    P S x copy q oldMember candidateX candidateCopy face column row member
  subst candidateX
  let corner := rxOriginalBoundaryQRawFaceCorner P face.1 q
  obtain ⟨hq, hraw⟩ := hnormalize rfl
  let target : RXOriginalBoundaryQTarget P x q :=
    .constructor (.smallZ face corner hq)
  let path := rxOriginalBoundaryQTargetBoundaryPathHistorical
    P A4 S x copy q oldMember target
  have htarget : rxOriginalBoundaryQTargetBoundaryVertex
        P A4 S x copy q oldMember target =
      ⟨Vertex.z (Sum.inl (Sum.inl
        ⟨x, Sum.inl (candidateCopy, (face, column, row))⟩)), member⟩ := by
    apply Subtype.ext
    exact congrArg Vertex.z hraw.symm
  exact htarget ▸ path
def rxOriginalBoundaryQRawLocalQZEdge?
    (P : TannerSquarePresentation) (S : OddScale) :
    RXLocalFace P S → Option (QZEdge P)
  | ⟨_, Sum.inr ⟨Sum.inl (⟨Sum.inr edge, _⟩, _), _⟩, _⟩ => some edge
  | _ => none
theorem rxOriginalBoundaryQRawRectangleZ_normalize
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (q : P.Q)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (candidateX : P.X) (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P candidateX (Sum.inr edge) = true)
    (segment : Fin S.half)
    (boundaryMember : subdivisionBoundaryEdgeMember P candidateX S
      (Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment)) = true)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q oldMember)
      (Vertex.z (Sum.inl (Sum.inl
        ⟨candidateX, Sum.inr
          ⟨Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment),
            boundaryMember⟩⟩))) = true) :
    candidateX = x ∧
      ∀ howner : candidateX = x,
        let transportedEdge : QZEdge P := edge
        let transportedMember : xStarEdgeMember P x
            (Sum.inr transportedEdge) = true := howner ▸ edgeMember
        transportedEdge.1.1 = q ∧
          (Sum.inl (Sum.inl
            ⟨candidateX, Sum.inr
              ⟨Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment),
                boundaryMember⟩⟩) : RX2 P S) =
            localFaceZ P S
              (rxOriginalBoundaryQRectangleLocalFaceAt
                P S x copy transportedEdge transportedMember) := by
  classical
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl]
    at member
  rw [decide_eq_true_eq] at member
  obtain ⟨candidate, hx, hzTag⟩ := member
  have hx' : rxFaceX P S candidate =
      rxOriginalBoundaryQXCoordinate P S x copy q oldMember := by
    simp only [xStarFaceMember, decide_eq_true_eq] at hx
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
    exact hx
  rcases candidate with candidateLocal | candidateGlue | candidateOld
  · rcases candidateLocal with ⟨ownerX, localCell, material⟩
    have hcell :
        (⟨candidateX, Sum.inr
          ⟨Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment),
            boundaryMember⟩⟩ :
            Σ ownerX : P.X, DoubleCylinderFace P ownerX S) =
        ⟨ownerX, localCell⟩ := by
      exact Sum.inl.inj (Sum.inl.inj hzTag)
    cases hcell
    have howner : candidateX = x := by
      simpa [rxFaceX, localFaceX, rxOriginalBoundaryQXCoordinate] using congrArg Sigma.fst hx'
    subst candidateX
    refine ⟨rfl, ?_⟩
    intro howner'
    have hproof : howner' = (rfl : x = x) := Subsingleton.elim _ _
    cases hproof
    obtain ⟨targetEdge, targetMember, hq, hcandidate⟩ :=
      rxOriginalBoundaryQRectangleFace_cases P S x copy q oldMember
        ⟨x, Sum.inr
          ⟨Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment),
            boundaryMember⟩, material⟩
        (by simpa [rxFaceX] using hx')
        ⟨⟨Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment),
          boundaryMember⟩, rfl⟩
    have hedgeOption := congrArg
      (rxOriginalBoundaryQRawLocalQZEdge? P S) hcandidate
    have hedge : edge = targetEdge := by
      simpa [rxOriginalBoundaryQRawLocalQZEdge?,
        rxOriginalBoundaryQRectangleLocalFaceAt,
        subdivisionOriginalBoundaryEdge,
        rxStarEdgeInteriorBoundaryEdge,
        xStarBoundaryEdgeToStar] using hedgeOption
    subst targetEdge
    cases Subsingleton.elim targetMember edgeMember
    refine ⟨hq, ?_⟩
    simpa only [localFaceZ] using
      congrArg (localFaceZ P S) hcandidate
  · cases hzTag
  · cases hzTag
noncomputable def rxOriginalBoundaryQRawRectangleZPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (candidateX : P.X) (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P candidateX (Sum.inr edge) = true)
    (segment : Fin S.half)
    (boundaryMember : subdivisionBoundaryEdgeMember P candidateX S
      (Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment)) = true)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q oldMember)
      (Vertex.z (Sum.inl (Sum.inl
        ⟨candidateX, Sum.inr
          ⟨Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment),
            boundaryMember⟩⟩))) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      (rxReplacementXBoundaryRoot P
        A4.toTannerSquareAdmissibleV3 S
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      ⟨Vertex.z (Sum.inl (Sum.inl
        ⟨candidateX, Sum.inr
          ⟨Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment),
            boundaryMember⟩⟩)), member⟩ := by
  obtain ⟨howner, hnormalize⟩ :=
    rxOriginalBoundaryQRawRectangleZ_normalize
      P S x copy q oldMember candidateX edge edgeMember
        segment boundaryMember member
  subst candidateX
  obtain ⟨hq, hraw⟩ := hnormalize rfl
  let target : RXOriginalBoundaryQTarget P x q :=
    .constructor (.rectangleZ edge edgeMember hq)
  let path := rxOriginalBoundaryQTargetBoundaryPathHistorical
    P A4 S x copy q oldMember target
  have htarget : rxOriginalBoundaryQTargetBoundaryVertex
        P A4 S x copy q oldMember target =
      ⟨Vertex.z (Sum.inl (Sum.inl
        ⟨x, Sum.inr
          ⟨Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment),
            boundaryMember⟩⟩)), member⟩ := by
    apply Subtype.ext
    exact congrArg Vertex.z hraw.symm
  exact htarget ▸ path
def rxOriginalBoundaryQRawGlueQ
    (P : TannerSquarePresentation) (S : OddScale) :
    RXXQGlueFace P S → P.Q
  | ⟨a, _, _⟩ => a.1.2
def rxOriginalBoundaryQRawGlueZ
    (P : TannerSquarePresentation) (S : OddScale) :
    RXXQGlueFace P S → P.Z
  | ⟨a, edge, _⟩ =>
      (qDoubleCylinderUnderlyingStarEdge P a.1.2 S edge).1
def rxOriginalBoundaryQRawGlueCopied
    (P : TannerSquarePresentation) (S : OddScale) :
    RXXQGlueFace P S → Bool
  | ⟨_, Sum.inl _, _⟩ => true
  | ⟨_, Sum.inr _, _⟩ => false
theorem rxOriginalBoundaryQRawGlueZ_normalize
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (q : P.Q)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (candidateQ : P.Q) (candidateCopy : Two)
    (edge : QStarEdge P candidateQ) (segment : Fin S.half)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q oldMember)
      (Vertex.z (Sum.inl (Sum.inr
        ⟨candidateQ, Sum.inl (candidateCopy, (edge, segment))⟩))) = true) :
    candidateQ = q ∧
      ∀ hq : candidateQ = q,
        let transportedEdge : QStarEdge P q := hq ▸ edge
        (Sum.inl (Sum.inr
          ⟨candidateQ, Sum.inl (candidateCopy, (edge, segment))⟩) :
            RX2 P S) =
          glueFaceZ P S
            (rxOriginalBoundaryQGlueFaceAt
              P S x copy q oldMember transportedEdge) := by
  classical
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl]
    at member
  rw [decide_eq_true_eq] at member
  obtain ⟨candidate, hx, hzTag⟩ := member
  have hx' : rxFaceX P S candidate =
      rxOriginalBoundaryQXCoordinate P S x copy q oldMember := by
    simp only [xStarFaceMember, decide_eq_true_eq] at hx
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
    exact hx
  rcases candidate with candidateLocal | candidateGlue | candidateOld
  · cases hzTag
  · rcases candidateGlue with ⟨a, qEdge, endpoint⟩
    have hqEdge : (⟨candidateQ,
          Sum.inl (candidateCopy, (edge, segment))⟩ :
          Σ q : P.Q, QDoubleCylinderEdge P q S) =
        ⟨a.1.2, qEdge⟩ := by
      exact Sum.inr.inj (Sum.inl.inj hzTag)
    cases hqEdge
    rcases a with ⟨⟨oldX, oldQ⟩, hxq⟩
    have howner : oldX = x := congrArg Sigma.fst hx'
    subst oldX
    obtain ⟨targetEdge, hcandidate⟩ :=
      rxOriginalBoundaryQGlueFace_cases P S x copy q oldMember
        ⟨⟨(x, oldQ), hxq⟩,
          Sum.inl (candidateCopy, (edge, segment)), endpoint⟩
        (by simpa [rxFaceX] using hx')
    have hqValue := congrArg (rxOriginalBoundaryQRawGlueQ P S) hcandidate
    have hq : oldQ = q := by
      simpa [rxOriginalBoundaryQRawGlueQ,
        rxOriginalBoundaryQGlueFaceAt] using hqValue
    subst oldQ
    refine ⟨rfl, ?_⟩
    intro hq'
    have hproof : hq' = (rfl : q = q) := Subsingleton.elim _ _
    cases hproof
    have hzValue := congrArg (rxOriginalBoundaryQRawGlueZ P S) hcandidate
    have hedge : edge = targetEdge := by
      apply Subtype.ext
      simpa [rxOriginalBoundaryQRawGlueZ,
        rxOriginalBoundaryQGlueFaceAt,
        qDoubleCylinderUnderlyingStarEdge] using hzValue
    subst targetEdge
    simpa only [glueFaceZ] using
      congrArg (glueFaceZ P S) hcandidate
  · cases hzTag
noncomputable def rxOriginalBoundaryQRawGlueZPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (candidateQ : P.Q) (candidateCopy : Two)
    (edge : QStarEdge P candidateQ) (segment : Fin S.half)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q oldMember)
      (Vertex.z (Sum.inl (Sum.inr
        ⟨candidateQ, Sum.inl (candidateCopy, (edge, segment))⟩))) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      (rxReplacementXBoundaryRoot P
        A4.toTannerSquareAdmissibleV3 S
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      ⟨Vertex.z (Sum.inl (Sum.inr
        ⟨candidateQ, Sum.inl (candidateCopy, (edge, segment))⟩)),
        member⟩ := by
  obtain ⟨hq, hnormalize⟩ := rxOriginalBoundaryQRawGlueZ_normalize
    P S x copy q oldMember candidateQ candidateCopy edge segment member
  subst candidateQ
  have hraw := hnormalize rfl
  let target : RXOriginalBoundaryQTarget P x q :=
    .glue (.z edge)
  let path := rxOriginalBoundaryQTargetBoundaryPathHistorical
    P A4 S x copy q oldMember target
  have htarget : rxOriginalBoundaryQTargetBoundaryVertex
        P A4 S x copy q oldMember target =
      ⟨Vertex.z (Sum.inl (Sum.inr
        ⟨q, Sum.inl (candidateCopy, (edge, segment))⟩)), member⟩ := by
    apply Subtype.ext
    exact congrArg Vertex.z hraw.symm
  exact htarget ▸ path
theorem rxOriginalBoundaryQRawVerticalGlueZ_false
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (q : P.Q)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (candidateQ : P.Q) (edge : QStarEdge P candidateQ)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q oldMember)
      (Vertex.z (Sum.inl (Sum.inr
        ⟨candidateQ, Sum.inr edge⟩))) = true) : False := by
  classical
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl]
    at member
  rw [decide_eq_true_eq] at member
  obtain ⟨candidate, hx, hzTag⟩ := member
  have hx' : rxFaceX P S candidate =
      rxOriginalBoundaryQXCoordinate P S x copy q oldMember := by
    simp only [xStarFaceMember, decide_eq_true_eq] at hx
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
    exact hx
  rcases candidate with candidateLocal | candidateGlue | candidateOld
  · cases hzTag
  · rcases candidateGlue with ⟨a, qEdge, endpoint⟩
    have hqEdge : (⟨candidateQ, Sum.inr edge⟩ :
          Σ q : P.Q, QDoubleCylinderEdge P q S) =
        ⟨a.1.2, qEdge⟩ := by
      exact Sum.inr.inj (Sum.inl.inj hzTag)
    cases hqEdge
    rcases a with ⟨⟨oldX, oldQ⟩, hxq⟩
    have howner : oldX = x := congrArg Sigma.fst hx'
    subst oldX
    obtain ⟨targetEdge, hcandidate⟩ :=
      rxOriginalBoundaryQGlueFace_cases P S x copy q oldMember
        ⟨⟨(x, oldQ), hxq⟩, Sum.inr edge, endpoint⟩
        (by simpa [rxFaceX] using hx')
    have hqValue := congrArg (rxOriginalBoundaryQRawGlueQ P S) hcandidate
    have hq : oldQ = q := by
      simpa [rxOriginalBoundaryQRawGlueQ,
        rxOriginalBoundaryQGlueFaceAt] using hqValue
    subst oldQ
    have himpossible := congrArg
      (rxOriginalBoundaryQRawGlueCopied P S) hcandidate
    simp [rxOriginalBoundaryQRawGlueCopied,
      rxOriginalBoundaryQGlueFaceAt] at himpossible
  · cases hzTag
theorem rxOriginalBoundaryQRawOldZ_false
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (q : P.Q)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (candidateZ : P.Z) (candidateCopy : Two)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q oldMember)
      (Vertex.z (Sum.inr (candidateZ, candidateCopy))) = true) : False := by
  classical
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl]
    at member
  rw [decide_eq_true_eq] at member
  obtain ⟨candidate, hx, hzTag⟩ := member
  have hx' : rxFaceX P S candidate =
      rxOriginalBoundaryQXCoordinate P S x copy q oldMember := by
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
        (copy, Sum.inl ⟨Vertex.q q, by
          simpa [xStarBoundaryVertexMember, xStarVertexMember]
            using oldMember⟩) :=
      eq_of_heq (Sigma.mk.inj_iff.mp hx').2
    have hinl := Sum.inl.inj (congrArg Prod.snd hvertex)
    have hraw := congrArg Subtype.val hinl
    change Vertex.z (P.faceZ oldFace) = Vertex.q q at hraw
    cases hraw
noncomputable def rxOriginalBoundaryQRawZPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (newZ : RX2 P S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q oldMember)
      (Vertex.z newZ) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      (rxReplacementXBoundaryRoot P
        A4.toTannerSquareAdmissibleV3 S
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      ⟨Vertex.z newZ, member⟩ := by
  rcases newZ with localOrGlue | old
  · rcases localOrGlue with localZ | glue
    · rcases localZ with ⟨candidateX, cell⟩
      rcases cell with small | rectangle
      · rcases small with ⟨candidateCopy, face, column, row⟩
        exact rxOriginalBoundaryQRawSmallZPath
          P A4 S x copy q oldMember candidateX candidateCopy
            face column row member
      · rcases rectangle with ⟨raw, boundaryMember⟩
        rcases raw with original | interior
        · rcases original with ⟨starEdge, segment⟩
          rcases starEdge with ⟨rawEdge, edgeMember⟩
          rcases rawEdge with xqEdge | qzEdge
          · simp [subdivisionBoundaryEdgeMember,
              xStarBoundaryEdgeMember] at boundaryMember
          · exact rxOriginalBoundaryQRawRectangleZPath
              P A4 S x copy q oldMember candidateX qzEdge
                edgeMember segment boundaryMember member
        · simp [subdivisionBoundaryEdgeMember] at boundaryMember
    · rcases glue with ⟨candidateQ, edge⟩
      rcases edge with copied | vertical
      · rcases copied with ⟨candidateCopy, qEdge⟩
        rcases qEdge with ⟨starEdge, segment⟩
        exact rxOriginalBoundaryQRawGlueZPath
          P A4 S x copy q oldMember candidateQ candidateCopy
            starEdge segment member
      · exact False.elim (rxOriginalBoundaryQRawVerticalGlueZ_false
          P S x copy q oldMember candidateQ vertical member)
  · rcases old with ⟨candidateZ, candidateCopy⟩
    exact False.elim (rxOriginalBoundaryQRawOldZ_false
      P S x copy q oldMember candidateZ candidateCopy member)
theorem rxOriginalBoundaryQRawLocalQ_endpoint
    (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (copy : Two) (q : P.Q)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (candidateX : P.X) (edge : DoubleCylinderEdge P candidateX S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q oldMember)
      (Vertex.q (Sum.inl ⟨candidateX, edge⟩)) = true) :
    candidateX = x ∧
      ∀ howner : candidateX = x,
        let transportedEdge : DoubleCylinderEdge P x S := howner ▸ edge
        tannerDoubleCylinderEdgeStart P x S transportedEdge =
            (copy, Sum.inl ⟨Vertex.q q, by
              simpa [xStarBoundaryVertexMember, xStarVertexMember]
                using oldMember⟩) ∨
          tannerDoubleCylinderEdgeEnd P x S transportedEdge =
            (copy, Sum.inl ⟨Vertex.q q, by
              simpa [xStarBoundaryVertexMember, xStarVertexMember]
                using oldMember⟩) := by
  classical
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceQ = rxFaceQ P S from rfl]
    at member
  rw [decide_eq_true_eq] at member
  obtain ⟨candidate, hx, hqTag⟩ := member
  have hx' : rxFaceX P S candidate =
      rxOriginalBoundaryQXCoordinate P S x copy q oldMember := by
    simp only [xStarFaceMember, decide_eq_true_eq] at hx
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
    exact hx
  have handle : ∀ cornerTag : Two,
      rxFaceQ P S candidate cornerTag = Sum.inl ⟨candidateX, edge⟩ →
        candidateX = x ∧
          ∀ howner : candidateX = x,
            let transportedEdge : DoubleCylinderEdge P x S := howner ▸ edge
            tannerDoubleCylinderEdgeStart P x S transportedEdge =
                (copy, Sum.inl ⟨Vertex.q q, by
                  simpa [xStarBoundaryVertexMember, xStarVertexMember]
                    using oldMember⟩) ∨
              tannerDoubleCylinderEdgeEnd P x S transportedEdge =
                (copy, Sum.inl ⟨Vertex.q q, by
                  simpa [xStarBoundaryVertexMember, xStarVertexMember]
                    using oldMember⟩) := by
    intro cornerTag hqTag'
    obtain ⟨endpoint, hendpoint⟩ :=
      rxFaceX_eq_endpoint_of_faceQ_eq_xEdge
        P S candidate cornerTag candidateX edge hqTag'
    have hcoordinate :
        (⟨candidateX,
          edgeEndpoint (tannerDoubleCylinderEdgeStart P candidateX S)
            (tannerDoubleCylinderEdgeEnd P candidateX S) edge endpoint⟩ :
            RX0 P S) =
          rxOriginalBoundaryQXCoordinate P S x copy q oldMember :=
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
theorem rxOriginalBoundaryQRawRadialQ_normalize
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (candidateX : P.X) (candidateCopy : Two) (edge : XQEdge P)
    (edgeMember : xStarEdgeMember P candidateX (Sum.inl edge) = true)
    (segment : Fin S.half)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q oldMember)
      (Vertex.q (Sum.inl ⟨candidateX,
        Sum.inl (candidateCopy,
          Sum.inl (⟨Sum.inl edge, edgeMember⟩, segment))⟩)) = true) :
    candidateX = x ∧
      ∀ howner : candidateX = x,
        let transportedEdge : XQEdge P := edge
        let transportedMember : xStarEdgeMember P x
            (Sum.inl transportedEdge) = true := howner ▸ edgeMember
        (Sum.inl ⟨candidateX,
          Sum.inl (candidateCopy,
            Sum.inl (⟨Sum.inl edge, edgeMember⟩, segment))⟩ : RX1 P S) =
          localFaceQAt P S
            (rxOriginalBoundaryQOwnerLocalFace
              P A4 S x copy q oldMember)
            (rxOriginalBoundaryQRootCorner P A4 x q oldMember) := by
  obtain ⟨howner, hendpoint⟩ := rxOriginalBoundaryQRawLocalQ_endpoint
    P S x copy q oldMember candidateX
      (Sum.inl (candidateCopy,
        Sum.inl (⟨Sum.inl edge, edgeMember⟩, segment))) member
  subst candidateX
  refine ⟨rfl, ?_⟩
  intro howner'
  have hproof : howner' = (rfl : x = x) := Subsingleton.elim _ _
  cases hproof
  rcases hendpoint rfl with hstart | hend
  · have hsubdivision := congrArg Prod.snd hstart
    by_cases hzero : segment.1 = 0
    · have hinl :
          (Sum.inl (xStarEdgeStart P x ⟨Sum.inl edge, edgeMember⟩) :
            SubdivisionVertex P x S) =
          Sum.inl ⟨Vertex.q q, by
            simpa [xStarBoundaryVertexMember, xStarVertexMember]
              using oldMember⟩ := by
        simpa [tannerDoubleCylinderEdgeStart, subdivisionEdgeStart,
          subdivisionSegmentStart, hzero] using hsubdivision
      have hraw := congrArg Subtype.val (Sum.inl.inj hinl)
      change Vertex.x edge.1.1 = Vertex.q q at hraw
      cases hraw
    · have himpossible :
          (Sum.inr (Sum.inl
            (⟨Sum.inl edge, edgeMember⟩,
              ⟨segment.1 - 1, by have := segment.2; omega⟩)) :
              SubdivisionVertex P x S) =
            Sum.inl ⟨Vertex.q q, by
              simpa [xStarBoundaryVertexMember, xStarVertexMember]
                using oldMember⟩ := by
        simpa [tannerDoubleCylinderEdgeStart, subdivisionEdgeStart,
          subdivisionSegmentStart, hzero] using hsubdivision
      cases himpossible
  · have hcopy : candidateCopy = copy := congrArg Prod.fst hend
    subst candidateCopy
    have hsubdivision := congrArg Prod.snd hend
    by_cases hlast : segment.1 + 1 = S.half
    · have hinl :
          (Sum.inl (xStarEdgeEnd P x ⟨Sum.inl edge, edgeMember⟩) :
            SubdivisionVertex P x S) =
          Sum.inl ⟨Vertex.q q, by
            simpa [xStarBoundaryVertexMember, xStarVertexMember]
              using oldMember⟩ := by
        simpa [tannerDoubleCylinderEdgeEnd, subdivisionEdgeEnd,
          subdivisionSegmentEnd, hlast] using hsubdivision
      have hraw := congrArg Subtype.val (Sum.inl.inj hinl)
      have hq : edge.1.2 = q := Vertex.q.inj hraw
      have hxEdge : edge.1.1 = x := by
        change decide (∃ face : P.Face,
          xStarFaceMember P x face = true ∧
            decide (edge = faceXQEdge P face 0 ∨
              edge = faceXQEdge P face 1) = true) = true at edgeMember
        rw [decide_eq_true_eq] at edgeMember
        obtain ⟨ownerFace, hxFace, hedge⟩ := edgeMember
        rw [decide_eq_true_eq] at hedge
        rcases hedge with hedge | hedge <;> subst edge
        all_goals simpa [xStarFaceMember, faceXQEdge] using hxFace
      have hedge : ⟨Sum.inl edge, edgeMember⟩ =
          rxOriginalXBoundaryRadialEdge P x q oldMember := by
        apply Subtype.ext
        apply congrArg Sum.inl
        apply Subtype.ext
        exact Prod.ext hxEdge hq
      have hsegment : segment = rxStarEdgeInteriorLastIndex S := by
        apply Fin.ext
        change segment.1 = S.half - 1
        omega
      rw [hedge, hsegment]
      exact (rxOriginalBoundaryQLocalFaceAtRadialQ
        P S x copy q oldMember
          (rxOriginalBoundaryQRootFace P A4 x q oldMember)
          (rxOriginalBoundaryQRootCorner P A4 x q oldMember)
          (rxOriginalBoundaryQRootFace_q P A4 x q oldMember)).symm
    · have himpossible :
          (Sum.inr (Sum.inl
            (⟨Sum.inl edge, edgeMember⟩,
              ⟨segment.1, by have := segment.2; omega⟩)) :
              SubdivisionVertex P x S) =
            Sum.inl ⟨Vertex.q q, by
              simpa [xStarBoundaryVertexMember, xStarVertexMember]
                using oldMember⟩ := by
        simpa [tannerDoubleCylinderEdgeEnd, subdivisionEdgeEnd,
          subdivisionSegmentEnd, hlast] using hsubdivision
      cases himpossible
noncomputable def rxOriginalBoundaryQRawRadialQPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (candidateX : P.X) (candidateCopy : Two) (edge : XQEdge P)
    (edgeMember : xStarEdgeMember P candidateX (Sum.inl edge) = true)
    (segment : Fin S.half)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q oldMember)
      (Vertex.q (Sum.inl ⟨candidateX,
        Sum.inl (candidateCopy,
          Sum.inl (⟨Sum.inl edge, edgeMember⟩, segment))⟩)) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      (rxReplacementXBoundaryRoot P
        A4.toTannerSquareAdmissibleV3 S
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      ⟨Vertex.q (Sum.inl ⟨candidateX,
        Sum.inl (candidateCopy,
          Sum.inl (⟨Sum.inl edge, edgeMember⟩, segment))⟩), member⟩ := by
  obtain ⟨howner, hnormalize⟩ :=
    rxOriginalBoundaryQRawRadialQ_normalize
      P A4 S x copy q oldMember candidateX candidateCopy
        edge edgeMember segment member
  subst candidateX
  have hraw := hnormalize rfl
  let target : RXOriginalBoundaryQTarget P x q :=
    .constructor (.smallQ
      (rxOriginalBoundaryQRootFace P A4 x q oldMember)
      (rxOriginalBoundaryQRootCorner P A4 x q oldMember)
      (rxOriginalBoundaryQRootFace_q P A4 x q oldMember)
      (rxOriginalBoundaryQRootCorner P A4 x q oldMember))
  let path := rxOriginalBoundaryQTargetBoundaryPathHistorical
    P A4 S x copy q oldMember target
  have htarget : rxOriginalBoundaryQTargetBoundaryVertex
        P A4 S x copy q oldMember target =
      ⟨Vertex.q (Sum.inl ⟨x,
        Sum.inl (candidateCopy,
          Sum.inl (⟨Sum.inl edge, edgeMember⟩, segment))⟩), member⟩ := by
    apply Subtype.ext
    exact congrArg Vertex.q hraw.symm
  exact htarget ▸ path
theorem rxOriginalBoundaryQRectangleQ0
    (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (copy : Two) (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true) :
    localFaceQAt P S
        (rxOriginalBoundaryQRectangleLocalFaceAt
          P S x copy edge edgeMember) 0 =
      Sum.inl ⟨x, Sum.inl (copy, Sum.inl
        (⟨Sum.inr edge, edgeMember⟩, rxRadialGridZero S))⟩ := by
  simp [rxOriginalBoundaryQRectangleLocalFaceAt, localFaceQAt,
    localFaceQ0, localFaceQ0Edge, localFaceQ0EdgeAt,
    doubleCylinderRectangleBoundaryEdge,
    rxStarEdgeInteriorBoundaryEdge, subdivisionOriginalBoundaryEdge]
  apply Subtype.ext
  rfl
theorem rxOriginalBoundaryQRawRectangleQ_normalize
    (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (copy : Two) (q : P.Q)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (candidateX : P.X) (candidateCopy : Two) (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P candidateX (Sum.inr edge) = true)
    (segment : Fin S.half)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q oldMember)
      (Vertex.q (Sum.inl ⟨candidateX,
        Sum.inl (candidateCopy,
          Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment))⟩)) = true) :
    candidateX = x ∧
      ∀ howner : candidateX = x,
        let transportedEdge : QZEdge P := edge
        let transportedMember : xStarEdgeMember P x
            (Sum.inr transportedEdge) = true := howner ▸ edgeMember
        transportedEdge.1.1 = q ∧
          (Sum.inl ⟨candidateX,
            Sum.inl (candidateCopy,
              Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment))⟩ : RX1 P S) =
            localFaceQAt P S
              (rxOriginalBoundaryQRectangleLocalFaceAt
                P S x copy transportedEdge transportedMember) 0 := by
  obtain ⟨howner, hendpoint⟩ := rxOriginalBoundaryQRawLocalQ_endpoint
    P S x copy q oldMember candidateX
      (Sum.inl (candidateCopy,
        Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment))) member
  subst candidateX
  refine ⟨rfl, ?_⟩
  intro howner'
  have hproof : howner' = (rfl : x = x) := Subsingleton.elim _ _
  cases hproof
  rcases hendpoint rfl with hstart | hend
  · have hcopy : candidateCopy = copy := congrArg Prod.fst hstart
    subst candidateCopy
    have hsubdivision := congrArg Prod.snd hstart
    by_cases hzero : segment.1 = 0
    · have hinl :
          (Sum.inl (xStarEdgeStart P x ⟨Sum.inr edge, edgeMember⟩) :
            SubdivisionVertex P x S) =
          Sum.inl ⟨Vertex.q q, by
            simpa [xStarBoundaryVertexMember, xStarVertexMember]
              using oldMember⟩ := by
        simpa [tannerDoubleCylinderEdgeStart, subdivisionEdgeStart,
          subdivisionSegmentStart, hzero] using hsubdivision
      have hraw := congrArg Subtype.val (Sum.inl.inj hinl)
      have hq : edge.1.1 = q := Vertex.q.inj hraw
      have hsegment : segment = rxRadialGridZero S := by
        apply Fin.ext
        simpa [rxRadialGridZero] using hzero
      subst segment
      refine ⟨hq, ?_⟩
      exact (rxOriginalBoundaryQRectangleQ0
        P S x copy edge edgeMember).symm
    · have himpossible :
          (Sum.inr (Sum.inl
            (⟨Sum.inr edge, edgeMember⟩,
              ⟨segment.1 - 1, by have := segment.2; omega⟩)) :
              SubdivisionVertex P x S) =
            Sum.inl ⟨Vertex.q q, by
              simpa [xStarBoundaryVertexMember, xStarVertexMember]
                using oldMember⟩ := by
        simpa [tannerDoubleCylinderEdgeStart, subdivisionEdgeStart,
          subdivisionSegmentStart, hzero] using hsubdivision
      cases himpossible
  · have hsubdivision := congrArg Prod.snd hend
    by_cases hlast : segment.1 + 1 = S.half
    · have hinl :
          (Sum.inl (xStarEdgeEnd P x ⟨Sum.inr edge, edgeMember⟩) :
            SubdivisionVertex P x S) =
          Sum.inl ⟨Vertex.q q, by
            simpa [xStarBoundaryVertexMember, xStarVertexMember]
              using oldMember⟩ := by
        simpa [tannerDoubleCylinderEdgeEnd, subdivisionEdgeEnd,
          subdivisionSegmentEnd, hlast] using hsubdivision
      have hraw := congrArg Subtype.val (Sum.inl.inj hinl)
      change Vertex.z edge.1.2 = Vertex.q q at hraw
      cases hraw
    · have himpossible :
          (Sum.inr (Sum.inl
            (⟨Sum.inr edge, edgeMember⟩,
              ⟨segment.1, by have := segment.2; omega⟩)) :
              SubdivisionVertex P x S) =
            Sum.inl ⟨Vertex.q q, by
              simpa [xStarBoundaryVertexMember, xStarVertexMember]
                using oldMember⟩ := by
        simpa [tannerDoubleCylinderEdgeEnd, subdivisionEdgeEnd,
          subdivisionSegmentEnd, hlast] using hsubdivision
      cases himpossible
noncomputable def rxOriginalBoundaryQRawRectangleQPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (candidateX : P.X) (candidateCopy : Two) (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P candidateX (Sum.inr edge) = true)
    (segment : Fin S.half)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q oldMember)
      (Vertex.q (Sum.inl ⟨candidateX,
        Sum.inl (candidateCopy,
          Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment))⟩)) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      (rxReplacementXBoundaryRoot P
        A4.toTannerSquareAdmissibleV3 S
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      ⟨Vertex.q (Sum.inl ⟨candidateX,
        Sum.inl (candidateCopy,
          Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment))⟩), member⟩ := by
  obtain ⟨howner, hnormalize⟩ :=
    rxOriginalBoundaryQRawRectangleQ_normalize
      P S x copy q oldMember candidateX candidateCopy
        edge edgeMember segment member
  subst candidateX
  obtain ⟨hq, hraw⟩ := hnormalize rfl
  let target : RXOriginalBoundaryQTarget P x q :=
    .constructor (.rectangleQ edge edgeMember hq 0)
  let path := rxOriginalBoundaryQTargetBoundaryPathHistorical
    P A4 S x copy q oldMember target
  have htarget : rxOriginalBoundaryQTargetBoundaryVertex
        P A4 S x copy q oldMember target =
      ⟨Vertex.q (Sum.inl ⟨x,
        Sum.inl (candidateCopy,
          Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment))⟩), member⟩ := by
    apply Subtype.ext
    exact congrArg Vertex.q hraw.symm
  exact htarget ▸ path
theorem rxOriginalBoundaryQRawVerticalQ_normalize
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (candidateX : P.X)
    (boundaryVertex : SubdivisionBoundaryVertex P candidateX S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q oldMember)
      (Vertex.q (Sum.inl ⟨candidateX, Sum.inr boundaryVertex⟩)) = true) :
    candidateX = x ∧
      ∀ howner : candidateX = x,
        (Sum.inl ⟨candidateX, Sum.inr boundaryVertex⟩ : RX1 P S) =
          localFaceQAt P S
            (rxOriginalBoundaryQRootLocalFace
              P A4 S x copy q oldMember) 1 := by
  obtain ⟨howner, hendpoint⟩ := rxOriginalBoundaryQRawLocalQ_endpoint
    P S x copy q oldMember candidateX (Sum.inr boundaryVertex) member
  subst candidateX
  refine ⟨rfl, ?_⟩
  intro howner'
  have hproof : howner' = (rfl : x = x) := Subsingleton.elim _ _
  cases hproof
  have hvertex : boundaryVertex =
      subdivisionOriginalBoundaryVertex P x S ⟨Vertex.q q, oldMember⟩ := by
    rcases hendpoint rfl with hstart | hend
    · have hraw := congrArg Prod.snd hstart
      apply Subtype.ext
      simpa [tannerDoubleCylinderEdgeStart,
        subdivisionOriginalBoundaryVertex, xStarBoundaryVertexToStar] using hraw
    · have hraw := congrArg Prod.snd hend
      apply Subtype.ext
      simpa [tannerDoubleCylinderEdgeEnd,
        subdivisionOriginalBoundaryVertex, xStarBoundaryVertexToStar] using hraw
  rw [hvertex]
  exact (rxOriginalBoundaryQRootRectangleQ1
    P A4 S x copy q oldMember).symm
noncomputable def rxOriginalBoundaryQRawVerticalQPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (candidateX : P.X)
    (boundaryVertex : SubdivisionBoundaryVertex P candidateX S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q oldMember)
      (Vertex.q (Sum.inl ⟨candidateX, Sum.inr boundaryVertex⟩)) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      (rxReplacementXBoundaryRoot P
        A4.toTannerSquareAdmissibleV3 S
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      ⟨Vertex.q (Sum.inl ⟨candidateX, Sum.inr boundaryVertex⟩), member⟩ := by
  obtain ⟨howner, hnormalize⟩ :=
    rxOriginalBoundaryQRawVerticalQ_normalize
      P A4 S x copy q oldMember candidateX boundaryVertex member
  subst candidateX
  have hraw := hnormalize rfl
  let owner := rxOriginalBoundaryQRootOwner P A4 x q oldMember
  let target : RXOriginalBoundaryQTarget P x q :=
    .constructor (.rectangleQ owner.1.edge owner.1.member owner.2 1)
  let path := rxOriginalBoundaryQTargetBoundaryPathHistorical
    P A4 S x copy q oldMember target
  have htarget : rxOriginalBoundaryQTargetBoundaryVertex
        P A4 S x copy q oldMember target =
      ⟨Vertex.q (Sum.inl ⟨x, Sum.inr boundaryVertex⟩), member⟩ := by
    apply Subtype.ext
    exact congrArg Vertex.q hraw.symm
  exact htarget ▸ path
theorem rxOriginalBoundaryQRawInteriorQ_false
    (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (copy : Two) (q : P.Q)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (candidateX : P.X) (candidateCopy : Two)
    (interior :
      (XStarFace P candidateX × Fin S.half × Fin (S.half - 1)) ⊕
        (XStarFace P candidateX × Fin (S.half - 1) × Fin S.half))
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q oldMember)
      (Vertex.q (Sum.inl ⟨candidateX,
        Sum.inl (candidateCopy, Sum.inr interior)⟩)) = true) : False := by
  obtain ⟨howner, hendpoint⟩ := rxOriginalBoundaryQRawLocalQ_endpoint
    P S x copy q oldMember candidateX
      (Sum.inl (candidateCopy, Sum.inr interior)) member
  subst candidateX
  rcases hendpoint rfl with hstart | hend
  · have hsubdivision := congrArg Prod.snd hstart
    rcases interior with horizontal | vertical
    · rcases horizontal with ⟨face, column, row⟩
      have hgrid : subdivisionGridVertex P x S face
          ⟨column.1, by have := column.2; omega⟩
          ⟨row.1 + 1, by have := row.2; omega⟩ =
          Sum.inl ⟨Vertex.q q, by
            simpa [xStarBoundaryVertexMember, xStarVertexMember]
              using oldMember⟩ := by
        simp only [tannerDoubleCylinderEdgeStart, subdivisionEdgeStart] at hsubdivision
        exact hsubdivision
      rcases subdivisionGridVertex_eq_originalQ_coordinates
          P S x face _ _ q _ hgrid with hq0 | hq1
      · have hcoordinate := hq0.1
        change column.1 = S.half at hcoordinate
        have := column.2
        omega
      · have hcoordinate := hq1.2.1
        change row.1 + 1 = S.half at hcoordinate
        have := row.2
        omega
    · rcases vertical with ⟨face, column, row⟩
      have hgrid : subdivisionGridVertex P x S face
          ⟨column.1 + 1, by have := column.2; omega⟩
          ⟨row.1, by have := row.2; omega⟩ =
          Sum.inl ⟨Vertex.q q, by
            simpa [xStarBoundaryVertexMember, xStarVertexMember]
              using oldMember⟩ := by
        simp only [tannerDoubleCylinderEdgeStart, subdivisionEdgeStart] at hsubdivision
        exact hsubdivision
      rcases subdivisionGridVertex_eq_originalQ_coordinates
          P S x face _ _ q _ hgrid with hq0 | hq1
      · have hcoordinate := hq0.1
        change column.1 + 1 = S.half at hcoordinate
        have := column.2
        omega
      · have hcoordinate := hq1.2.1
        change row.1 = S.half at hcoordinate
        have := row.2
        omega
  · have hsubdivision := congrArg Prod.snd hend
    rcases interior with horizontal | vertical
    · rcases horizontal with ⟨face, column, row⟩
      have hgrid : subdivisionGridVertex P x S face
          ⟨column.1 + 1, by have := column.2; omega⟩
          ⟨row.1 + 1, by have := row.2; omega⟩ =
          Sum.inl ⟨Vertex.q q, by
            simpa [xStarBoundaryVertexMember, xStarVertexMember]
              using oldMember⟩ := by
        simp only [tannerDoubleCylinderEdgeEnd, subdivisionEdgeEnd] at hsubdivision
        exact hsubdivision
      rcases subdivisionGridVertex_eq_originalQ_coordinates
          P S x face _ _ q _ hgrid with hq0 | hq1
      · have hcoordinate := hq0.2.1
        change row.1 + 1 = 0 at hcoordinate
        omega
      · have hcoordinate := hq1.1
        change column.1 + 1 = 0 at hcoordinate
        omega
    · rcases vertical with ⟨face, column, row⟩
      have hgrid : subdivisionGridVertex P x S face
          ⟨column.1 + 1, by have := column.2; omega⟩
          ⟨row.1 + 1, by have := row.2; omega⟩ =
          Sum.inl ⟨Vertex.q q, by
            simpa [xStarBoundaryVertexMember, xStarVertexMember]
              using oldMember⟩ := by
        simp only [tannerDoubleCylinderEdgeEnd, subdivisionEdgeEnd] at hsubdivision
        exact hsubdivision
      rcases subdivisionGridVertex_eq_originalQ_coordinates
          P S x face _ _ q _ hgrid with hq0 | hq1
      · have hcoordinate := hq0.2.1
        change row.1 + 1 = 0 at hcoordinate
        omega
      · have hcoordinate := hq1.1
        change column.1 + 1 = 0 at hcoordinate
        omega
noncomputable def rxOriginalBoundaryQRawLocalQPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (candidateX : P.X) (edge : DoubleCylinderEdge P candidateX S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q oldMember)
      (Vertex.q (Sum.inl ⟨candidateX, edge⟩)) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      (rxReplacementXBoundaryRoot P
        A4.toTannerSquareAdmissibleV3 S
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      ⟨Vertex.q (Sum.inl ⟨candidateX, edge⟩), member⟩ := by
  rcases edge with copied | boundaryVertex
  · rcases copied with ⟨candidateCopy, subdivisionEdge⟩
    rcases subdivisionEdge with original | interior
    · rcases original with ⟨starEdge, segment⟩
      rcases starEdge with ⟨rawEdge, edgeMember⟩
      rcases rawEdge with xqEdge | qzEdge
      · exact rxOriginalBoundaryQRawRadialQPath
          P A4 S x copy q oldMember candidateX candidateCopy
            xqEdge edgeMember segment member
      · exact rxOriginalBoundaryQRawRectangleQPath
          P A4 S x copy q oldMember candidateX candidateCopy
            qzEdge edgeMember segment member
    · exact False.elim (rxOriginalBoundaryQRawInteriorQ_false
        P S x copy q oldMember candidateX candidateCopy interior member)
  · exact rxOriginalBoundaryQRawVerticalQPath
      P A4 S x copy q oldMember candidateX boundaryVertex member
noncomputable def rxOriginalBoundaryQRootQStarEdge
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (x : P.X) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    QStarEdge P q := by
  let owner := rxOriginalBoundaryQRootOwner P A4 x q member
  refine ⟨owner.1.edge.1.2, ?_⟩
  simpa [owner.2] using owner.1.edge.2
theorem rxOriginalBoundaryQRootGlueQ1
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    glueFaceQ1 P S
        (rxOriginalBoundaryQGlueFaceAt P S x copy q member
          (rxOriginalBoundaryQRootQStarEdge P A4 x q member)) =
      Sum.inr ⟨q, (copy, Sum.inl (Sum.inl ()))⟩ := by
  simp [rxOriginalBoundaryQGlueFaceAt, glueFaceQ1, edgeEndpoint,
    qDoubleCylinderEdgeStart, qSubdivisionEdgeStart,
    rxRadialGridZero, qStarEdgeStart]
def rxOriginalBoundaryQRawCenterData
    (P : TannerSquarePresentation) (S : OddScale) :
    RX1 P S → Option (P.Q × Two)
  | Sum.inr ⟨ownerQ, (ownerCopy, Sum.inl (Sum.inl _))⟩ =>
      some (ownerQ, ownerCopy)
  | _ => none
theorem rxOriginalBoundaryQRawCenterQ_normalize
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (candidateQ : P.Q) (candidateCopy : Two)
    (center : Unit)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q oldMember)
      (Vertex.q (Sum.inr
        ⟨candidateQ, (candidateCopy, Sum.inl (Sum.inl center))⟩)) = true) :
    candidateQ = q ∧ candidateCopy = copy ∧
      (Sum.inr
        ⟨candidateQ, (candidateCopy, Sum.inl (Sum.inl center))⟩ : RX1 P S) =
        glueFaceQ1 P S
          (rxOriginalBoundaryQGlueFaceAt P S x copy q oldMember
            (rxOriginalBoundaryQRootQStarEdge P A4 x q oldMember)) := by
  classical
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceQ = rxFaceQ P S from rfl]
    at member
  rw [decide_eq_true_eq] at member
  obtain ⟨candidate, hx, hqTag⟩ := member
  have hx' : rxFaceX P S candidate =
      rxOriginalBoundaryQXCoordinate P S x copy q oldMember := by
    simp only [xStarFaceMember, decide_eq_true_eq] at hx
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
    exact hx
  rcases candidate with candidateLocal | candidateGlue | candidateOld
  · rcases hqTag with hqTag | hqTag <;> cases hqTag
  · rcases candidateGlue with ⟨a, qEdge, endpoint⟩
    rcases hqTag with hqTag | hqTag
    · cases hqTag
    · obtain ⟨targetEdge, hcandidate⟩ :=
        rxOriginalBoundaryQGlueFace_cases P S x copy q oldMember
          ⟨a, qEdge, endpoint⟩ (by simpa [rxFaceX] using hx')
      have hraw :
          (Sum.inr
            ⟨candidateQ, (candidateCopy, Sum.inl (Sum.inl center))⟩ :
              RX1 P S) =
            glueFaceQ1 P S
              (rxOriginalBoundaryQGlueFaceAt
                P S x copy q oldMember targetEdge) :=
        hqTag.trans (congrArg (glueFaceQ1 P S) hcandidate)
      have hdata : (candidateQ, candidateCopy) = (q, copy) := by
        simpa [rxOriginalBoundaryQRawCenterData,
          rxOriginalBoundaryQGlueFaceAt, glueFaceQ1, edgeEndpoint,
          qDoubleCylinderEdgeStart, qSubdivisionEdgeStart,
          rxRadialGridZero, qStarEdgeStart] using
            congrArg (rxOriginalBoundaryQRawCenterData P S) hraw
      have hq : candidateQ = q := congrArg Prod.fst hdata
      have hcopy : candidateCopy = copy := congrArg Prod.snd hdata
      subst candidateQ
      subst candidateCopy
      rcases center with ⟨⟩
      refine ⟨rfl, rfl, ?_⟩
      exact (rxOriginalBoundaryQRootGlueQ1
        P A4 S x copy q oldMember).symm
  · rcases candidateOld with ⟨oldFace, oldCopy⟩
    have howner : P.faceX oldFace = x := congrArg Sigma.fst hx'
    subst x
    have hvertex :
        (oldCopy, Sum.inl
          (xStarFaceZVertex P (P.faceX oldFace) (oldFaceInXStar P oldFace))) =
        (copy, Sum.inl ⟨Vertex.q q, by
          simpa [xStarBoundaryVertexMember, xStarVertexMember]
            using oldMember⟩) :=
      eq_of_heq (Sigma.mk.inj_iff.mp hx').2
    have hinl := Sum.inl.inj (congrArg Prod.snd hvertex)
    have hraw := congrArg Subtype.val hinl
    change Vertex.z (P.faceZ oldFace) = Vertex.q q at hraw
    cases hraw
noncomputable def rxOriginalBoundaryQRawCenterQPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (candidateQ : P.Q) (candidateCopy : Two) (center : Unit)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q oldMember)
      (Vertex.q (Sum.inr
        ⟨candidateQ, (candidateCopy, Sum.inl (Sum.inl center))⟩)) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      (rxReplacementXBoundaryRoot P
        A4.toTannerSquareAdmissibleV3 S
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      ⟨Vertex.q (Sum.inr
        ⟨candidateQ, (candidateCopy, Sum.inl (Sum.inl center))⟩),
        member⟩ := by
  obtain ⟨hq, hcopy, hraw⟩ := rxOriginalBoundaryQRawCenterQ_normalize
    P A4 S x copy q oldMember candidateQ candidateCopy center member
  subst candidateQ
  subst candidateCopy
  rcases center with ⟨⟩
  let edge := rxOriginalBoundaryQRootQStarEdge P A4 x q oldMember
  let target : RXOriginalBoundaryQTarget P x q :=
    .glue (.q edge 1)
  let path := rxOriginalBoundaryQTargetBoundaryPathHistorical
    P A4 S x copy q oldMember target
  have htarget : rxOriginalBoundaryQTargetBoundaryVertex
        P A4 S x copy q oldMember target =
      ⟨Vertex.q (Sum.inr
        ⟨q, (copy, Sum.inl (Sum.inl ()))⟩), member⟩ := by
    apply Subtype.ext
    exact congrArg Vertex.q hraw.symm
  exact htarget ▸ path
def rxOriginalBoundaryQQCenterTag
    (P : TannerSquarePresentation) (S : OddScale) : RX1 P S → Bool
  | Sum.inr ⟨_, (_, Sum.inl (Sum.inl _))⟩ => true
  | _ => false
theorem rxOriginalBoundaryQRawQCenterTag_true
    (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (copy : Two) (q : P.Q)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (newQ : Σ q : P.Q, QDoubleCylinderVertex P q S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q oldMember)
      (Vertex.q (Sum.inr newQ)) = true) :
    rxOriginalBoundaryQQCenterTag P S (Sum.inr newQ) = true := by
  classical
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceQ = rxFaceQ P S from rfl]
    at member
  rw [decide_eq_true_eq] at member
  obtain ⟨candidate, hx, hqTag⟩ := member
  have hx' : rxFaceX P S candidate =
      rxOriginalBoundaryQXCoordinate P S x copy q oldMember := by
    simp only [xStarFaceMember, decide_eq_true_eq] at hx
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
    exact hx
  rcases candidate with candidateLocal | candidateGlue | candidateOld
  · rcases hqTag with hqTag | hqTag <;> cases hqTag
  · rcases candidateGlue with ⟨a, qEdge, endpoint⟩
    rcases hqTag with hqTag | hqTag
    · cases hqTag
    · obtain ⟨targetEdge, hcandidate⟩ :=
        rxOriginalBoundaryQGlueFace_cases P S x copy q oldMember
          ⟨a, qEdge, endpoint⟩ (by simpa [rxFaceX] using hx')
      change Sum.inr newQ = glueFaceQ1 P S
        ⟨a, qEdge, endpoint⟩ at hqTag
      rw [congrArg (glueFaceQ1 P S) hcandidate] at hqTag
      rw [hqTag]
      simp [rxOriginalBoundaryQQCenterTag,
        rxOriginalBoundaryQGlueFaceAt, glueFaceQ1, edgeEndpoint,
        qDoubleCylinderEdgeStart, qSubdivisionEdgeStart,
        rxRadialGridZero, qStarEdgeStart]
  · rcases candidateOld with ⟨oldFace, oldCopy⟩
    have howner : P.faceX oldFace = x := congrArg Sigma.fst hx'
    subst x
    have hvertex :
        (oldCopy, Sum.inl
          (xStarFaceZVertex P (P.faceX oldFace) (oldFaceInXStar P oldFace))) =
        (copy, Sum.inl ⟨Vertex.q q, by
          simpa [xStarBoundaryVertexMember, xStarVertexMember]
            using oldMember⟩) :=
      eq_of_heq (Sigma.mk.inj_iff.mp hx').2
    have hinl := Sum.inl.inj (congrArg Prod.snd hvertex)
    have hraw := congrArg Subtype.val hinl
    change Vertex.z (P.faceZ oldFace) = Vertex.q q at hraw
    cases hraw
noncomputable def rxOriginalBoundaryQRawQPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (newQ : RX1 P S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q oldMember)
      (Vertex.q newQ) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      (rxReplacementXBoundaryRoot P
        A4.toTannerSquareAdmissibleV3 S
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      ⟨Vertex.q newQ, member⟩ := by
  rcases newQ with localEdge | qVertex
  · rcases localEdge with ⟨candidateX, edge⟩
    exact rxOriginalBoundaryQRawLocalQPath
      P A4 S x copy q oldMember candidateX edge member
  · rcases qVertex with ⟨candidateQ, candidateCopy, subdivisionVertex⟩
    rcases subdivisionVertex with oldVertex | interior
    · rcases oldVertex with center | edge
      · exact rxOriginalBoundaryQRawCenterQPath
          P A4 S x copy q oldMember
            candidateQ candidateCopy center member
      · have himpossible := rxOriginalBoundaryQRawQCenterTag_true
          P S x copy q oldMember
            ⟨candidateQ, (candidateCopy, Sum.inl (Sum.inr edge))⟩ member
        simp [rxOriginalBoundaryQQCenterTag] at himpossible
    · have himpossible := rxOriginalBoundaryQRawQCenterTag_true
        P S x copy q oldMember
          ⟨candidateQ, (candidateCopy, Sum.inr interior)⟩ member
      simp [rxOriginalBoundaryQQCenterTag] at himpossible
noncomputable def rxReplacementXBoundaryPathOriginalQ
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (vertex : XStarBoundaryVertex (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q oldMember)) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      (rxReplacementXBoundaryRoot P
        A4.toTannerSquareAdmissibleV3 S
        (rxOriginalBoundaryQXCoordinate P S x copy q oldMember))
      vertex := by
  rcases vertex with ⟨value, member⟩
  rcases value with newX | newQ | newZ
  · simp [xStarBoundaryVertexMember] at member
  · exact rxOriginalBoundaryQRawQPath
      P A4 S x copy q oldMember newQ member
  · exact rxOriginalBoundaryQRawZPath
      P A4 S x copy q oldMember newZ member
noncomputable def rxOriginalBoundaryZRootBoundaryEdge
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (x : P.X) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true) :
    XStarBoundaryEdge P x :=
  rxStarEdgeInteriorBoundaryEdge P x
    (rxOriginalBoundaryZRootOwner P A4 x z member).1.edge
    (rxOriginalBoundaryZRootOwner P A4 x z member).1.member
noncomputable def rxOriginalBoundaryZRootRectangle
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true) :
    SubdivisionBoundaryEdge P x S :=
  subdivisionOriginalBoundaryEdge P x S
    (rxOriginalBoundaryZRootBoundaryEdge P A4 x z member)
    (rxStarEdgeInteriorLastIndex S)
noncomputable def rxOriginalBoundaryZRootLocalFace
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true) :
    RXLocalFace P S :=
  ⟨x, Sum.inr (rxOriginalBoundaryZRootRectangle P A4 S x z member),
    (copy, 1)⟩
theorem rxOriginalBoundaryZRootLocalFace_x
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true) :
    localFaceX P S
        (rxOriginalBoundaryZRootLocalFace P A4 S x copy z member) =
      rxOriginalBoundaryZXCoordinate P S x copy z member := by
  have hlast : S.half - 1 + 1 = S.half := by
    have := S.half_pos
    omega
  simp [rxOriginalBoundaryZRootLocalFace,
    rxOriginalBoundaryZRootRectangle,
    rxOriginalBoundaryZRootBoundaryEdge,
    rxStarEdgeInteriorBoundaryEdge,
    subdivisionOriginalBoundaryEdge, localFaceX,
    doubleCylinderRectangleCorner, subdivisionBoundaryEdgeEnd,
    subdivisionEdgeEnd, subdivisionSegmentEnd,
    rxStarEdgeInteriorLastIndex, hlast]
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Prod.ext
    · rfl
    · apply congrArg Sum.inl
      apply Subtype.ext
      change Vertex.z
          (rxOriginalBoundaryZRootOwner P A4 x z member).1.edge.1.2 =
        Vertex.z z
      exact congrArg Vertex.z
        (rxOriginalBoundaryZRootOwner P A4 x z member).2
noncomputable def rxOriginalBoundaryZRootXStarFace
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true) :
    XStarFace (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z member) :=
  ⟨Sum.inl (rxOriginalBoundaryZRootLocalFace
      P A4 S x copy z member), by
    simp only [xStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    exact rxOriginalBoundaryZRootLocalFace_x P A4 S x copy z member⟩
noncomputable def rxOriginalBoundaryZLocalFaceAt
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (face : XStarFace P x) : RXLocalFace P S :=
  ⟨x, Sum.inl (copy, (face, rxStarEdgeInteriorLastIndex S,
    rxStarEdgeInteriorLastIndex S)), (1, 1)⟩
theorem rxOriginalBoundaryZLocalFaceAt_x
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (face : XStarFace P x) (hz : P.faceZ face.1 = z) :
    localFaceX P S (rxOriginalBoundaryZLocalFaceAt P S x copy face) =
      rxOriginalBoundaryZXCoordinate P S x copy z member := by
  have hlast : S.half - 1 + 1 = S.half := by
    have := S.half_pos
    omega
  simp [rxOriginalBoundaryZLocalFaceAt, localFaceX, gridEndpoint,
    upperGridIndex, rxStarEdgeInteriorLastIndex, hlast,
    subdivisionGridVertex, Nat.ne_of_gt S.half_pos,
    rxOriginalBoundaryZXCoordinate]
  apply Subtype.ext
  exact congrArg Vertex.z hz
noncomputable def rxOriginalBoundaryZOwnerLocalFace
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true) :
    RXLocalFace P S :=
  rxOriginalBoundaryZLocalFaceAt P S x copy
    (rxOriginalBoundaryZRootFace P A4 x z member)
theorem rxOriginalBoundaryZOwnerLocalFace_x
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true) :
    localFaceX P S
        (rxOriginalBoundaryZOwnerLocalFace P A4 S x copy z member) =
      rxOriginalBoundaryZXCoordinate P S x copy z member :=
  rxOriginalBoundaryZLocalFaceAt_x P S x copy z member _
    (rxOriginalBoundaryZRootFace_z P A4 x z member)
noncomputable def rxOriginalBoundaryZOwnerXStarFace
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true) :
    XStarFace (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z member) :=
  ⟨Sum.inl (rxOriginalBoundaryZOwnerLocalFace
      P A4 S x copy z member), by
    simp only [xStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    exact rxOriginalBoundaryZOwnerLocalFace_x P A4 S x copy z member⟩
theorem rxOriginalBoundaryZRootRectangleQ0
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true) :
    localFaceQAt P S
        (rxOriginalBoundaryZRootLocalFace P A4 S x copy z member) 0 =
      Sum.inl ⟨x, Sum.inl (copy, Sum.inl
        (⟨Sum.inr
          (rxOriginalBoundaryZRootOwner P A4 x z member).1.edge,
          (rxOriginalBoundaryZRootOwner P A4 x z member).1.member⟩,
          rxStarEdgeInteriorLastIndex S))⟩ := by
  simp [rxOriginalBoundaryZRootLocalFace, localFaceQAt,
    localFaceQ0, localFaceQ0Edge, localFaceQ0EdgeAt,
    rxOriginalBoundaryZRootRectangle,
    rxOriginalBoundaryZRootBoundaryEdge,
    rxStarEdgeInteriorBoundaryEdge, subdivisionOriginalBoundaryEdge]
  apply Subtype.ext
  rfl
theorem rxOriginalBoundaryZRootRectangleQ1
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true) :
    localFaceQAt P S
        (rxOriginalBoundaryZRootLocalFace P A4 S x copy z member) 1 =
      Sum.inl ⟨x, Sum.inr
        (subdivisionOriginalBoundaryVertex P x S ⟨Vertex.z z, member⟩)⟩ := by
  have hlast : S.half - 1 + 1 = S.half := by
    have := S.half_pos
    omega
  simp [rxOriginalBoundaryZRootLocalFace, localFaceQAt,
    localFaceQ1, localFaceQ1Edge, localFaceQ1EdgeAt,
    rxOriginalBoundaryZRootRectangle,
    rxOriginalBoundaryZRootBoundaryEdge,
    rxStarEdgeInteriorBoundaryEdge, subdivisionOriginalBoundaryEdge,
    subdivisionBoundaryEdgeEnd, subdivisionEdgeEnd,
    subdivisionSegmentEnd, rxStarEdgeInteriorLastIndex, hlast]
  congr 4
  apply Subtype.ext
  change Vertex.z
      (rxOriginalBoundaryZRootOwner P A4 x z member).1.edge.1.2 = Vertex.z z
  exact congrArg Vertex.z
    (rxOriginalBoundaryZRootOwner P A4 x z member).2
theorem rxOriginalBoundaryZLocalFaceAtBoundaryQ
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (face : XStarFace P x) (corner : Two) (edge : XStarEdge P x)
    (hedge : xStarFaceQZEdge P x face corner = edge) :
    localFaceQAt P S
        (rxOriginalBoundaryZLocalFaceAt P S x copy face)
        (flipEndpoint corner) =
      Sum.inl ⟨x, Sum.inl (copy, Sum.inl
        (edge, rxStarEdgeInteriorLastIndex S))⟩ := by
  have hlast : S.half - 1 + 1 = S.half := by
    have := S.half_pos
    omega
  fin_cases corner
  · simp [rxOriginalBoundaryZLocalFaceAt, flipEndpoint,
      localFaceQAt, localFaceQ1, localFaceQ1Edge, localFaceQ1EdgeAt,
      subdivisionFaceBoundaryEdge_one_one,
      subdivisionVerticalEdge, rxStarEdgeInteriorLastIndex,
      hlast] at hedge ⊢
    split <;> rename_i hzero
    · have hzeroValue := congrArg Fin.val hzero
      change S.half - 1 + 1 = 0 at hzeroValue
      omega
    · split <;> rename_i hboundary
      · exact congrArg (fun selected : XStarEdge P x =>
          (Sum.inl ⟨x, Sum.inl (copy, Sum.inl
            (selected, rxStarEdgeInteriorLastIndex S))⟩ : RX1 P S)) hedge
      · exfalso
        apply hboundary
        exact hlast
  · simp [rxOriginalBoundaryZLocalFaceAt, flipEndpoint,
      localFaceQAt, localFaceQ0, localFaceQ0Edge, localFaceQ0EdgeAt,
      subdivisionFaceBoundaryEdge_zero_one,
      subdivisionHorizontalEdge, rxStarEdgeInteriorLastIndex,
      hlast] at hedge ⊢
    split <;> rename_i hzero
    · have hzeroValue := congrArg Fin.val hzero
      change S.half - 1 + 1 = 0 at hzeroValue
      omega
    · split <;> rename_i hboundary
      · exact congrArg (fun selected : XStarEdge P x =>
          (Sum.inl ⟨x, Sum.inl (copy, Sum.inl
            (selected, rxStarEdgeInteriorLastIndex S))⟩ : RX1 P S)) hedge
      · exfalso
        apply hboundary
        exact hlast
theorem rxOriginalBoundaryZOwnerBoundaryQ
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true) :
    localFaceQAt P S
        (rxOriginalBoundaryZOwnerLocalFace P A4 S x copy z member)
        (flipEndpoint (rxOriginalBoundaryZRootCorner P A4 x z member)) =
      localFaceQAt P S
        (rxOriginalBoundaryZRootLocalFace P A4 S x copy z member) 0 := by
  exact (rxOriginalBoundaryZLocalFaceAtBoundaryQ P S x copy
    (rxOriginalBoundaryZRootFace P A4 x z member)
    (rxOriginalBoundaryZRootCorner P A4 x z member)
    ⟨Sum.inr (rxOriginalBoundaryZRootOwner P A4 x z member).1.edge,
      (rxOriginalBoundaryZRootOwner P A4 x z member).1.member⟩
    (rxOriginalBoundaryZRootOwner P A4 x z member).1.edgeExact).trans
    (rxOriginalBoundaryZRootRectangleQ0 P A4 S x copy z member).symm
theorem rxOriginalBoundaryZOwnerBoundaryVertexEq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true) :
    xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z member)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxOriginalBoundaryZXCoordinate P S x copy z member)
          (rxOriginalBoundaryZOwnerXStarFace P A4 S x copy z member)
          (flipEndpoint (rxOriginalBoundaryZRootCorner P A4 x z member))) =
      xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z member)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxOriginalBoundaryZXCoordinate P S x copy z member)
          (rxOriginalBoundaryZRootXStarFace P A4 S x copy z member) 0) := by
  apply Subtype.ext
  exact congrArg Vertex.q
    (rxOriginalBoundaryZOwnerBoundaryQ P A4 S x copy z member)
noncomputable def rxOriginalBoundaryZRootBoundaryPathToQ
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (corner : Two) :=
  xStarFaceBoundaryPathToQ (rxReplacementPresentation P S)
    (rxOriginalBoundaryZXCoordinate P S x copy z member)
    (rxOriginalBoundaryZRootXStarFace P A4 S x copy z member) corner
noncomputable def rxOriginalBoundaryZRootBoundaryPathToZ
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true) :=
  (rxOriginalBoundaryZRootBoundaryPathToQ
    P A4 S x copy z member 0).append
    (xStarFaceBoundaryPathToZ _ _
      (rxOriginalBoundaryZRootXStarFace P A4 S x copy z member))
def rxOriginalBoundaryZRectangleLocalFaceAt
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true) :
    RXLocalFace P S :=
  ⟨x, Sum.inr (subdivisionOriginalBoundaryEdge P x S
    (rxStarEdgeInteriorBoundaryEdge P x edge edgeMember)
    (rxStarEdgeInteriorLastIndex S)), (copy, 1)⟩
theorem rxOriginalBoundaryZRectangleLocalFaceAt_x
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (hz : edge.1.2 = z) :
    localFaceX P S (rxOriginalBoundaryZRectangleLocalFaceAt
        P S x copy edge edgeMember) =
      rxOriginalBoundaryZXCoordinate P S x copy z member := by
  have hlast : S.half - 1 + 1 = S.half := by
    have := S.half_pos
    omega
  simp [rxOriginalBoundaryZRectangleLocalFaceAt,
    rxStarEdgeInteriorBoundaryEdge, subdivisionOriginalBoundaryEdge,
    localFaceX, doubleCylinderRectangleCorner,
    subdivisionBoundaryEdgeEnd, subdivisionEdgeEnd,
    subdivisionSegmentEnd, rxStarEdgeInteriorLastIndex, hlast]
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Prod.ext
    · rfl
    · apply congrArg Sum.inl
      apply Subtype.ext
      exact congrArg Vertex.z hz
def rxOriginalBoundaryZRectangleXStarFaceAt
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (hz : edge.1.2 = z) :
    XStarFace (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z member) :=
  ⟨Sum.inl (rxOriginalBoundaryZRectangleLocalFaceAt
      P S x copy edge edgeMember), by
    simp only [xStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    exact rxOriginalBoundaryZRectangleLocalFaceAt_x
      P S x copy z member edge edgeMember hz⟩
theorem rxOriginalBoundaryZRectangleVerticalQ
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (hz : edge.1.2 = z) :
    localFaceQAt P S (rxOriginalBoundaryZRectangleLocalFaceAt
        P S x copy edge edgeMember) 1 =
      Sum.inl ⟨x, Sum.inr
        (subdivisionOriginalBoundaryVertex P x S ⟨Vertex.z z, member⟩)⟩ := by
  have hlast : S.half - 1 + 1 = S.half := by
    have := S.half_pos
    omega
  simp [rxOriginalBoundaryZRectangleLocalFaceAt,
    localFaceQAt, localFaceQ1, localFaceQ1Edge, localFaceQ1EdgeAt,
    rxStarEdgeInteriorBoundaryEdge, subdivisionOriginalBoundaryEdge,
    subdivisionBoundaryEdgeEnd, subdivisionEdgeEnd,
    subdivisionSegmentEnd, rxStarEdgeInteriorLastIndex, hlast]
  congr 4
  apply Subtype.ext
  exact congrArg Vertex.z hz
theorem rxOriginalBoundaryZRectangleVerticalBoundaryEq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (hz : edge.1.2 = z) :
    xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z member)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxOriginalBoundaryZXCoordinate P S x copy z member)
          (rxOriginalBoundaryZRootXStarFace P A4 S x copy z member) 1) =
      xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z member)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxOriginalBoundaryZXCoordinate P S x copy z member)
          (rxOriginalBoundaryZRectangleXStarFaceAt
            P S x copy z member edge edgeMember hz) 1) := by
  apply Subtype.ext
  exact congrArg Vertex.q
    ((rxOriginalBoundaryZRootRectangleQ1 P A4 S x copy z member).trans
      (rxOriginalBoundaryZRectangleVerticalQ
        P S x copy z member edge edgeMember hz).symm)
noncomputable def rxOriginalBoundaryZRectangleBoundaryPathToQAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (hz : edge.1.2 = z) (corner : Two) := by
  let first := rxOriginalBoundaryZRootBoundaryPathToQ
    P A4 S x copy z member 1
  let bridge := (xStarFaceBoundaryPathToQ (rxReplacementPresentation P S)
    (rxOriginalBoundaryZXCoordinate P S x copy z member)
    (rxOriginalBoundaryZRectangleXStarFaceAt
      P S x copy z member edge edgeMember hz) 1).reverse
  let last := xStarFaceBoundaryPathToQ (rxReplacementPresentation P S)
    (rxOriginalBoundaryZXCoordinate P S x copy z member)
    (rxOriginalBoundaryZRectangleXStarFaceAt
      P S x copy z member edge edgeMember hz) corner
  exact first.append
    (((rxOriginalBoundaryZRectangleVerticalBoundaryEq
      P A4 S x copy z member edge edgeMember hz).symm ▸ bridge).append last)
noncomputable def rxOriginalBoundaryZRectangleBoundaryPathToZAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (hz : edge.1.2 = z) :=
  (rxOriginalBoundaryZRectangleBoundaryPathToQAt
    P A4 S x copy z member edge edgeMember hz 0).append
    (xStarFaceBoundaryPathToZ _ _
      (rxOriginalBoundaryZRectangleXStarFaceAt
        P S x copy z member edge edgeMember hz))
def rxOriginalBoundaryZGlueFaceAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true) :
    RXXQGlueFace P S :=
  ⟨rxStarEdgeInteriorBoundaryXQEdge P A4 x edge edgeMember,
    Sum.inl (copy, (rxStarEdgeInteriorBoundaryQStarEdge P edge,
      rxStarEdgeInteriorLastIndex S)), 1⟩
theorem rxOriginalBoundaryZGlueFaceAt_x
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (hz : edge.1.2 = z) :
    glueFaceX P S (rxOriginalBoundaryZGlueFaceAt
        P A4 S x copy edge edgeMember) =
      rxOriginalBoundaryZXCoordinate P S x copy z member := by
  have hlast : S.half - 1 + 1 = S.half := by
    have := S.half_pos
    omega
  simp [rxOriginalBoundaryZGlueFaceAt,
    rxStarEdgeInteriorBoundaryXQEdge,
    rxStarEdgeInteriorBoundaryQStarEdge,
    glueFaceX, edgeEndpoint, qToXDoubleCylinderEdgeRaw,
    qToXSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge,
    tannerDoubleCylinderEdgeEnd, subdivisionEdgeEnd,
    subdivisionSegmentEnd, rxStarEdgeInteriorLastIndex, hlast,
    rxOriginalBoundaryZXCoordinate]
  apply Subtype.ext
  exact congrArg Vertex.z hz
def rxOriginalBoundaryZGlueXStarFaceAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (hz : edge.1.2 = z) :
    XStarFace (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z member) :=
  ⟨Sum.inr (Sum.inl (rxOriginalBoundaryZGlueFaceAt
      P A4 S x copy edge edgeMember)), by
    simp only [xStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    exact rxOriginalBoundaryZGlueFaceAt_x
      P A4 S x copy z member edge edgeMember hz⟩
theorem rxOriginalBoundaryZGlueQ0
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true) :
    glueFaceQ0 P S
        (rxOriginalBoundaryZGlueFaceAt P A4 S x copy edge edgeMember) =
      localFaceQAt P S
        (rxOriginalBoundaryZRectangleLocalFaceAt
          P S x copy edge edgeMember) 0 := by
  simp [rxOriginalBoundaryZGlueFaceAt, glueFaceQ0,
    rxOriginalBoundaryZRectangleLocalFaceAt, localFaceQAt,
    localFaceQ0, localFaceQ0Edge, localFaceQ0EdgeAt,
    subdivisionOriginalBoundaryEdge,
    doubleCylinderRectangleBoundaryEdge,
    qToXDoubleCylinderEdgeRaw, qToXSubdivisionBoundaryEdge,
    rxStarEdgeInteriorBoundaryEdge,
    rxStarEdgeInteriorBoundaryXQEdge,
    rxStarEdgeInteriorBoundaryQStarEdge,
    rxStarEdgeInteriorLastIndex]
  apply Subtype.ext
  rfl
theorem rxOriginalBoundaryZGlueBoundaryQEq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (hz : edge.1.2 = z) :
    xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z member)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxOriginalBoundaryZXCoordinate P S x copy z member)
          (rxOriginalBoundaryZRectangleXStarFaceAt
            P S x copy z member edge edgeMember hz) 0) =
      xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z member)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxOriginalBoundaryZXCoordinate P S x copy z member)
          (rxOriginalBoundaryZGlueXStarFaceAt
            P A4 S x copy z member edge edgeMember hz) 0) := by
  apply Subtype.ext
  apply congrArg Vertex.q
  exact (rxOriginalBoundaryZGlueQ0
    P A4 S x copy edge edgeMember).symm
noncomputable def rxOriginalBoundaryZGlueBoundaryPathToQAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (hz : edge.1.2 = z) (corner : Two) := by
  let first := rxOriginalBoundaryZRectangleBoundaryPathToQAt
    P A4 S x copy z member edge edgeMember hz 0
  let last := xStarFaceBoundaryPathToQ (rxReplacementPresentation P S)
    (rxOriginalBoundaryZXCoordinate P S x copy z member)
    (rxOriginalBoundaryZGlueXStarFaceAt
      P A4 S x copy z member edge edgeMember hz) corner
  exact first.append ((rxOriginalBoundaryZGlueBoundaryQEq
    P A4 S x copy z member edge edgeMember hz).symm ▸ last)
noncomputable def rxOriginalBoundaryZGlueBoundaryPathToZAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (hz : edge.1.2 = z) :=
  (rxOriginalBoundaryZGlueBoundaryPathToQAt
    P A4 S x copy z member edge edgeMember hz 0).append
    (xStarFaceBoundaryPathToZ _ _
      (rxOriginalBoundaryZGlueXStarFaceAt
        P A4 S x copy z member edge edgeMember hz))
def rxOriginalBoundaryZFaceEdge
    (P : TannerSquarePresentation) (x : P.X)
    (face : XStarFace P x) (corner : Two) : QZEdge P :=
  faceQZEdge P face.1 corner
theorem rxOriginalBoundaryZFaceEdge_member
    (P : TannerSquarePresentation) (x : P.X)
    (face : XStarFace P x) (corner : Two) :
    xStarEdgeMember P x
      (Sum.inr (rxOriginalBoundaryZFaceEdge P x face corner)) = true :=
  (xStarFaceQZEdge P x face corner).2
theorem rxOriginalBoundaryZFaceEdge_z
    (P : TannerSquarePresentation) (x : P.X) (z : P.Z)
    (face : XStarFace P x) (hz : P.faceZ face.1 = z)
    (corner : Two) :
    (rxOriginalBoundaryZFaceEdge P x face corner).1.2 = z := by
  exact hz
def rxOriginalBoundaryZOldFaceXStarFaceAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (face : XStarFace P x) (hz : P.faceZ face.1 = z) :
    XStarFace (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z member) :=
  let edge := rxOriginalBoundaryZFaceEdge P x face 0
  let edgeMember := rxOriginalBoundaryZFaceEdge_member P x face 0
  let edgeZ := rxOriginalBoundaryZFaceEdge_z P x z face hz 0
  let glue := rxOriginalBoundaryZGlueFaceAt
    P A4 S x copy edge edgeMember
  have hlast : S.half - 1 + 1 = S.half := by
    have := S.half_pos
    omega
  have hqz : P.qz edge.1.1 z = true := by
    rw [← edgeZ]
    exact edge.2
  have hqEndpoint :
      edgeEndpoint (qDoubleCylinderEdgeStart P edge.1.1 S)
          (qDoubleCylinderEdgeEnd P edge.1.1 S)
          (Sum.inl (copy, (rxStarEdgeInteriorBoundaryQStarEdge P edge,
            rxStarEdgeInteriorLastIndex S))) 1 =
        (copy, Sum.inl (Sum.inr
          (⟨z, hqz⟩ : QStarEdge P edge.1.1))) := by
    simp [edgeEndpoint, qDoubleCylinderEdgeEnd, qSubdivisionEdgeEnd,
      qStarEdgeEnd, rxStarEdgeInteriorLastIndex, hlast]
    apply Subtype.ext
    exact edgeZ
  have hglueOld : glueFaceX P S glue = oldZFaceX P S (face.1, copy) := by
    exact qToXDoubleCylinderEdgeRaw_endpoint_eq_oldZFaceX
      P S x edge.1.1 z
      (rxStarEdgeInteriorBoundaryQIncidence P A4 x edge edgeMember)
      hqz
      (Sum.inl (copy, (rxStarEdgeInteriorBoundaryQStarEdge P edge,
        rxStarEdgeInteriorLastIndex S))) 1 face.1 0 copy
      (by simpa [xStarFaceMember] using face.2) hz rfl
      hqEndpoint
  have hglueCoordinate : glueFaceX P S glue =
      rxOriginalBoundaryZXCoordinate P S x copy z member :=
    rxOriginalBoundaryZGlueFaceAt_x
      P A4 S x copy z member edge edgeMember edgeZ
  have holdCoordinate : oldZFaceX P S (face.1, copy) =
      rxOriginalBoundaryZXCoordinate P S x copy z member :=
    hglueOld.symm.trans hglueCoordinate
  ⟨Sum.inr (Sum.inr (face.1, copy)), by
    simp only [xStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    exact holdCoordinate⟩
theorem rxOriginalBoundaryZGlueQ1_eq_oldFaceQ
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (face : XStarFace P x) (hz : P.faceZ face.1 = z)
    (corner : Two) :
    glueFaceQ1 P S
        (rxOriginalBoundaryZGlueFaceAt P A4 S x copy
          (rxOriginalBoundaryZFaceEdge P x face corner)
          (rxOriginalBoundaryZFaceEdge_member P x face corner)) =
      oldZFaceQ P S corner (face.1, copy) := by
  have hlast : S.half - 1 + 1 = S.half := by
    have := S.half_pos
    omega
  simp [rxOriginalBoundaryZGlueFaceAt,
    rxOriginalBoundaryZFaceEdge,
    rxStarEdgeInteriorBoundaryQStarEdge,
    glueFaceQ1, edgeEndpoint, qDoubleCylinderEdgeEnd,
    qSubdivisionEdgeEnd, qStarEdgeEnd,
    rxStarEdgeInteriorLastIndex, hlast, oldZFaceQ]
  constructor
  · rfl
  · apply heq_of_eq
    rfl
theorem rxOriginalBoundaryZGlueOldFaceBoundaryQEq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (face : XStarFace P x) (hz : P.faceZ face.1 = z)
    (corner : Two) :
    xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z member)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxOriginalBoundaryZXCoordinate P S x copy z member)
          (rxOriginalBoundaryZGlueXStarFaceAt P A4 S x copy z member
            (rxOriginalBoundaryZFaceEdge P x face corner)
            (rxOriginalBoundaryZFaceEdge_member P x face corner)
            (rxOriginalBoundaryZFaceEdge_z P x z face hz corner)) 1) =
      xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z member)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxOriginalBoundaryZXCoordinate P S x copy z member)
          (rxOriginalBoundaryZOldFaceXStarFaceAt
            P A4 S x copy z member face hz) corner) := by
  apply Subtype.ext
  rw [xBoundaryEdgeStart_xStarFaceBoundaryEdge_value,
    xBoundaryEdgeStart_xStarFaceBoundaryEdge_value]
  change (Vertex.q (glueFaceQ1 P S
      (rxOriginalBoundaryZGlueFaceAt P A4 S x copy
        (rxOriginalBoundaryZFaceEdge P x face corner)
        (rxOriginalBoundaryZFaceEdge_member P x face corner))) :
      Vertex (rxReplacementPresentation P S)) =
    (Vertex.q (oldZFaceQ P S corner (face.1, copy)) :
      Vertex (rxReplacementPresentation P S))
  exact congrArg (fun qValue : RX1 P S =>
    (Vertex.q qValue : Vertex (rxReplacementPresentation P S)))
      (rxOriginalBoundaryZGlueQ1_eq_oldFaceQ
    P A4 S x copy z face hz corner)
noncomputable def rxOriginalBoundaryZOldFaceBoundaryPathToQAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (face : XStarFace P x) (hz : P.faceZ face.1 = z)
    (corner : Two) := by
  let first := rxOriginalBoundaryZGlueBoundaryPathToQAt
    P A4 S x copy z member
      (rxOriginalBoundaryZFaceEdge P x face corner)
      (rxOriginalBoundaryZFaceEdge_member P x face corner)
      (rxOriginalBoundaryZFaceEdge_z P x z face hz corner) 1
  exact rxOriginalBoundaryZGlueOldFaceBoundaryQEq
    P A4 S x copy z member face hz corner ▸ first
noncomputable def rxOriginalBoundaryZOldFaceBoundaryPathToZAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (face : XStarFace P x) (hz : P.faceZ face.1 = z) :=
  (rxOriginalBoundaryZOldFaceBoundaryPathToQAt
    P A4 S x copy z member face hz 0).append
    (xStarFaceBoundaryPathToZ _ _
      (rxOriginalBoundaryZOldFaceXStarFaceAt
        P A4 S x copy z member face hz))
theorem rxOriginalBoundaryZOldFace_cases
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (candidate : RXOldZFace P)
    (hx : oldZFaceX P S candidate =
      rxOriginalBoundaryZXCoordinate P S x copy z member) :
    candidate =
      ((rxOriginalBoundaryZRootFace P A4 x z member).1, copy) := by
  rcases candidate with ⟨face, candidateCopy⟩
  have howner : P.faceX face = x := congrArg Sigma.fst hx
  have hcopy : candidateCopy = copy :=
    congrArg (fun coordinate : RX0 P S => coordinate.2.1) hx
  have htag := congrArg (fun coordinate : RX0 P S =>
      match coordinate.2.2 with
      | Sum.inl vertex => some vertex.1
      | Sum.inr _ => none) hx
  have hfaceZ : P.faceZ face = z := by
    simp [oldZFaceX, rxOriginalBoundaryZXCoordinate,
      xStarFaceZVertex, oldFaceInXStar] at htag
    exact htag
  have hrootX :
      P.faceX (rxOriginalBoundaryZRootFace P A4 x z member).1 = x := by
    simpa [xStarFaceMember] using
      (rxOriginalBoundaryZRootFace P A4 x z member).2
  have hface : face =
      (rxOriginalBoundaryZRootFace P A4 x z member).1 := by
    apply R.faceXZ_injective
    exact Prod.ext (howner.trans hrootX.symm)
      (hfaceZ.trans
        (rxOriginalBoundaryZRootFace_z P A4 x z member).symm)
  exact Prod.ext hface hcopy
noncomputable def rxOriginalBoundaryZLocalXStarFaceAt
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (face : XStarFace P x) (hz : P.faceZ face.1 = z) :
    XStarFace (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z member) :=
  ⟨Sum.inl (rxOriginalBoundaryZLocalFaceAt P S x copy face), by
    simp only [xStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    exact rxOriginalBoundaryZLocalFaceAt_x
      P S x copy z member face hz⟩
theorem rxOriginalBoundaryZRectangleBoundaryQ0
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true) :
    localFaceQAt P S
        (rxOriginalBoundaryZRectangleLocalFaceAt
          P S x copy edge edgeMember) 0 =
      Sum.inl ⟨x, Sum.inl (copy, Sum.inl
        (⟨Sum.inr edge, edgeMember⟩, rxStarEdgeInteriorLastIndex S))⟩ := by
  simp [rxOriginalBoundaryZRectangleLocalFaceAt, localFaceQAt,
    localFaceQ0, localFaceQ0Edge, localFaceQ0EdgeAt,
    doubleCylinderRectangleBoundaryEdge,
    rxStarEdgeInteriorBoundaryEdge, subdivisionOriginalBoundaryEdge]
  apply Subtype.ext
  rfl
theorem rxOriginalBoundaryZRectangleLocalBoundaryQEq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (face : XStarFace P x) (hz : P.faceZ face.1 = z)
    (faceCorner : Two) :
    xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z member)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxOriginalBoundaryZXCoordinate P S x copy z member)
          (rxOriginalBoundaryZRectangleXStarFaceAt P S x copy z member
            (rxOriginalBoundaryZFaceEdge P x face faceCorner)
            (rxOriginalBoundaryZFaceEdge_member P x face faceCorner)
            (rxOriginalBoundaryZFaceEdge_z
              P x z face hz faceCorner)) 0) =
      xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z member)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxOriginalBoundaryZXCoordinate P S x copy z member)
          (rxOriginalBoundaryZLocalXStarFaceAt
            P S x copy z member face hz)
          (flipEndpoint faceCorner)) := by
  apply Subtype.ext
  rw [xBoundaryEdgeStart_xStarFaceBoundaryEdge_value,
    xBoundaryEdgeStart_xStarFaceBoundaryEdge_value]
  apply congrArg Vertex.q
  exact (rxOriginalBoundaryZRectangleBoundaryQ0 P S x copy
      (rxOriginalBoundaryZFaceEdge P x face faceCorner)
      (rxOriginalBoundaryZFaceEdge_member P x face faceCorner)).trans
    (rxOriginalBoundaryZLocalFaceAtBoundaryQ P S x copy face faceCorner
      (xStarFaceQZEdge P x face faceCorner) rfl).symm
noncomputable def rxOriginalBoundaryZLocalBoundaryPathToQAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (face : XStarFace P x) (hz : P.faceZ face.1 = z)
    (faceCorner targetCorner : Two) := by
  let first := rxOriginalBoundaryZRectangleBoundaryPathToQAt
    P A4 S x copy z member
      (rxOriginalBoundaryZFaceEdge P x face faceCorner)
      (rxOriginalBoundaryZFaceEdge_member P x face faceCorner)
      (rxOriginalBoundaryZFaceEdge_z P x z face hz faceCorner) 0
  let bridge := (xStarFaceBoundaryPathToQ
    (rxReplacementPresentation P S)
    (rxOriginalBoundaryZXCoordinate P S x copy z member)
    (rxOriginalBoundaryZLocalXStarFaceAt
      P S x copy z member face hz)
    (flipEndpoint faceCorner)).reverse
  let last := xStarFaceBoundaryPathToQ
    (rxReplacementPresentation P S)
    (rxOriginalBoundaryZXCoordinate P S x copy z member)
    (rxOriginalBoundaryZLocalXStarFaceAt
      P S x copy z member face hz) targetCorner
  exact first.append
    (((rxOriginalBoundaryZRectangleLocalBoundaryQEq
      P A4 S x copy z member face hz faceCorner).symm ▸ bridge).append last)
noncomputable def rxOriginalBoundaryZLocalBoundaryPathToZAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (face : XStarFace P x) (hz : P.faceZ face.1 = z)
    (faceCorner : Two) :=
  (rxOriginalBoundaryZLocalBoundaryPathToQAt
    P A4 S x copy z member face hz faceCorner 0).append
    (xStarFaceBoundaryPathToZ _ _
      (rxOriginalBoundaryZLocalXStarFaceAt
        P S x copy z member face hz))
def rxOriginalBoundaryZVerticalGlueFaceAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true) :
    RXXQGlueFace P S :=
  ⟨rxStarEdgeInteriorBoundaryXQEdge P A4 x edge edgeMember,
    Sum.inr (rxStarEdgeInteriorBoundaryQStarEdge P edge), copy⟩
theorem rxOriginalBoundaryZVerticalGlueFaceAt_x
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (hz : edge.1.2 = z) :
    glueFaceX P S (rxOriginalBoundaryZVerticalGlueFaceAt
        P A4 S x copy edge edgeMember) =
      rxOriginalBoundaryZXCoordinate P S x copy z member := by
  fin_cases copy <;> simp [rxOriginalBoundaryZVerticalGlueFaceAt,
    rxStarEdgeInteriorBoundaryXQEdge,
    rxStarEdgeInteriorBoundaryQStarEdge,
    glueFaceX, edgeEndpoint, qToXDoubleCylinderEdgeRaw,
    tannerDoubleCylinderEdgeStart, tannerDoubleCylinderEdgeEnd,
    subdivisionOriginalBoundaryVertex, qToXBoundaryEdge,
    rxOriginalBoundaryZXCoordinate, hz]
  all_goals apply Subtype.ext <;> rfl
def rxOriginalBoundaryZVerticalGlueXStarFaceAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (hz : edge.1.2 = z) :
    XStarFace (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z member) :=
  ⟨Sum.inr (Sum.inl (rxOriginalBoundaryZVerticalGlueFaceAt
      P A4 S x copy edge edgeMember)), by
    simp only [xStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    exact rxOriginalBoundaryZVerticalGlueFaceAt_x
      P A4 S x copy z member edge edgeMember hz⟩
theorem rxOriginalBoundaryZGlueVerticalQ1
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true) :
    glueFaceQ1 P S
        (rxOriginalBoundaryZGlueFaceAt P A4 S x copy edge edgeMember) =
      glueFaceQ1 P S
        (rxOriginalBoundaryZVerticalGlueFaceAt
          P A4 S x copy edge edgeMember) := by
  have hlast : S.half - 1 + 1 = S.half := by
    have := S.half_pos
    omega
  fin_cases copy <;> simp [rxOriginalBoundaryZGlueFaceAt,
    rxOriginalBoundaryZVerticalGlueFaceAt,
    rxStarEdgeInteriorBoundaryXQEdge,
    rxStarEdgeInteriorBoundaryQStarEdge,
    glueFaceQ1, edgeEndpoint, qDoubleCylinderEdgeStart,
    qDoubleCylinderEdgeEnd,
    qSubdivisionEdgeEnd, qStarEdgeEnd,
    rxStarEdgeInteriorLastIndex, hlast]
theorem rxOriginalBoundaryZGlueVerticalBoundaryQEq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (hz : edge.1.2 = z) :
    xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z member)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxOriginalBoundaryZXCoordinate P S x copy z member)
          (rxOriginalBoundaryZGlueXStarFaceAt
            P A4 S x copy z member edge edgeMember hz) 1) =
      xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z member)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxOriginalBoundaryZXCoordinate P S x copy z member)
          (rxOriginalBoundaryZVerticalGlueXStarFaceAt
            P A4 S x copy z member edge edgeMember hz) 1) := by
  apply Subtype.ext
  rw [xBoundaryEdgeStart_xStarFaceBoundaryEdge_value,
    xBoundaryEdgeStart_xStarFaceBoundaryEdge_value]
  exact congrArg Vertex.q
    (rxOriginalBoundaryZGlueVerticalQ1
      P A4 S x copy edge edgeMember)
noncomputable def rxOriginalBoundaryZVerticalGlueBoundaryPathToQAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (hz : edge.1.2 = z) (corner : Two) := by
  let first := rxOriginalBoundaryZGlueBoundaryPathToQAt
    P A4 S x copy z member edge edgeMember hz 1
  let bridge := (xStarFaceBoundaryPathToQ
    (rxReplacementPresentation P S)
    (rxOriginalBoundaryZXCoordinate P S x copy z member)
    (rxOriginalBoundaryZVerticalGlueXStarFaceAt
      P A4 S x copy z member edge edgeMember hz) 1).reverse
  let last := xStarFaceBoundaryPathToQ
    (rxReplacementPresentation P S)
    (rxOriginalBoundaryZXCoordinate P S x copy z member)
    (rxOriginalBoundaryZVerticalGlueXStarFaceAt
      P A4 S x copy z member edge edgeMember hz) corner
  exact first.append
    (((rxOriginalBoundaryZGlueVerticalBoundaryQEq
      P A4 S x copy z member edge edgeMember hz).symm ▸ bridge).append last)
noncomputable def rxOriginalBoundaryZVerticalGlueBoundaryPathToZAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (hz : edge.1.2 = z) :=
  (rxOriginalBoundaryZVerticalGlueBoundaryPathToQAt
    P A4 S x copy z member edge edgeMember hz 0).append
    (xStarFaceBoundaryPathToZ _ _
      (rxOriginalBoundaryZVerticalGlueXStarFaceAt
        P A4 S x copy z member edge edgeMember hz))
theorem rxOriginalBoundaryZSmallFace_eq
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (candidateCopy : Two) (candidateFace : XStarFace P x)
    (column row : Fin S.half) (first second : Two)
    (hx : localFaceX P S
      ⟨x,
        Sum.inl (candidateCopy, (candidateFace, column, row)),
        (first, second)⟩ =
      rxOriginalBoundaryZXCoordinate P S x copy z member) :
    P.faceZ candidateFace.1 = z ∧
      (⟨x,
          Sum.inl (candidateCopy, (candidateFace, column, row)),
          (first, second)⟩ : RXLocalFace P S) =
        rxOriginalBoundaryZLocalFaceAt P S x copy candidateFace := by
  have hvertex :
      (candidateCopy, subdivisionGridVertex P x S candidateFace
        (gridEndpoint column first) (gridEndpoint row second)) =
      (copy, Sum.inl ⟨Vertex.z z, by
        simpa [xStarBoundaryVertexMember, xStarVertexMember] using member⟩) :=
    eq_of_heq (Sigma.mk.inj_iff.mp hx).2
  have hcopy : candidateCopy = copy := congrArg Prod.fst hvertex
  subst candidateCopy
  have hgrid := congrArg Prod.snd hvertex
  obtain ⟨hcolumn, hrow, hz⟩ :=
    subdivisionGridVertex_eq_originalZ_coordinates
      P S x candidateFace (gridEndpoint column first)
        (gridEndpoint row second) z _ hgrid
  have hfirst : first = 1 := by
    fin_cases first
    · simp [gridEndpoint, lowerGridIndex] at hcolumn
      have := column.2
      omega
    · rfl
  have hsecond : second = 1 := by
    fin_cases second
    · simp [gridEndpoint, lowerGridIndex] at hrow
      have := row.2
      omega
    · rfl
  subst first
  subst second
  have hcolumnIndex : column = rxStarEdgeInteriorLastIndex S := by
    apply Fin.ext
    change column.1 = S.half - 1
    have hcolumn' := hcolumn
    simp [gridEndpoint, upperGridIndex] at hcolumn'
    omega
  have hrowIndex : row = rxStarEdgeInteriorLastIndex S := by
    apply Fin.ext
    change row.1 = S.half - 1
    have hrow' := hrow
    simp [gridEndpoint, upperGridIndex] at hrow'
    omega
  rw [hcolumnIndex, hrowIndex]
  exact ⟨hz, rfl⟩
noncomputable def rxOriginalBoundaryZOwnerBoundaryPathToQAt
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (corner : Two) := by
  let bridge := (xStarFaceBoundaryPathToQ
    (rxReplacementPresentation P S)
    (rxOriginalBoundaryZXCoordinate P S x copy z member)
    (rxOriginalBoundaryZOwnerXStarFace P A4 S x copy z member)
    (flipEndpoint (rxOriginalBoundaryZRootCorner P A4 x z member))).reverse
  let last := xStarFaceBoundaryPathToQ
    (rxReplacementPresentation P S)
    (rxOriginalBoundaryZXCoordinate P S x copy z member)
    (rxOriginalBoundaryZOwnerXStarFace P A4 S x copy z member) corner
  exact ((rxOriginalBoundaryZOwnerBoundaryVertexEq
    P A4 S x copy z member) ▸ bridge).append last
noncomputable def rxOriginalBoundaryZOwnerBoundaryPathToZ
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true) :=
  (rxOriginalBoundaryZOwnerBoundaryPathToQAt
    P A4 S x copy z member 0).append
    (xStarFaceBoundaryPathToZ _ _
      (rxOriginalBoundaryZOwnerXStarFace
        P A4 S x copy z member))
inductive RXOriginalBoundaryZTarget
    (P : TannerSquarePresentation) (x : P.X) (z : P.Z)
  | ownerQ (corner : Two)
  | ownerZ
  | localQ (face : XStarFace P x) (hz : P.faceZ face.1 = z)
      (faceCorner targetCorner : Two)
  | localZ (face : XStarFace P x) (hz : P.faceZ face.1 = z)
      (faceCorner : Two)
  | rectangleQ (edge : QZEdge P)
      (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
      (hz : edge.1.2 = z) (corner : Two)
  | rectangleZ (edge : QZEdge P)
      (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
      (hz : edge.1.2 = z)
  | glueQ (edge : QZEdge P)
      (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
      (hz : edge.1.2 = z) (corner : Two)
  | glueZ (edge : QZEdge P)
      (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
      (hz : edge.1.2 = z)
  | verticalGlueQ (edge : QZEdge P)
      (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
      (hz : edge.1.2 = z) (corner : Two)
  | verticalGlueZ (edge : QZEdge P)
      (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
      (hz : edge.1.2 = z)
  | oldQ (face : XStarFace P x) (hz : P.faceZ face.1 = z)
      (corner : Two)
  | oldZ (face : XStarFace P x) (hz : P.faceZ face.1 = z)
noncomputable def rxOriginalBoundaryZTargetBoundaryVertex
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true) :
    RXOriginalBoundaryZTarget P x z →
      XStarBoundaryVertex (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z member)
  | .ownerQ corner =>
      xBoundaryEdgeStart (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxOriginalBoundaryZOwnerXStarFace
            P A4 S x copy z member) corner)
  | .ownerZ =>
      xBoundaryEdgeEnd (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxOriginalBoundaryZOwnerXStarFace
            P A4 S x copy z member) 0)
  | .localQ face hz _ targetCorner =>
      xBoundaryEdgeStart (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxOriginalBoundaryZLocalXStarFaceAt
            P S x copy z member face hz) targetCorner)
  | .localZ face hz _ =>
      xBoundaryEdgeEnd (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxOriginalBoundaryZLocalXStarFaceAt
            P S x copy z member face hz) 0)
  | .rectangleQ edge edgeMember hz corner =>
      xBoundaryEdgeStart (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxOriginalBoundaryZRectangleXStarFaceAt
            P S x copy z member edge edgeMember hz) corner)
  | .rectangleZ edge edgeMember hz =>
      xBoundaryEdgeEnd (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxOriginalBoundaryZRectangleXStarFaceAt
            P S x copy z member edge edgeMember hz) 0)
  | .glueQ edge edgeMember hz corner =>
      xBoundaryEdgeStart (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxOriginalBoundaryZGlueXStarFaceAt
            P A4 S x copy z member edge edgeMember hz) corner)
  | .glueZ edge edgeMember hz =>
      xBoundaryEdgeEnd (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxOriginalBoundaryZGlueXStarFaceAt
            P A4 S x copy z member edge edgeMember hz) 0)
  | .verticalGlueQ edge edgeMember hz corner =>
      xBoundaryEdgeStart (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxOriginalBoundaryZVerticalGlueXStarFaceAt
            P A4 S x copy z member edge edgeMember hz) corner)
  | .verticalGlueZ edge edgeMember hz =>
      xBoundaryEdgeEnd (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxOriginalBoundaryZVerticalGlueXStarFaceAt
            P A4 S x copy z member edge edgeMember hz) 0)
  | .oldQ face hz corner =>
      xBoundaryEdgeStart (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxOriginalBoundaryZOldFaceXStarFaceAt
            P A4 S x copy z member face hz) corner)
  | .oldZ face hz =>
      xBoundaryEdgeEnd (rxReplacementPresentation P S) _
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S) _
          (rxOriginalBoundaryZOldFaceXStarFaceAt
            P A4 S x copy z member face hz) 0)
noncomputable def rxOriginalBoundaryZTargetBoundaryPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (target : RXOriginalBoundaryZTarget P x z) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z member))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z member))
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z member)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxOriginalBoundaryZXCoordinate P S x copy z member)
          (rxOriginalBoundaryZRootXStarFace
            P A4 S x copy z member) 0))
      (rxOriginalBoundaryZTargetBoundaryVertex
        P A4 S x copy z member target) := by
  rcases target with
    ⟨corner⟩ | _ |
    ⟨face, hz, faceCorner, targetCorner⟩ |
    ⟨face, hz, faceCorner⟩ |
    ⟨edge, edgeMember, hz, corner⟩ |
    ⟨edge, edgeMember, hz⟩ |
    ⟨edge, edgeMember, hz, corner⟩ |
    ⟨edge, edgeMember, hz⟩ |
    ⟨edge, edgeMember, hz, corner⟩ |
    ⟨edge, edgeMember, hz⟩ |
    ⟨face, hz, corner⟩ |
    ⟨face, hz⟩
  · exact rxOriginalBoundaryZOwnerBoundaryPathToQAt
      P A4 S x copy z member corner
  · exact rxOriginalBoundaryZOwnerBoundaryPathToZ
      P A4 S x copy z member
  · exact rxOriginalBoundaryZLocalBoundaryPathToQAt
      P A4 S x copy z member face hz faceCorner targetCorner
  · exact rxOriginalBoundaryZLocalBoundaryPathToZAt
      P A4 S x copy z member face hz faceCorner
  · exact rxOriginalBoundaryZRectangleBoundaryPathToQAt
      P A4 S x copy z member edge edgeMember hz corner
  · exact rxOriginalBoundaryZRectangleBoundaryPathToZAt
      P A4 S x copy z member edge edgeMember hz
  · exact rxOriginalBoundaryZGlueBoundaryPathToQAt
      P A4 S x copy z member edge edgeMember hz corner
  · exact rxOriginalBoundaryZGlueBoundaryPathToZAt
      P A4 S x copy z member edge edgeMember hz
  · exact rxOriginalBoundaryZVerticalGlueBoundaryPathToQAt
      P A4 S x copy z member edge edgeMember hz corner
  · exact rxOriginalBoundaryZVerticalGlueBoundaryPathToZAt
      P A4 S x copy z member edge edgeMember hz
  · exact rxOriginalBoundaryZOldFaceBoundaryPathToQAt
      P A4 S x copy z member face hz corner
  · exact rxOriginalBoundaryZOldFaceBoundaryPathToZAt
      P A4 S x copy z member face hz
noncomputable def rxOriginalBoundaryZIncidentXStarFace
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (candidate : RXFace P S)
    (hx : rxFaceX P S candidate =
      rxOriginalBoundaryZXCoordinate P S x copy z member) :
    XStarFace (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z member) :=
  ⟨candidate, by
    simp only [xStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
    exact hx⟩
noncomputable def rxOriginalBoundaryZSmallQTarget
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (candidateX : P.X) (candidateCopy : Two)
    (candidateFace : XStarFace P candidateX)
    (column row : Fin S.half) (first second corner : Two)
    (hx : rxFaceX P S
      (Sum.inl ⟨candidateX,
        Sum.inl (candidateCopy, (candidateFace, column, row)),
        (first, second)⟩) =
      rxOriginalBoundaryZXCoordinate P S x copy z member) :
    {target : RXOriginalBoundaryZTarget P x z //
      rxOriginalBoundaryZTargetBoundaryVertex
          P A4 S x copy z member target =
        xBoundaryEdgeStart (rxReplacementPresentation P S)
          (rxOriginalBoundaryZXCoordinate P S x copy z member)
          (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
            (rxOriginalBoundaryZXCoordinate P S x copy z member)
            (rxOriginalBoundaryZIncidentXStarFace P S x copy z member
              (Sum.inl ⟨candidateX,
                Sum.inl (candidateCopy, (candidateFace, column, row)),
                (first, second)⟩) hx) corner)} := by
  have howner : candidateX = x := congrArg Sigma.fst hx
  subst candidateX
  obtain ⟨hz, hcandidate⟩ := rxOriginalBoundaryZSmallFace_eq
    P S x copy z member candidateCopy candidateFace
      column row first second (by simpa [rxFaceX] using hx)
  refine ⟨.localQ candidateFace hz 0 corner, ?_⟩
  have hface : rxOriginalBoundaryZIncidentXStarFace P S x copy z member
        (Sum.inl ⟨x,
          Sum.inl (candidateCopy, (candidateFace, column, row)),
          (first, second)⟩) hx =
      rxOriginalBoundaryZLocalXStarFaceAt
        P S x copy z member candidateFace hz := by
    apply Subtype.ext
    exact congrArg Sum.inl hcandidate
  rw [hface]
  rfl
noncomputable def rxOriginalBoundaryZSmallZTarget
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (candidateX : P.X) (candidateCopy : Two)
    (candidateFace : XStarFace P candidateX)
    (column row : Fin S.half) (first second : Two)
    (hx : rxFaceX P S
      (Sum.inl ⟨candidateX,
        Sum.inl (candidateCopy, (candidateFace, column, row)),
        (first, second)⟩) =
      rxOriginalBoundaryZXCoordinate P S x copy z member) :
    {target : RXOriginalBoundaryZTarget P x z //
      rxOriginalBoundaryZTargetBoundaryVertex
          P A4 S x copy z member target =
        xBoundaryEdgeEnd (rxReplacementPresentation P S)
          (rxOriginalBoundaryZXCoordinate P S x copy z member)
          (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
            (rxOriginalBoundaryZXCoordinate P S x copy z member)
            (rxOriginalBoundaryZIncidentXStarFace P S x copy z member
              (Sum.inl ⟨candidateX,
                Sum.inl (candidateCopy, (candidateFace, column, row)),
                (first, second)⟩) hx) 0)} := by
  have howner : candidateX = x := congrArg Sigma.fst hx
  subst candidateX
  obtain ⟨hz, hcandidate⟩ := rxOriginalBoundaryZSmallFace_eq
    P S x copy z member candidateCopy candidateFace
      column row first second (by simpa [rxFaceX] using hx)
  refine ⟨.localZ candidateFace hz 0, ?_⟩
  have hface : rxOriginalBoundaryZIncidentXStarFace P S x copy z member
        (Sum.inl ⟨x,
          Sum.inl (candidateCopy, (candidateFace, column, row)),
          (first, second)⟩) hx =
      rxOriginalBoundaryZLocalXStarFaceAt
        P S x copy z member candidateFace hz := by
    apply Subtype.ext
    exact congrArg Sum.inl hcandidate
  rw [hface]
  rfl
theorem rxOriginalBoundaryZRectangleFace_eq
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (segment : Fin S.half)
    (boundaryMember : subdivisionBoundaryEdgeMember P x S
      (Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment)) = true)
    (candidateCopy endpoint : Two)
    (hx : localFaceX P S
      ⟨x,
        Sum.inr ⟨Sum.inl
          (⟨Sum.inr edge, edgeMember⟩, segment), boundaryMember⟩,
        (candidateCopy, endpoint)⟩ =
      rxOriginalBoundaryZXCoordinate P S x copy z member) :
    edge.1.2 = z ∧
      (⟨x,
          Sum.inr ⟨Sum.inl
            (⟨Sum.inr edge, edgeMember⟩, segment), boundaryMember⟩,
          (candidateCopy, endpoint)⟩ : RXLocalFace P S) =
        rxOriginalBoundaryZRectangleLocalFaceAt
          P S x copy edge edgeMember := by
  have hvertex : doubleCylinderRectangleCorner P x S
        ⟨Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment), boundaryMember⟩
        (candidateCopy, endpoint) =
      (copy, Sum.inl ⟨Vertex.z z, by
        simpa [xStarBoundaryVertexMember, xStarVertexMember] using member⟩) :=
    eq_of_heq (Sigma.mk.inj_iff.mp hx).2
  have hcopy : candidateCopy = copy := congrArg Prod.fst hvertex
  subst candidateCopy
  have hsubdivision := congrArg Prod.snd hvertex
  have hendpoint : endpoint = 1 := by
    fin_cases endpoint
    · by_cases hzero : segment.1 = 0
      · have hstart : xStarEdgeStart P x
            ⟨Sum.inr edge, edgeMember⟩ =
          ⟨Vertex.z z, by
            simpa [xStarBoundaryVertexMember, xStarVertexMember]
              using member⟩ := by
          have hinl :
              (Sum.inl (xStarEdgeStart P x
                ⟨Sum.inr edge, edgeMember⟩) :
                SubdivisionVertex P x S) =
              Sum.inl ⟨Vertex.z z, by
                simpa [xStarBoundaryVertexMember, xStarVertexMember]
                  using member⟩ := by
            simpa [doubleCylinderRectangleCorner,
              subdivisionBoundaryEdgeStart, subdivisionEdgeStart,
              subdivisionSegmentStart, hzero] using hsubdivision
          exact Sum.inl.inj hinl
        have hraw := congrArg Subtype.val hstart
        change Vertex.q edge.1.1 = Vertex.z z at hraw
        cases hraw
      · have himpossible :
            (Sum.inr (Sum.inl
              (⟨Sum.inr edge, edgeMember⟩,
                ⟨segment.1 - 1, by have := segment.2; omega⟩)) :
              SubdivisionVertex P x S) =
            Sum.inl ⟨Vertex.z z, by
              simpa [xStarBoundaryVertexMember, xStarVertexMember]
                using member⟩ := by
          simpa [doubleCylinderRectangleCorner,
            subdivisionBoundaryEdgeStart, subdivisionEdgeStart,
            subdivisionSegmentStart, hzero] using hsubdivision
        cases himpossible
    · rfl
  subst endpoint
  by_cases hlast : segment.1 + 1 = S.half
  · have hend : xStarEdgeEnd P x ⟨Sum.inr edge, edgeMember⟩ =
        ⟨Vertex.z z, by
          simpa [xStarBoundaryVertexMember, xStarVertexMember]
            using member⟩ := by
      have hinl :
          (Sum.inl (xStarEdgeEnd P x ⟨Sum.inr edge, edgeMember⟩) :
            SubdivisionVertex P x S) =
          Sum.inl ⟨Vertex.z z, by
            simpa [xStarBoundaryVertexMember, xStarVertexMember]
              using member⟩ := by
        simpa [doubleCylinderRectangleCorner,
          subdivisionBoundaryEdgeEnd, subdivisionEdgeEnd,
          subdivisionSegmentEnd, hlast] using hsubdivision
      exact Sum.inl.inj hinl
    have hz : edge.1.2 = z :=
      Vertex.z.inj (congrArg Subtype.val hend)
    have hsegment : segment = rxStarEdgeInteriorLastIndex S := by
      apply Fin.ext
      change segment.1 = S.half - 1
      omega
    rw [hsegment]
    exact ⟨hz, rfl⟩
  · have himpossible :
        (Sum.inr (Sum.inl
          (⟨Sum.inr edge, edgeMember⟩,
            ⟨segment.1, by have := segment.2; omega⟩)) :
          SubdivisionVertex P x S) =
        Sum.inl ⟨Vertex.z z, by
          simpa [xStarBoundaryVertexMember, xStarVertexMember]
            using member⟩ := by
      simpa [doubleCylinderRectangleCorner,
        subdivisionBoundaryEdgeEnd, subdivisionEdgeEnd,
        subdivisionSegmentEnd, hlast] using hsubdivision
    cases himpossible
noncomputable def rxOriginalBoundaryZRectangleQTarget
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (segment : Fin S.half)
    (boundaryMember : subdivisionBoundaryEdgeMember P x S
      (Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment)) = true)
    (candidateCopy endpoint corner : Two)
    (hx : rxFaceX P S
      (Sum.inl ⟨x,
        Sum.inr ⟨Sum.inl
          (⟨Sum.inr edge, edgeMember⟩, segment), boundaryMember⟩,
        (candidateCopy, endpoint)⟩) =
      rxOriginalBoundaryZXCoordinate P S x copy z member) :
    {target : RXOriginalBoundaryZTarget P x z //
      rxOriginalBoundaryZTargetBoundaryVertex
          P A4 S x copy z member target =
        xBoundaryEdgeStart (rxReplacementPresentation P S)
          (rxOriginalBoundaryZXCoordinate P S x copy z member)
          (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
            (rxOriginalBoundaryZXCoordinate P S x copy z member)
            (rxOriginalBoundaryZIncidentXStarFace P S x copy z member
              (Sum.inl ⟨x,
                Sum.inr ⟨Sum.inl
                  (⟨Sum.inr edge, edgeMember⟩, segment), boundaryMember⟩,
                (candidateCopy, endpoint)⟩) hx) corner)} := by
  obtain ⟨hz, hcandidate⟩ := rxOriginalBoundaryZRectangleFace_eq
    P S x copy z member edge edgeMember segment boundaryMember
      candidateCopy endpoint (by simpa [rxFaceX] using hx)
  refine ⟨.rectangleQ edge edgeMember hz corner, ?_⟩
  have hface : rxOriginalBoundaryZIncidentXStarFace P S x copy z member
        (Sum.inl ⟨x,
          Sum.inr ⟨Sum.inl
            (⟨Sum.inr edge, edgeMember⟩, segment), boundaryMember⟩,
          (candidateCopy, endpoint)⟩) hx =
      rxOriginalBoundaryZRectangleXStarFaceAt
        P S x copy z member edge edgeMember hz := by
    apply Subtype.ext
    exact congrArg Sum.inl hcandidate
  rw [hface]
  rfl
noncomputable def rxOriginalBoundaryZRectangleZTarget
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (segment : Fin S.half)
    (boundaryMember : subdivisionBoundaryEdgeMember P x S
      (Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment)) = true)
    (candidateCopy endpoint : Two)
    (hx : rxFaceX P S
      (Sum.inl ⟨x,
        Sum.inr ⟨Sum.inl
          (⟨Sum.inr edge, edgeMember⟩, segment), boundaryMember⟩,
        (candidateCopy, endpoint)⟩) =
      rxOriginalBoundaryZXCoordinate P S x copy z member) :
    {target : RXOriginalBoundaryZTarget P x z //
      rxOriginalBoundaryZTargetBoundaryVertex
          P A4 S x copy z member target =
        xBoundaryEdgeEnd (rxReplacementPresentation P S)
          (rxOriginalBoundaryZXCoordinate P S x copy z member)
          (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
            (rxOriginalBoundaryZXCoordinate P S x copy z member)
            (rxOriginalBoundaryZIncidentXStarFace P S x copy z member
              (Sum.inl ⟨x,
                Sum.inr ⟨Sum.inl
                  (⟨Sum.inr edge, edgeMember⟩, segment), boundaryMember⟩,
                (candidateCopy, endpoint)⟩) hx) 0)} := by
  obtain ⟨hz, hcandidate⟩ := rxOriginalBoundaryZRectangleFace_eq
    P S x copy z member edge edgeMember segment boundaryMember
      candidateCopy endpoint (by simpa [rxFaceX] using hx)
  refine ⟨.rectangleZ edge edgeMember hz, ?_⟩
  have hface : rxOriginalBoundaryZIncidentXStarFace P S x copy z member
        (Sum.inl ⟨x,
          Sum.inr ⟨Sum.inl
            (⟨Sum.inr edge, edgeMember⟩, segment), boundaryMember⟩,
          (candidateCopy, endpoint)⟩) hx =
      rxOriginalBoundaryZRectangleXStarFaceAt
        P S x copy z member edge edgeMember hz := by
    apply Subtype.ext
    exact congrArg Sum.inl hcandidate
  rw [hface]
  rfl
def rxOriginalBoundaryZGlueEdge
    (P : TannerSquarePresentation) (q : P.Q)
    (edge : QStarEdge P q) : QZEdge P :=
  ⟨(q, edge.1), edge.2⟩
theorem rxOriginalBoundaryZGlueEdge_member
    (P : TannerSquarePresentation) (x : P.X) (q : P.Q)
    (hxq : P.xq x q = true) (edge : QStarEdge P q) :
    xStarEdgeMember P x
      (Sum.inr (rxOriginalBoundaryZGlueEdge P q edge)) = true :=
  (xStarBoundaryEdgeToStar P x
    (qToXBoundaryEdge P q x hxq edge)).2
theorem rxOriginalBoundaryZGlueFace_eq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (q : P.Q) (hxq : P.xq x q = true) (edge : QStarEdge P q)
    (segment : Fin S.half) (candidateCopy endpoint : Two)
    (hx : glueFaceX P S
      ⟨(⟨(x, q), hxq⟩ : XQEdge P),
        Sum.inl (candidateCopy, (edge, segment)), endpoint⟩ =
      rxOriginalBoundaryZXCoordinate P S x copy z member) :
    edge.1 = z ∧
      (⟨(⟨(x, q), hxq⟩ : XQEdge P),
          Sum.inl (candidateCopy, (edge, segment)), endpoint⟩ :
          RXXQGlueFace P S) =
        rxOriginalBoundaryZGlueFaceAt P A4 S x copy
          (rxOriginalBoundaryZGlueEdge P q edge)
          (rxOriginalBoundaryZGlueEdge_member P x q hxq edge) := by
  have hvertex : edgeEndpoint
        (tannerDoubleCylinderEdgeStart P x S)
        (tannerDoubleCylinderEdgeEnd P x S)
        (qToXDoubleCylinderEdgeRaw P q x hxq S
          (Sum.inl (candidateCopy, (edge, segment)))) endpoint =
      (copy, Sum.inl ⟨Vertex.z z, by
        simpa [xStarBoundaryVertexMember, xStarVertexMember] using member⟩) :=
    eq_of_heq (Sigma.mk.inj_iff.mp hx).2
  have hcopy : candidateCopy = copy := by
    fin_cases endpoint <;>
      simpa [edgeEndpoint, qToXDoubleCylinderEdgeRaw,
        tannerDoubleCylinderEdgeStart, tannerDoubleCylinderEdgeEnd]
        using congrArg Prod.fst hvertex
  subst candidateCopy
  have hsubdivision := congrArg Prod.snd hvertex
  have hendpoint : endpoint = 1 := by
    fin_cases endpoint
    · by_cases hzero : segment.1 = 0
      · have hstart : xStarEdgeStart P x
            (xStarBoundaryEdgeToStar P x
              (qToXBoundaryEdge P q x hxq edge)) =
          ⟨Vertex.z z, by
            simpa [xStarBoundaryVertexMember, xStarVertexMember]
              using member⟩ := by
          simpa [edgeEndpoint, qToXDoubleCylinderEdgeRaw,
            tannerDoubleCylinderEdgeStart,
            qToXSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge,
            subdivisionEdgeStart, subdivisionSegmentStart, hzero]
            using hsubdivision
        have hraw := congrArg Subtype.val hstart
        change Vertex.q q = Vertex.z z at hraw
        cases hraw
      · have himpossible :
            (Sum.inr (Sum.inl
              (xStarBoundaryEdgeToStar P x
                (qToXBoundaryEdge P q x hxq edge),
                ⟨segment.1 - 1, by have := segment.2; omega⟩)) :
              SubdivisionVertex P x S) =
            Sum.inl ⟨Vertex.z z, by
              simpa [xStarBoundaryVertexMember, xStarVertexMember]
                using member⟩ := by
          simpa [edgeEndpoint, qToXDoubleCylinderEdgeRaw,
            tannerDoubleCylinderEdgeStart,
            qToXSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge,
            subdivisionEdgeStart, subdivisionSegmentStart, hzero]
            using hsubdivision
        cases himpossible
    · rfl
  subst endpoint
  by_cases hlast : segment.1 + 1 = S.half
  · have hend : xStarEdgeEnd P x
          (xStarBoundaryEdgeToStar P x
            (qToXBoundaryEdge P q x hxq edge)) =
        ⟨Vertex.z z, by
          simpa [xStarBoundaryVertexMember, xStarVertexMember]
            using member⟩ := by
      simpa [edgeEndpoint, qToXDoubleCylinderEdgeRaw,
        tannerDoubleCylinderEdgeEnd,
        qToXSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge,
        subdivisionEdgeEnd, subdivisionSegmentEnd, hlast]
        using hsubdivision
    have hz : edge.1 = z :=
      Vertex.z.inj (congrArg Subtype.val hend)
    have hsegment : segment = rxStarEdgeInteriorLastIndex S := by
      apply Fin.ext
      change segment.1 = S.half - 1
      omega
    rw [hsegment]
    refine ⟨hz, ?_⟩
    apply Sigma.ext
    · apply Subtype.ext
      rfl
    · apply heq_of_eq
      rfl
  · have himpossible :
        (Sum.inr (Sum.inl
          (xStarBoundaryEdgeToStar P x
            (qToXBoundaryEdge P q x hxq edge),
            ⟨segment.1, by have := segment.2; omega⟩)) :
          SubdivisionVertex P x S) =
        Sum.inl ⟨Vertex.z z, by
          simpa [xStarBoundaryVertexMember, xStarVertexMember]
            using member⟩ := by
      simpa [edgeEndpoint, qToXDoubleCylinderEdgeRaw,
        tannerDoubleCylinderEdgeEnd,
        qToXSubdivisionBoundaryEdge, subdivisionOriginalBoundaryEdge,
        subdivisionEdgeEnd, subdivisionSegmentEnd, hlast]
        using hsubdivision
    cases himpossible
noncomputable def rxOriginalBoundaryZGlueQTarget
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (q : P.Q) (hxq : P.xq x q = true) (edge : QStarEdge P q)
    (segment : Fin S.half) (candidateCopy endpoint corner : Two)
    (hx : rxFaceX P S
      (Sum.inr (Sum.inl
        ⟨(⟨(x, q), hxq⟩ : XQEdge P),
          Sum.inl (candidateCopy, (edge, segment)), endpoint⟩)) =
      rxOriginalBoundaryZXCoordinate P S x copy z member) :
    {target : RXOriginalBoundaryZTarget P x z //
      rxOriginalBoundaryZTargetBoundaryVertex
          P A4 S x copy z member target =
        xBoundaryEdgeStart (rxReplacementPresentation P S)
          (rxOriginalBoundaryZXCoordinate P S x copy z member)
          (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
            (rxOriginalBoundaryZXCoordinate P S x copy z member)
            (rxOriginalBoundaryZIncidentXStarFace P S x copy z member
              (Sum.inr (Sum.inl
                ⟨(⟨(x, q), hxq⟩ : XQEdge P),
                  Sum.inl (candidateCopy, (edge, segment)), endpoint⟩)) hx)
            corner)} := by
  obtain ⟨hz, hcandidate⟩ := rxOriginalBoundaryZGlueFace_eq
    P A4 S x copy z member q hxq edge segment candidateCopy endpoint
      (by simpa [rxFaceX] using hx)
  let oldEdge := rxOriginalBoundaryZGlueEdge P q edge
  let oldEdgeMember := rxOriginalBoundaryZGlueEdge_member P x q hxq edge
  refine ⟨.glueQ oldEdge oldEdgeMember hz corner, ?_⟩
  have hface : rxOriginalBoundaryZIncidentXStarFace P S x copy z member
        (Sum.inr (Sum.inl
          ⟨(⟨(x, q), hxq⟩ : XQEdge P),
            Sum.inl (candidateCopy, (edge, segment)), endpoint⟩)) hx =
      rxOriginalBoundaryZGlueXStarFaceAt P A4 S x copy z member
        oldEdge oldEdgeMember hz := by
    apply Subtype.ext
    exact congrArg (fun glue => Sum.inr (Sum.inl glue)) hcandidate
  rw [hface]
  rfl
noncomputable def rxOriginalBoundaryZGlueZTarget
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (q : P.Q) (hxq : P.xq x q = true) (edge : QStarEdge P q)
    (segment : Fin S.half) (candidateCopy endpoint : Two)
    (hx : rxFaceX P S
      (Sum.inr (Sum.inl
        ⟨(⟨(x, q), hxq⟩ : XQEdge P),
          Sum.inl (candidateCopy, (edge, segment)), endpoint⟩)) =
      rxOriginalBoundaryZXCoordinate P S x copy z member) :
    {target : RXOriginalBoundaryZTarget P x z //
      rxOriginalBoundaryZTargetBoundaryVertex
          P A4 S x copy z member target =
        xBoundaryEdgeEnd (rxReplacementPresentation P S)
          (rxOriginalBoundaryZXCoordinate P S x copy z member)
          (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
            (rxOriginalBoundaryZXCoordinate P S x copy z member)
            (rxOriginalBoundaryZIncidentXStarFace P S x copy z member
              (Sum.inr (Sum.inl
                ⟨(⟨(x, q), hxq⟩ : XQEdge P),
                  Sum.inl (candidateCopy, (edge, segment)), endpoint⟩)) hx)
            0)} := by
  obtain ⟨hz, hcandidate⟩ := rxOriginalBoundaryZGlueFace_eq
    P A4 S x copy z member q hxq edge segment candidateCopy endpoint
      (by simpa [rxFaceX] using hx)
  let oldEdge := rxOriginalBoundaryZGlueEdge P q edge
  let oldEdgeMember := rxOriginalBoundaryZGlueEdge_member P x q hxq edge
  refine ⟨.glueZ oldEdge oldEdgeMember hz, ?_⟩
  have hface : rxOriginalBoundaryZIncidentXStarFace P S x copy z member
        (Sum.inr (Sum.inl
          ⟨(⟨(x, q), hxq⟩ : XQEdge P),
            Sum.inl (candidateCopy, (edge, segment)), endpoint⟩)) hx =
      rxOriginalBoundaryZGlueXStarFaceAt P A4 S x copy z member
        oldEdge oldEdgeMember hz := by
    apply Subtype.ext
    exact congrArg (fun glue => Sum.inr (Sum.inl glue)) hcandidate
  rw [hface]
  rfl
theorem rxOriginalBoundaryZVerticalGlueFace_eq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (q : P.Q) (hxq : P.xq x q = true) (edge : QStarEdge P q)
    (endpoint : Two)
    (hx : glueFaceX P S
      ⟨(⟨(x, q), hxq⟩ : XQEdge P), Sum.inr edge, endpoint⟩ =
      rxOriginalBoundaryZXCoordinate P S x copy z member) :
    edge.1 = z ∧ endpoint = copy ∧
      (⟨(⟨(x, q), hxq⟩ : XQEdge P), Sum.inr edge, endpoint⟩ :
          RXXQGlueFace P S) =
        rxOriginalBoundaryZVerticalGlueFaceAt P A4 S x copy
          (rxOriginalBoundaryZGlueEdge P q edge)
          (rxOriginalBoundaryZGlueEdge_member P x q hxq edge) := by
  have hvertex : edgeEndpoint
        (tannerDoubleCylinderEdgeStart P x S)
        (tannerDoubleCylinderEdgeEnd P x S)
        (qToXDoubleCylinderEdgeRaw P q x hxq S (Sum.inr edge)) endpoint =
      (copy, Sum.inl ⟨Vertex.z z, by
        simpa [xStarBoundaryVertexMember, xStarVertexMember] using member⟩) :=
    eq_of_heq (Sigma.mk.inj_iff.mp hx).2
  have hcopy : endpoint = copy := by
    fin_cases endpoint <;> fin_cases copy <;>
      simp [edgeEndpoint, qToXDoubleCylinderEdgeRaw,
        tannerDoubleCylinderEdgeStart, tannerDoubleCylinderEdgeEnd]
        at hvertex ⊢
  subst endpoint
  have hend : xStarEdgeEnd P x
        (xStarBoundaryEdgeToStar P x
          (qToXBoundaryEdge P q x hxq edge)) =
      ⟨Vertex.z z, by
        simpa [xStarBoundaryVertexMember, xStarVertexMember]
          using member⟩ := by
    have hsubdivision := congrArg Prod.snd hvertex
    fin_cases copy <;>
      simpa [edgeEndpoint, qToXDoubleCylinderEdgeRaw,
        tannerDoubleCylinderEdgeStart, tannerDoubleCylinderEdgeEnd,
        subdivisionOriginalBoundaryVertex] using hsubdivision
  have hz : edge.1 = z :=
    Vertex.z.inj (congrArg Subtype.val hend)
  refine ⟨hz, rfl, ?_⟩
  apply Sigma.ext
  · apply Subtype.ext
    rfl
  · apply heq_of_eq
    rfl
noncomputable def rxOriginalBoundaryZVerticalGlueQTarget
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (q : P.Q) (hxq : P.xq x q = true) (edge : QStarEdge P q)
    (endpoint corner : Two)
    (hx : rxFaceX P S
      (Sum.inr (Sum.inl
        ⟨(⟨(x, q), hxq⟩ : XQEdge P), Sum.inr edge, endpoint⟩)) =
      rxOriginalBoundaryZXCoordinate P S x copy z member) :
    {target : RXOriginalBoundaryZTarget P x z //
      rxOriginalBoundaryZTargetBoundaryVertex
          P A4 S x copy z member target =
        xBoundaryEdgeStart (rxReplacementPresentation P S)
          (rxOriginalBoundaryZXCoordinate P S x copy z member)
          (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
            (rxOriginalBoundaryZXCoordinate P S x copy z member)
            (rxOriginalBoundaryZIncidentXStarFace P S x copy z member
              (Sum.inr (Sum.inl
                ⟨(⟨(x, q), hxq⟩ : XQEdge P),
                  Sum.inr edge, endpoint⟩)) hx) corner)} := by
  obtain ⟨hz, _, hcandidate⟩ := rxOriginalBoundaryZVerticalGlueFace_eq
    P A4 S x copy z member q hxq edge endpoint
      (by simpa [rxFaceX] using hx)
  let oldEdge := rxOriginalBoundaryZGlueEdge P q edge
  let oldEdgeMember := rxOriginalBoundaryZGlueEdge_member P x q hxq edge
  refine ⟨.verticalGlueQ oldEdge oldEdgeMember hz corner, ?_⟩
  have hface : rxOriginalBoundaryZIncidentXStarFace P S x copy z member
        (Sum.inr (Sum.inl
          ⟨(⟨(x, q), hxq⟩ : XQEdge P), Sum.inr edge, endpoint⟩)) hx =
      rxOriginalBoundaryZVerticalGlueXStarFaceAt P A4 S x copy z member
        oldEdge oldEdgeMember hz := by
    apply Subtype.ext
    exact congrArg (fun glue => Sum.inr (Sum.inl glue)) hcandidate
  rw [hface]
  rfl
noncomputable def rxOriginalBoundaryZVerticalGlueZTarget
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (q : P.Q) (hxq : P.xq x q = true) (edge : QStarEdge P q)
    (endpoint : Two)
    (hx : rxFaceX P S
      (Sum.inr (Sum.inl
        ⟨(⟨(x, q), hxq⟩ : XQEdge P), Sum.inr edge, endpoint⟩)) =
      rxOriginalBoundaryZXCoordinate P S x copy z member) :
    {target : RXOriginalBoundaryZTarget P x z //
      rxOriginalBoundaryZTargetBoundaryVertex
          P A4 S x copy z member target =
        xBoundaryEdgeEnd (rxReplacementPresentation P S)
          (rxOriginalBoundaryZXCoordinate P S x copy z member)
          (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
            (rxOriginalBoundaryZXCoordinate P S x copy z member)
            (rxOriginalBoundaryZIncidentXStarFace P S x copy z member
              (Sum.inr (Sum.inl
                ⟨(⟨(x, q), hxq⟩ : XQEdge P),
                  Sum.inr edge, endpoint⟩)) hx) 0)} := by
  obtain ⟨hz, _, hcandidate⟩ := rxOriginalBoundaryZVerticalGlueFace_eq
    P A4 S x copy z member q hxq edge endpoint
      (by simpa [rxFaceX] using hx)
  let oldEdge := rxOriginalBoundaryZGlueEdge P q edge
  let oldEdgeMember := rxOriginalBoundaryZGlueEdge_member P x q hxq edge
  refine ⟨.verticalGlueZ oldEdge oldEdgeMember hz, ?_⟩
  have hface : rxOriginalBoundaryZIncidentXStarFace P S x copy z member
        (Sum.inr (Sum.inl
          ⟨(⟨(x, q), hxq⟩ : XQEdge P), Sum.inr edge, endpoint⟩)) hx =
      rxOriginalBoundaryZVerticalGlueXStarFaceAt P A4 S x copy z member
        oldEdge oldEdgeMember hz := by
    apply Subtype.ext
    exact congrArg (fun glue => Sum.inr (Sum.inl glue)) hcandidate
  rw [hface]
  rfl
noncomputable def rxOriginalBoundaryZOldQTarget
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (candidate : RXOldZFace P) (corner : Two)
    (hx : rxFaceX P S (Sum.inr (Sum.inr candidate)) =
      rxOriginalBoundaryZXCoordinate P S x copy z member) :
    {target : RXOriginalBoundaryZTarget P x z //
      rxOriginalBoundaryZTargetBoundaryVertex
          P A4 S x copy z member target =
        xBoundaryEdgeStart (rxReplacementPresentation P S)
          (rxOriginalBoundaryZXCoordinate P S x copy z member)
          (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
            (rxOriginalBoundaryZXCoordinate P S x copy z member)
            (rxOriginalBoundaryZIncidentXStarFace P S x copy z member
              (Sum.inr (Sum.inr candidate)) hx) corner)} := by
  have hcandidate : candidate =
      ((rxOriginalBoundaryZRootFace P A4 x z member).1, copy) :=
    rxOriginalBoundaryZOldFace_cases P R A4 S x copy z member candidate
      (by simpa [rxFaceX] using hx)
  let face := rxOriginalBoundaryZRootFace P A4 x z member
  let hz := rxOriginalBoundaryZRootFace_z P A4 x z member
  refine ⟨.oldQ face hz corner, ?_⟩
  have hface : rxOriginalBoundaryZIncidentXStarFace P S x copy z member
        (Sum.inr (Sum.inr candidate)) hx =
      rxOriginalBoundaryZOldFaceXStarFaceAt
        P A4 S x copy z member face hz := by
    apply Subtype.ext
    exact congrArg (fun old => Sum.inr (Sum.inr old)) hcandidate
  rw [hface]
  rfl
noncomputable def rxOriginalBoundaryZOldZTarget
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (candidate : RXOldZFace P)
    (hx : rxFaceX P S (Sum.inr (Sum.inr candidate)) =
      rxOriginalBoundaryZXCoordinate P S x copy z member) :
    {target : RXOriginalBoundaryZTarget P x z //
      rxOriginalBoundaryZTargetBoundaryVertex
          P A4 S x copy z member target =
        xBoundaryEdgeEnd (rxReplacementPresentation P S)
          (rxOriginalBoundaryZXCoordinate P S x copy z member)
          (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
            (rxOriginalBoundaryZXCoordinate P S x copy z member)
            (rxOriginalBoundaryZIncidentXStarFace P S x copy z member
              (Sum.inr (Sum.inr candidate)) hx) 0)} := by
  have hcandidate : candidate =
      ((rxOriginalBoundaryZRootFace P A4 x z member).1, copy) :=
    rxOriginalBoundaryZOldFace_cases P R A4 S x copy z member candidate
      (by simpa [rxFaceX] using hx)
  let face := rxOriginalBoundaryZRootFace P A4 x z member
  let hz := rxOriginalBoundaryZRootFace_z P A4 x z member
  refine ⟨.oldZ face hz, ?_⟩
  have hface : rxOriginalBoundaryZIncidentXStarFace P S x copy z member
        (Sum.inr (Sum.inr candidate)) hx =
      rxOriginalBoundaryZOldFaceXStarFaceAt
        P A4 S x copy z member face hz := by
    apply Subtype.ext
    exact congrArg (fun old => Sum.inr (Sum.inr old)) hcandidate
  rw [hface]
  rfl
noncomputable def rxOriginalBoundaryZFaceQTarget
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (candidate : RXFace P S) (corner : Two)
    (hx : rxFaceX P S candidate =
      rxOriginalBoundaryZXCoordinate P S x copy z member) :
    {target : RXOriginalBoundaryZTarget P x z //
      rxOriginalBoundaryZTargetBoundaryVertex
          P A4 S x copy z member target =
        xBoundaryEdgeStart (rxReplacementPresentation P S)
          (rxOriginalBoundaryZXCoordinate P S x copy z member)
          (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
            (rxOriginalBoundaryZXCoordinate P S x copy z member)
            (rxOriginalBoundaryZIncidentXStarFace
              P S x copy z member candidate hx) corner)} := by
  rcases candidate with candidateLocal | candidateGlue | candidateOld
  · rcases candidateLocal with ⟨candidateX, localCell, material⟩
    have howner : candidateX = x := by
      rcases localCell with copyFace | rectangle
      · simpa [rxFaceX, localFaceX, rxOriginalBoundaryZXCoordinate] using congrArg Sigma.fst hx
      · simpa [rxFaceX, localFaceX, rxOriginalBoundaryZXCoordinate] using congrArg Sigma.fst hx
    subst candidateX
    rcases localCell with copyFace | rectangle
    · rcases copyFace with ⟨candidateCopy, candidateFace, column, row⟩
      rcases material with ⟨first, second⟩
      exact rxOriginalBoundaryZSmallQTarget P A4 S x copy z member
        x candidateCopy candidateFace column row first second corner hx
    · rcases rectangle with ⟨raw, boundaryMember⟩
      rcases raw with original | interior
      · rcases original with ⟨starEdge, segment⟩
        rcases starEdge with ⟨rawEdge, starMember⟩
        rcases rawEdge with radial | edge
        · simp [subdivisionBoundaryEdgeMember,
            xStarBoundaryEdgeMember] at boundaryMember
        · rcases material with ⟨candidateCopy, endpoint⟩
          exact rxOriginalBoundaryZRectangleQTarget
            P A4 S x copy z member edge starMember segment boundaryMember
              candidateCopy endpoint corner hx
      · simp [subdivisionBoundaryEdgeMember] at boundaryMember
  · rcases candidateGlue with
      ⟨⟨⟨candidateX, q⟩, hxq⟩, qEdge, endpoint⟩
    have howner : candidateX = x := congrArg Sigma.fst hx
    subst candidateX
    rcases qEdge with copyEdge | vertical
    · rcases copyEdge with ⟨candidateCopy, edge, segment⟩
      exact rxOriginalBoundaryZGlueQTarget P A4 S x copy z member
        q hxq edge segment candidateCopy endpoint corner hx
    · exact rxOriginalBoundaryZVerticalGlueQTarget
        P A4 S x copy z member q hxq vertical endpoint corner hx
  · exact rxOriginalBoundaryZOldQTarget
      P R A4 S x copy z member candidateOld corner hx
noncomputable def rxOriginalBoundaryZFaceZTarget
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (candidate : RXFace P S)
    (hx : rxFaceX P S candidate =
      rxOriginalBoundaryZXCoordinate P S x copy z member) :
    {target : RXOriginalBoundaryZTarget P x z //
      rxOriginalBoundaryZTargetBoundaryVertex
          P A4 S x copy z member target =
        xBoundaryEdgeEnd (rxReplacementPresentation P S)
          (rxOriginalBoundaryZXCoordinate P S x copy z member)
          (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
            (rxOriginalBoundaryZXCoordinate P S x copy z member)
            (rxOriginalBoundaryZIncidentXStarFace
              P S x copy z member candidate hx) 0)} := by
  rcases candidate with candidateLocal | candidateGlue | candidateOld
  · rcases candidateLocal with ⟨candidateX, localCell, material⟩
    have howner : candidateX = x := by
      rcases localCell with copyFace | rectangle
      · simpa [rxFaceX, localFaceX, rxOriginalBoundaryZXCoordinate] using congrArg Sigma.fst hx
      · simpa [rxFaceX, localFaceX, rxOriginalBoundaryZXCoordinate] using congrArg Sigma.fst hx
    subst candidateX
    rcases localCell with copyFace | rectangle
    · rcases copyFace with ⟨candidateCopy, candidateFace, column, row⟩
      rcases material with ⟨first, second⟩
      exact rxOriginalBoundaryZSmallZTarget P A4 S x copy z member
        x candidateCopy candidateFace column row first second hx
    · rcases rectangle with ⟨raw, boundaryMember⟩
      rcases raw with original | interior
      · rcases original with ⟨starEdge, segment⟩
        rcases starEdge with ⟨rawEdge, starMember⟩
        rcases rawEdge with radial | edge
        · simp [subdivisionBoundaryEdgeMember,
            xStarBoundaryEdgeMember] at boundaryMember
        · rcases material with ⟨candidateCopy, endpoint⟩
          exact rxOriginalBoundaryZRectangleZTarget
            P A4 S x copy z member edge starMember segment boundaryMember
              candidateCopy endpoint hx
      · simp [subdivisionBoundaryEdgeMember] at boundaryMember
  · rcases candidateGlue with
      ⟨⟨⟨candidateX, q⟩, hxq⟩, qEdge, endpoint⟩
    have howner : candidateX = x := congrArg Sigma.fst hx
    subst candidateX
    rcases qEdge with copyEdge | vertical
    · rcases copyEdge with ⟨candidateCopy, edge, segment⟩
      exact rxOriginalBoundaryZGlueZTarget P A4 S x copy z member
        q hxq edge segment candidateCopy endpoint hx
    · exact rxOriginalBoundaryZVerticalGlueZTarget
        P A4 S x copy z member q hxq vertical endpoint hx
  · exact rxOriginalBoundaryZOldZTarget
      P R A4 S x copy z member candidateOld hx
theorem rxOriginalBoundaryZIncidentEndpointOne
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (x : P.X) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true) :
    (A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2
      |>.xBoundaryIncidentEdge x ⟨Vertex.z z, member⟩).1.2 = 1 := by
  let A2 := A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2
  let vertex : XStarBoundaryVertex P x := ⟨Vertex.z z, member⟩
  generalize hselected : A2.xBoundaryIncidentEdge x vertex = selected
  rcases selected with ⟨⟨boundary, endpoint⟩, hendpoint⟩
  fin_cases endpoint
  · have hraw := congrArg Subtype.val hendpoint
    rcases boundary with ⟨raw, boundaryMember⟩
    rcases raw with impossible | edge
    · simp [xStarBoundaryEdgeMember] at boundaryMember
    · change Vertex.q edge.1.1 = Vertex.z z at hraw
      cases hraw
  · rfl
theorem rxOriginalBoundaryZRootBoundaryEdge_eq_selected
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (x : P.X) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true) :
    rxOriginalBoundaryZRootBoundaryEdge P A4 x z member =
      (A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2
        |>.xBoundaryIncidentEdge x ⟨Vertex.z z, member⟩).1.1 := by
  apply Subtype.ext
  exact rxOriginalBoundaryZRootOwnerFromIncident_edge P A4 x z member
    (A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2
      |>.xBoundaryIncidentEdge x ⟨Vertex.z z, member⟩)
theorem rxDoubleCylinderVertexIncidentEdge_originalZ
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true) :
    (rxDoubleCylinderVertexIncidentEdge P
      A4.toTannerSquareAdmissibleV3 x S
      (copy, Sum.inl ⟨Vertex.z z, by
        simpa [xStarBoundaryVertexMember, xStarVertexMember] using member⟩)).1 =
      (Sum.inl (copy,
        (rxOriginalBoundaryZRootRectangle P A4 S x z member).1), 1) := by
  classical
  let A2 := A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2
  let vertex : XStarBoundaryVertex P x := ⟨Vertex.z z, member⟩
  have hone : (A2.xBoundaryIncidentEdge x vertex).1.2 = 1 :=
    rxOriginalBoundaryZIncidentEndpointOne P A4 x z member
  have hnormalized := subdivisionBoundaryIncidentEdge_original_one
    P A2 x S vertex hone
  have hnormalized' :
      (subdivisionBoundaryIncidentEdge P
        A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2 x S
        (subdivisionOriginalBoundaryVertex P x S ⟨Vertex.z z, member⟩)).1 =
        (subdivisionOriginalBoundaryEdge P x S
          (A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2
            |>.xBoundaryIncidentEdge x ⟨Vertex.z z, member⟩).1.1
          ⟨S.half - 1, by have := S.half_pos; omega⟩, 1) := by
    simpa [A2, vertex] using hnormalized
  have hedge := congrArg (fun owned => owned.1.1) hnormalized'
  have hendpoint := congrArg Prod.snd hnormalized'
  simp only [rxDoubleCylinderVertexIncidentEdge,
    rxSubdivisionVertexIncidentEdge]
  rw [show
    (subdivisionBoundaryIncidentEdge P
      A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2 x S
      (subdivisionOriginalBoundaryVertex P x S ⟨Vertex.z z, by
        simpa [xStarBoundaryVertexMember, xStarVertexMember] using member⟩)).1.2 =
      1 by simpa using hendpoint]
  apply Prod.ext
  · apply congrArg Sum.inl
    apply Prod.ext
    · rfl
    · rw [show
        (subdivisionBoundaryIncidentEdge P
          A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2 x S
          (subdivisionOriginalBoundaryVertex P x S ⟨Vertex.z z, by
            simpa [xStarBoundaryVertexMember, xStarVertexMember]
              using member⟩)).1.1.1 =
          (subdivisionOriginalBoundaryEdge P x S
            (A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2
              |>.xBoundaryIncidentEdge x ⟨Vertex.z z, member⟩).1.1
            ⟨S.half - 1, by have := S.half_pos; omega⟩).1 by
          simpa using hedge]
      simp only [rxOriginalBoundaryZRootRectangle,
        subdivisionOriginalBoundaryEdge]
      rw [rxOriginalBoundaryZRootBoundaryEdge_eq_selected
        P A4 x z member]
      apply congrArg Sum.inl
      apply Prod.ext
      · rfl
      · apply Fin.ext
        rfl
  · rfl
theorem rxReplacementXBoundaryRoot_originalZ
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true) :
    rxReplacementXBoundaryRoot P A4.toTannerSquareAdmissibleV3 S
        (rxOriginalBoundaryZXCoordinate P S x copy z member) =
      xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z member)
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          (rxOriginalBoundaryZXCoordinate P S x copy z member)
          (rxOriginalBoundaryZRootXStarFace P A4 S x copy z member) 0) := by
  change rxReplacementXBoundaryRoot P A4.toTannerSquareAdmissibleV3 S
      ⟨x, (copy, Sum.inl ⟨Vertex.z z, by
        simpa [xStarBoundaryVertexMember, xStarVertexMember] using member⟩)⟩ = _
  apply Subtype.ext
  rw [rxReplacementXBoundaryRoot_value]
  rw [rxDoubleCylinderVertexIncidentEdge_originalZ
    P A4 S x copy z member]
  rfl
noncomputable def rxOriginalBoundaryZTargetBoundaryPathHistorical
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (target : RXOriginalBoundaryZTarget P x z) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z member))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z member))
      (rxReplacementXBoundaryRoot P
        A4.toTannerSquareAdmissibleV3 S
        (rxOriginalBoundaryZXCoordinate P S x copy z member))
      (rxOriginalBoundaryZTargetBoundaryVertex
        P A4 S x copy z member target) := by
  rw [rxReplacementXBoundaryRoot_originalZ P A4 S x copy z member]
  exact rxOriginalBoundaryZTargetBoundaryPath
    P A4 S x copy z member target
theorem rxOriginalBoundaryZRawSmallZ_normalize
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (z : P.Z)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (candidateX : P.X) (candidateCopy : Two)
    (face : XStarFace P candidateX) (column row : Fin S.half)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z oldMember)
      (Vertex.z (Sum.inl (Sum.inl
        ⟨candidateX, Sum.inl (candidateCopy, (face, column, row))⟩))) = true) :
    candidateX = x ∧
      ∀ howner : candidateX = x,
        let transportedFace : XStarFace P x := howner ▸ face
        P.faceZ transportedFace.1 = z ∧
          (Sum.inl (Sum.inl
            ⟨candidateX, Sum.inl (candidateCopy, (face, column, row))⟩) :
              RX2 P S) =
            localFaceZ P S
              (rxOriginalBoundaryZLocalFaceAt
                P S x copy transportedFace) := by
  classical
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl]
    at member
  rw [decide_eq_true_eq] at member
  obtain ⟨candidate, hx, hzTag⟩ := member
  have hx' : rxFaceX P S candidate =
      rxOriginalBoundaryZXCoordinate P S x copy z oldMember := by
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
    rcases material with ⟨first, second⟩
    have howner : candidateX = x := by
      simpa [rxFaceX, localFaceX, rxOriginalBoundaryZXCoordinate] using congrArg Sigma.fst hx'
    subst candidateX
    refine ⟨rfl, ?_⟩
    intro howner'
    have hproof : howner' = (rfl : x = x) := Subsingleton.elim _ _
    cases hproof
    obtain ⟨hz, hcandidate⟩ := rxOriginalBoundaryZSmallFace_eq
      P S x copy z oldMember candidateCopy face column row first second
        (by simpa [rxFaceX] using hx')
    refine ⟨hz, ?_⟩
    simpa only [localFaceZ] using
      congrArg (localFaceZ P S) hcandidate
  · cases hzTag
  · cases hzTag
noncomputable def rxOriginalBoundaryZRawSmallZPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (candidateX : P.X) (candidateCopy : Two)
    (face : XStarFace P candidateX) (column row : Fin S.half)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z oldMember)
      (Vertex.z (Sum.inl (Sum.inl
        ⟨candidateX, Sum.inl (candidateCopy, (face, column, row))⟩))) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      (rxReplacementXBoundaryRoot P
        A4.toTannerSquareAdmissibleV3 S
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      ⟨Vertex.z (Sum.inl (Sum.inl
        ⟨candidateX, Sum.inl (candidateCopy, (face, column, row))⟩)),
        member⟩ := by
  obtain ⟨howner, hnormalize⟩ := rxOriginalBoundaryZRawSmallZ_normalize
    P S x copy z oldMember candidateX candidateCopy face column row member
  let transportedFace : XStarFace P x := howner ▸ face
  obtain ⟨hz, hraw⟩ := hnormalize howner
  let target : RXOriginalBoundaryZTarget P x z :=
    .localZ transportedFace hz 0
  let path := rxOriginalBoundaryZTargetBoundaryPathHistorical
    P A4 S x copy z oldMember target
  have htarget : rxOriginalBoundaryZTargetBoundaryVertex
        P A4 S x copy z oldMember target =
      ⟨Vertex.z (Sum.inl (Sum.inl
        ⟨candidateX, Sum.inl (candidateCopy, (face, column, row))⟩)),
        member⟩ := by
    apply Subtype.ext
    exact congrArg Vertex.z hraw.symm
  exact htarget ▸ path
theorem rxOriginalBoundaryZRawRectangleZ_normalize
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (z : P.Z)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (candidateX : P.X) (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P candidateX (Sum.inr edge) = true)
    (segment : Fin S.half)
    (boundaryMember : subdivisionBoundaryEdgeMember P candidateX S
      (Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment)) = true)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z oldMember)
      (Vertex.z (Sum.inl (Sum.inl
        ⟨candidateX, Sum.inr
          ⟨Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment),
            boundaryMember⟩⟩))) = true) :
    candidateX = x ∧
      ∀ howner : candidateX = x,
        let transportedEdge : QZEdge P := edge
        let transportedMember : xStarEdgeMember P x
            (Sum.inr transportedEdge) = true := howner ▸ edgeMember
        transportedEdge.1.2 = z ∧
          (Sum.inl (Sum.inl
            ⟨candidateX, Sum.inr
              ⟨Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment),
                boundaryMember⟩⟩) : RX2 P S) =
            localFaceZ P S
              (rxOriginalBoundaryZRectangleLocalFaceAt
                P S x copy transportedEdge transportedMember) := by
  classical
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl]
    at member
  rw [decide_eq_true_eq] at member
  obtain ⟨candidate, hx, hzTag⟩ := member
  have hx' : rxFaceX P S candidate =
      rxOriginalBoundaryZXCoordinate P S x copy z oldMember := by
    simp only [xStarFaceMember, decide_eq_true_eq] at hx
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
    exact hx
  rcases candidate with candidateLocal | candidateGlue | candidateOld
  · rcases candidateLocal with ⟨ownerX, localCell, material⟩
    have hcell :
        (⟨candidateX, Sum.inr
          ⟨Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment),
            boundaryMember⟩⟩ :
            Σ ownerX : P.X, DoubleCylinderFace P ownerX S) =
        ⟨ownerX, localCell⟩ := by
      exact Sum.inl.inj (Sum.inl.inj hzTag)
    cases hcell
    rcases material with ⟨candidateCopy, endpoint⟩
    have howner : candidateX = x := by
      simpa [rxFaceX, localFaceX, rxOriginalBoundaryZXCoordinate] using congrArg Sigma.fst hx'
    subst candidateX
    refine ⟨rfl, ?_⟩
    intro howner'
    have hproof : howner' = (rfl : x = x) := Subsingleton.elim _ _
    cases hproof
    obtain ⟨hz, hcandidate⟩ := rxOriginalBoundaryZRectangleFace_eq
      P S x copy z oldMember edge edgeMember segment boundaryMember
        candidateCopy endpoint (by simpa [rxFaceX] using hx')
    refine ⟨hz, ?_⟩
    simpa only [localFaceZ] using
      congrArg (localFaceZ P S) hcandidate
  · cases hzTag
  · cases hzTag
noncomputable def rxOriginalBoundaryZRawRectangleZPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (candidateX : P.X) (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P candidateX (Sum.inr edge) = true)
    (segment : Fin S.half)
    (boundaryMember : subdivisionBoundaryEdgeMember P candidateX S
      (Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment)) = true)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z oldMember)
      (Vertex.z (Sum.inl (Sum.inl
        ⟨candidateX, Sum.inr
          ⟨Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment),
            boundaryMember⟩⟩))) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      (rxReplacementXBoundaryRoot P
        A4.toTannerSquareAdmissibleV3 S
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      ⟨Vertex.z (Sum.inl (Sum.inl
        ⟨candidateX, Sum.inr
          ⟨Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment),
            boundaryMember⟩⟩)), member⟩ := by
  obtain ⟨howner, hnormalize⟩ :=
    rxOriginalBoundaryZRawRectangleZ_normalize P S x copy z oldMember
      candidateX edge edgeMember segment boundaryMember member
  subst candidateX
  obtain ⟨hz, hraw⟩ := hnormalize rfl
  let target : RXOriginalBoundaryZTarget P x z :=
    .rectangleZ edge edgeMember hz
  let path := rxOriginalBoundaryZTargetBoundaryPathHistorical
    P A4 S x copy z oldMember target
  have htarget : rxOriginalBoundaryZTargetBoundaryVertex
        P A4 S x copy z oldMember target =
      ⟨Vertex.z (Sum.inl (Sum.inl
        ⟨x, Sum.inr
          ⟨Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment),
            boundaryMember⟩⟩)), member⟩ := by
    apply Subtype.ext
    exact congrArg Vertex.z hraw.symm
  exact htarget ▸ path
theorem rxOriginalBoundaryZRawGlueZ_normalize
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (q : P.Q) (candidateCopy : Two) (edge : QStarEdge P q)
    (segment : Fin S.half)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z oldMember)
      (Vertex.z (Sum.inl (Sum.inr
        ⟨q, Sum.inl (candidateCopy, (edge, segment))⟩))) = true) :
    P.xq x q = true ∧
      ∀ hxq : P.xq x q = true,
        edge.1 = z ∧
          (Sum.inl (Sum.inr
            ⟨q, Sum.inl (candidateCopy, (edge, segment))⟩) : RX2 P S) =
            glueFaceZ P S
              (rxOriginalBoundaryZGlueFaceAt P A4 S x copy
                (rxOriginalBoundaryZGlueEdge P q edge)
                (rxOriginalBoundaryZGlueEdge_member P x q hxq edge)) := by
  classical
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl]
    at member
  rw [decide_eq_true_eq] at member
  obtain ⟨candidate, hx, hzTag⟩ := member
  have hx' : rxFaceX P S candidate =
      rxOriginalBoundaryZXCoordinate P S x copy z oldMember := by
    simp only [xStarFaceMember, decide_eq_true_eq] at hx
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
    exact hx
  rcases candidate with candidateLocal | candidateGlue | candidateOld
  · cases hzTag
  · rcases candidateGlue with ⟨a, qEdge, endpoint⟩
    have hqEdge : (⟨q, Sum.inl (candidateCopy, (edge, segment))⟩ :
          Σ q : P.Q, QDoubleCylinderEdge P q S) =
        ⟨a.1.2, qEdge⟩ := by
      exact Sum.inr.inj (Sum.inl.inj hzTag)
    cases hqEdge
    rcases a with ⟨⟨oldX, oldQ⟩, hxq⟩
    have howner : oldX = x := congrArg Sigma.fst hx'
    subst oldX
    refine ⟨hxq, ?_⟩
    intro hxq'
    have hproof : hxq = hxq' := Subsingleton.elim _ _
    cases hproof
    obtain ⟨hz, hcandidate⟩ := rxOriginalBoundaryZGlueFace_eq
      P A4 S x copy z oldMember oldQ hxq edge segment candidateCopy endpoint
        (by simpa [rxFaceX] using hx')
    refine ⟨hz, ?_⟩
    simpa only [glueFaceZ] using congrArg (glueFaceZ P S) hcandidate
  · cases hzTag
noncomputable def rxOriginalBoundaryZRawGlueZPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (q : P.Q) (candidateCopy : Two) (edge : QStarEdge P q)
    (segment : Fin S.half)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z oldMember)
      (Vertex.z (Sum.inl (Sum.inr
        ⟨q, Sum.inl (candidateCopy, (edge, segment))⟩))) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      (rxReplacementXBoundaryRoot P
        A4.toTannerSquareAdmissibleV3 S
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      ⟨Vertex.z (Sum.inl (Sum.inr
        ⟨q, Sum.inl (candidateCopy, (edge, segment))⟩)), member⟩ := by
  obtain ⟨hxq, hnormalize⟩ := rxOriginalBoundaryZRawGlueZ_normalize
    P A4 S x copy z oldMember q candidateCopy edge segment member
  obtain ⟨hz, hraw⟩ := hnormalize hxq
  let oldEdge := rxOriginalBoundaryZGlueEdge P q edge
  let oldEdgeMember := rxOriginalBoundaryZGlueEdge_member P x q hxq edge
  let target : RXOriginalBoundaryZTarget P x z :=
    .glueZ oldEdge oldEdgeMember hz
  let path := rxOriginalBoundaryZTargetBoundaryPathHistorical
    P A4 S x copy z oldMember target
  have htarget : rxOriginalBoundaryZTargetBoundaryVertex
        P A4 S x copy z oldMember target =
      ⟨Vertex.z (Sum.inl (Sum.inr
        ⟨q, Sum.inl (candidateCopy, (edge, segment))⟩)), member⟩ := by
    apply Subtype.ext
    exact congrArg Vertex.z hraw.symm
  exact htarget ▸ path
theorem rxOriginalBoundaryZRawVerticalGlueZ_normalize
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (q : P.Q) (edge : QStarEdge P q)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z oldMember)
      (Vertex.z (Sum.inl (Sum.inr ⟨q, Sum.inr edge⟩))) = true) :
    P.xq x q = true ∧
      ∀ hxq : P.xq x q = true,
        edge.1 = z ∧
          (Sum.inl (Sum.inr ⟨q, Sum.inr edge⟩) : RX2 P S) =
            glueFaceZ P S
              (rxOriginalBoundaryZVerticalGlueFaceAt P A4 S x copy
                (rxOriginalBoundaryZGlueEdge P q edge)
                (rxOriginalBoundaryZGlueEdge_member P x q hxq edge)) := by
  classical
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl]
    at member
  rw [decide_eq_true_eq] at member
  obtain ⟨candidate, hx, hzTag⟩ := member
  have hx' : rxFaceX P S candidate =
      rxOriginalBoundaryZXCoordinate P S x copy z oldMember := by
    simp only [xStarFaceMember, decide_eq_true_eq] at hx
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
    exact hx
  rcases candidate with candidateLocal | candidateGlue | candidateOld
  · cases hzTag
  · rcases candidateGlue with ⟨a, qEdge, endpoint⟩
    have hqEdge : (⟨q, Sum.inr edge⟩ :
          Σ q : P.Q, QDoubleCylinderEdge P q S) =
        ⟨a.1.2, qEdge⟩ := by
      exact Sum.inr.inj (Sum.inl.inj hzTag)
    cases hqEdge
    rcases a with ⟨⟨oldX, oldQ⟩, hxq⟩
    have howner : oldX = x := congrArg Sigma.fst hx'
    subst oldX
    refine ⟨hxq, ?_⟩
    intro hxq'
    have hproof : hxq = hxq' := Subsingleton.elim _ _
    cases hproof
    obtain ⟨hz, _, hcandidate⟩ :=
      rxOriginalBoundaryZVerticalGlueFace_eq
        P A4 S x copy z oldMember oldQ hxq edge endpoint
          (by simpa [rxFaceX] using hx')
    refine ⟨hz, ?_⟩
    simpa only [glueFaceZ] using congrArg (glueFaceZ P S) hcandidate
  · cases hzTag
noncomputable def rxOriginalBoundaryZRawVerticalGlueZPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (q : P.Q) (edge : QStarEdge P q)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z oldMember)
      (Vertex.z (Sum.inl (Sum.inr ⟨q, Sum.inr edge⟩))) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      (rxReplacementXBoundaryRoot P
        A4.toTannerSquareAdmissibleV3 S
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      ⟨Vertex.z (Sum.inl (Sum.inr ⟨q, Sum.inr edge⟩)), member⟩ := by
  obtain ⟨hxq, hnormalize⟩ :=
    rxOriginalBoundaryZRawVerticalGlueZ_normalize
      P A4 S x copy z oldMember q edge member
  obtain ⟨hz, hraw⟩ := hnormalize hxq
  let oldEdge := rxOriginalBoundaryZGlueEdge P q edge
  let oldEdgeMember := rxOriginalBoundaryZGlueEdge_member P x q hxq edge
  let target : RXOriginalBoundaryZTarget P x z :=
    .verticalGlueZ oldEdge oldEdgeMember hz
  let path := rxOriginalBoundaryZTargetBoundaryPathHistorical
    P A4 S x copy z oldMember target
  have htarget : rxOriginalBoundaryZTargetBoundaryVertex
        P A4 S x copy z oldMember target =
      ⟨Vertex.z (Sum.inl (Sum.inr ⟨q, Sum.inr edge⟩)), member⟩ := by
    apply Subtype.ext
    exact congrArg Vertex.z hraw.symm
  exact htarget ▸ path
theorem rxOriginalBoundaryZRawOldZ_normalize
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (candidateZ : P.Z) (candidateCopy : Two)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z oldMember)
      (Vertex.z (Sum.inr (candidateZ, candidateCopy))) = true) :
    (Sum.inr (candidateZ, candidateCopy) : RX2 P S) =
      oldZFaceZ P S
        ((rxOriginalBoundaryZRootFace P A4 x z oldMember).1, copy) := by
  classical
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl]
    at member
  rw [decide_eq_true_eq] at member
  obtain ⟨candidate, hx, hzTag⟩ := member
  have hx' : rxFaceX P S candidate =
      rxOriginalBoundaryZXCoordinate P S x copy z oldMember := by
    simp only [xStarFaceMember, decide_eq_true_eq] at hx
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
    exact hx
  rcases candidate with candidateLocal | candidateGlue | candidateOld
  · cases hzTag
  · cases hzTag
  · have hcandidate : candidateOld =
        ((rxOriginalBoundaryZRootFace P A4 x z oldMember).1, copy) :=
      rxOriginalBoundaryZOldFace_cases
        P R A4 S x copy z oldMember candidateOld
          (by simpa [rxFaceX] using hx')
    rw [← hcandidate]
    simp only [rxFaceZ, oldZFaceZ] at hzTag
    exact hzTag
noncomputable def rxOriginalBoundaryZRawOldZPath
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (candidateZ : P.Z) (candidateCopy : Two)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z oldMember)
      (Vertex.z (Sum.inr (candidateZ, candidateCopy))) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      (rxReplacementXBoundaryRoot P
        A4.toTannerSquareAdmissibleV3 S
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      ⟨Vertex.z (Sum.inr (candidateZ, candidateCopy)), member⟩ := by
  have hraw := rxOriginalBoundaryZRawOldZ_normalize
    P R A4 S x copy z oldMember candidateZ candidateCopy member
  let face := rxOriginalBoundaryZRootFace P A4 x z oldMember
  let hz := rxOriginalBoundaryZRootFace_z P A4 x z oldMember
  let target : RXOriginalBoundaryZTarget P x z := .oldZ face hz
  let path := rxOriginalBoundaryZTargetBoundaryPathHistorical
    P A4 S x copy z oldMember target
  have htarget : rxOriginalBoundaryZTargetBoundaryVertex
        P A4 S x copy z oldMember target =
      ⟨Vertex.z (Sum.inr (candidateZ, candidateCopy)), member⟩ := by
    apply Subtype.ext
    exact congrArg Vertex.z hraw.symm
  exact htarget ▸ path
noncomputable def rxOriginalBoundaryZRawZPath
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (newZ : RX2 P S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z oldMember)
      (Vertex.z newZ) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      (rxReplacementXBoundaryRoot P
        A4.toTannerSquareAdmissibleV3 S
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      ⟨Vertex.z newZ, member⟩ := by
  rcases newZ with localOrGlue | old
  · rcases localOrGlue with localTag | glue
    · rcases localTag with ⟨candidateX, localCell⟩
      rcases localCell with copyFace | rectangle
      · rcases copyFace with ⟨candidateCopy, face, column, row⟩
        exact rxOriginalBoundaryZRawSmallZPath
          P A4 S x copy z oldMember candidateX candidateCopy
            face column row member
      · rcases rectangle with ⟨rawBoundaryEdge, boundaryMember⟩
        rcases rawBoundaryEdge with original | interior
        · rcases original with ⟨starEdge, segment⟩
          rcases starEdge with ⟨rawEdge, edgeMember⟩
          rcases rawEdge with xqEdge | qzEdge
          · simp [subdivisionBoundaryEdgeMember,
              xStarBoundaryEdgeMember] at boundaryMember
          · exact rxOriginalBoundaryZRawRectangleZPath
              P A4 S x copy z oldMember candidateX qzEdge edgeMember
                segment boundaryMember member
        · simp [subdivisionBoundaryEdgeMember] at boundaryMember
    · rcases glue with ⟨q, qEdge⟩
      rcases qEdge with copied | vertical
      · rcases copied with ⟨candidateCopy, edge, segment⟩
        exact rxOriginalBoundaryZRawGlueZPath
          P A4 S x copy z oldMember q candidateCopy edge segment member
      · exact rxOriginalBoundaryZRawVerticalGlueZPath
          P A4 S x copy z oldMember q vertical member
  · rcases old with ⟨candidateZ, candidateCopy⟩
    exact rxOriginalBoundaryZRawOldZPath
      P R A4 S x copy z oldMember candidateZ candidateCopy member
theorem rxOriginalBoundaryZRawQEndpoint_normalize
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (q : P.Q) (candidateCopy : Two) (edge : QStarEdge P q)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z oldMember)
      (Vertex.q (Sum.inr
        ⟨q, (candidateCopy, Sum.inl (Sum.inr edge))⟩)) = true) :
    P.xq x q = true ∧
      ∀ hxq : P.xq x q = true,
        edge.1 = z ∧
          (Sum.inr ⟨q,
            (candidateCopy, Sum.inl (Sum.inr edge))⟩ : RX1 P S) =
            glueFaceQ1 P S
              (rxOriginalBoundaryZGlueFaceAt P A4 S x copy
                (rxOriginalBoundaryZGlueEdge P q edge)
                (rxOriginalBoundaryZGlueEdge_member P x q hxq edge)) := by
  classical
  let endpointData : RX1 P S → Option (P.Q × Two × P.Z)
    | Sum.inr ⟨ownerQ, (ownerCopy, Sum.inl (Sum.inr ownerEdge))⟩ =>
        some (ownerQ, ownerCopy, ownerEdge.1)
    | _ => none
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceQ = rxFaceQ P S from rfl]
    at member
  rw [decide_eq_true_eq] at member
  obtain ⟨candidate, hx, hqTag⟩ := member
  have hx' : rxFaceX P S candidate =
      rxOriginalBoundaryZXCoordinate P S x copy z oldMember := by
    simp only [xStarFaceMember, decide_eq_true_eq] at hx
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
    exact hx
  rcases candidate with candidateLocal | candidateGlue | candidateOld
  · rcases hqTag with hqTag | hqTag <;> cases hqTag
  · rcases candidateGlue with ⟨a, qEdge, endpoint⟩
    rcases hqTag with hqTag | hqTag
    · cases hqTag
    · rcases a with ⟨⟨oldX, oldQ⟩, oldHXQ⟩
      have howner : oldX = x := congrArg Sigma.fst hx'
      subst oldX
      rcases qEdge with copied | vertical
      · rcases copied with ⟨glueCopy, glueEdge, segment⟩
        obtain ⟨hz, hcandidate⟩ := rxOriginalBoundaryZGlueFace_eq
          P A4 S x copy z oldMember oldQ oldHXQ glueEdge segment
            glueCopy endpoint (by simpa [rxFaceX] using hx')
        have hraw :
            (Sum.inr ⟨q,
              (candidateCopy, Sum.inl (Sum.inr edge))⟩ : RX1 P S) =
              glueFaceQ1 P S
                (rxOriginalBoundaryZGlueFaceAt P A4 S x copy
                  (rxOriginalBoundaryZGlueEdge P oldQ glueEdge)
                  (rxOriginalBoundaryZGlueEdge_member
                    P x oldQ oldHXQ glueEdge)) := by
          exact hqTag.trans (congrArg (glueFaceQ1 P S) hcandidate)
        have hlast : S.half - 1 + 1 = S.half := by
          have := S.half_pos
          omega
        have hdata : (q, candidateCopy, edge.1) =
            (oldQ, copy, glueEdge.1) := by
          simpa [endpointData, rxOriginalBoundaryZGlueFaceAt,
            rxOriginalBoundaryZGlueEdge,
            rxStarEdgeInteriorBoundaryQStarEdge, rxStarEdgeInteriorBoundaryXQEdge,
            glueFaceQ1, edgeEndpoint, qDoubleCylinderEdgeEnd,
            qSubdivisionEdgeEnd, qStarEdgeEnd,
            rxStarEdgeInteriorLastIndex, hlast] using
              congrArg endpointData hraw
        have hq : q = oldQ := congrArg Prod.fst hdata
        have hcopy : candidateCopy = copy :=
          congrArg (fun value => value.2.1) hdata
        have hzEdge : edge.1 = glueEdge.1 :=
          congrArg (fun value => value.2.2) hdata
        subst oldQ
        subst candidateCopy
        have hedge : edge = glueEdge := Subtype.ext hzEdge
        subst glueEdge
        refine ⟨oldHXQ, ?_⟩
        intro hxq
        have hproof : oldHXQ = hxq := Subsingleton.elim _ _
        cases hproof
        exact ⟨hz, by simpa using hraw⟩
      · obtain ⟨hz, _, hcandidate⟩ :=
          rxOriginalBoundaryZVerticalGlueFace_eq
            P A4 S x copy z oldMember oldQ oldHXQ vertical endpoint
              (by simpa [rxFaceX] using hx')
        have hrawVertical :
            (Sum.inr ⟨q,
              (candidateCopy, Sum.inl (Sum.inr edge))⟩ : RX1 P S) =
              glueFaceQ1 P S
                (rxOriginalBoundaryZVerticalGlueFaceAt P A4 S x copy
                  (rxOriginalBoundaryZGlueEdge P oldQ vertical)
                  (rxOriginalBoundaryZGlueEdge_member
                    P x oldQ oldHXQ vertical)) := by
          exact hqTag.trans (congrArg (glueFaceQ1 P S) hcandidate)
        have hraw :
            (Sum.inr ⟨q,
              (candidateCopy, Sum.inl (Sum.inr edge))⟩ : RX1 P S) =
              glueFaceQ1 P S
                (rxOriginalBoundaryZGlueFaceAt P A4 S x copy
                  (rxOriginalBoundaryZGlueEdge P oldQ vertical)
                  (rxOriginalBoundaryZGlueEdge_member
                    P x oldQ oldHXQ vertical)) :=
          hrawVertical.trans
            (rxOriginalBoundaryZGlueVerticalQ1
              P A4 S x copy
                (rxOriginalBoundaryZGlueEdge P oldQ vertical)
                (rxOriginalBoundaryZGlueEdge_member
                  P x oldQ oldHXQ vertical)).symm
        have hlast : S.half - 1 + 1 = S.half := by
          have := S.half_pos
          omega
        have hdata : (q, candidateCopy, edge.1) =
            (oldQ, copy, vertical.1) := by
          simpa [endpointData, rxOriginalBoundaryZGlueFaceAt,
            rxOriginalBoundaryZGlueEdge,
            rxStarEdgeInteriorBoundaryQStarEdge, rxStarEdgeInteriorBoundaryXQEdge,
            glueFaceQ1, edgeEndpoint, qDoubleCylinderEdgeEnd,
            qSubdivisionEdgeEnd, qStarEdgeEnd,
            rxStarEdgeInteriorLastIndex, hlast] using
              congrArg endpointData hraw
        have hq : q = oldQ := congrArg Prod.fst hdata
        have hcopy : candidateCopy = copy :=
          congrArg (fun value => value.2.1) hdata
        have hzEdge : edge.1 = vertical.1 :=
          congrArg (fun value => value.2.2) hdata
        subst oldQ
        subst candidateCopy
        have hedge : edge = vertical := Subtype.ext hzEdge
        subst vertical
        refine ⟨oldHXQ, ?_⟩
        intro hxq
        have hproof : oldHXQ = hxq := Subsingleton.elim _ _
        cases hproof
        exact ⟨hz, by simpa using hraw⟩
  · rcases candidateOld with ⟨face, faceCopy⟩
    have hcandidate : (face, faceCopy) =
        ((rxOriginalBoundaryZRootFace P A4 x z oldMember).1, copy) :=
      rxOriginalBoundaryZOldFace_cases P R A4 S x copy z oldMember
        (face, faceCopy) (by simpa [rxFaceX] using hx')
    have hfaceCopy : faceCopy = copy := congrArg Prod.snd hcandidate
    subst faceCopy
    have handle : ∀ corner : Two,
        (Sum.inr ⟨q,
          (candidateCopy, Sum.inl (Sum.inr edge))⟩ : RX1 P S) =
            oldZFaceQ P S corner (face, copy) →
          P.xq x q = true ∧
            ∀ hxq : P.xq x q = true,
              edge.1 = z ∧
                (Sum.inr ⟨q,
                  (candidateCopy, Sum.inl (Sum.inr edge))⟩ : RX1 P S) =
                  glueFaceQ1 P S
                    (rxOriginalBoundaryZGlueFaceAt P A4 S x copy
                      (rxOriginalBoundaryZGlueEdge P q edge)
                      (rxOriginalBoundaryZGlueEdge_member
                        P x q hxq edge)) := by
      intro corner hqTag
      have howner : P.faceX face = x := by
        simpa [rxFaceX, oldZFaceX, rxOriginalBoundaryZXCoordinate]
          using congrArg Sigma.fst hx'
      have hfaceMember : xStarFaceMember P x face = true := by
        simp only [xStarFaceMember, decide_eq_true_eq]
        exact howner
      let xFace : XStarFace P x := ⟨face, hfaceMember⟩
      have hzFace : P.faceZ face = z := by
        have hroot := congrArg (fun value : RXOldZFace P =>
          P.faceZ value.1) hcandidate
        simpa [rxOriginalBoundaryZRootFace_z P A4 x z oldMember] using hroot
      have hraw :
          (Sum.inr ⟨q,
            (candidateCopy, Sum.inl (Sum.inr edge))⟩ : RX1 P S) =
            glueFaceQ1 P S
              (rxOriginalBoundaryZGlueFaceAt P A4 S x copy
                (rxOriginalBoundaryZFaceEdge P x xFace corner)
                (rxOriginalBoundaryZFaceEdge_member P x xFace corner)) := by
        exact hqTag.trans
          (rxOriginalBoundaryZGlueQ1_eq_oldFaceQ
            P A4 S x copy z xFace hzFace corner).symm
      have hlast : S.half - 1 + 1 = S.half := by
        have := S.half_pos
        omega
      have hdata : (q, candidateCopy, edge.1) =
          (P.faceQ face corner, copy, P.faceZ face) := by
        simpa [endpointData, rxOriginalBoundaryZGlueFaceAt,
          rxOriginalBoundaryZFaceEdge,
          rxOriginalBoundaryZGlueEdge,
          rxStarEdgeInteriorBoundaryQStarEdge, rxStarEdgeInteriorBoundaryXQEdge,
          faceQZEdge, xFace,
          glueFaceQ1, edgeEndpoint, qDoubleCylinderEdgeEnd,
          qSubdivisionEdgeEnd, qStarEdgeEnd,
          rxStarEdgeInteriorLastIndex, hlast] using
            congrArg endpointData hraw
      have hq : q = P.faceQ face corner := congrArg Prod.fst hdata
      have hcopy : candidateCopy = copy :=
        congrArg (fun value => value.2.1) hdata
      have hzEdge : edge.1 = P.faceZ face :=
        congrArg (fun value => value.2.2) hdata
      subst q
      subst candidateCopy
      have hedge : edge =
          (⟨P.faceZ face, P.data.faceQ_qz face corner⟩ :
            QStarEdge P (P.faceQ face corner)) := Subtype.ext hzEdge
      subst edge
      let hxq : P.xq x (P.faceQ face corner) = true := by
        rw [← howner]
        exact P.data.faceQ_xq face corner
      refine ⟨hxq, ?_⟩
      intro hxq'
      have hproof : hxq = hxq' := Subsingleton.elim _ _
      cases hproof
      exact ⟨hzFace, by
        simpa [rxOriginalBoundaryZFaceEdge, rxOriginalBoundaryZGlueEdge,
          faceQZEdge, xFace] using hraw⟩
    rcases hqTag with hqTag | hqTag
    · exact handle 0 hqTag
    · exact handle 1 hqTag
noncomputable def rxOriginalBoundaryZRawQEndpointPath
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (q : P.Q) (candidateCopy : Two) (edge : QStarEdge P q)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z oldMember)
      (Vertex.q (Sum.inr
        ⟨q, (candidateCopy, Sum.inl (Sum.inr edge))⟩)) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      (rxReplacementXBoundaryRoot P
        A4.toTannerSquareAdmissibleV3 S
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      ⟨Vertex.q (Sum.inr
        ⟨q, (candidateCopy, Sum.inl (Sum.inr edge))⟩), member⟩ := by
  obtain ⟨hxq, hnormalize⟩ := rxOriginalBoundaryZRawQEndpoint_normalize
    P R A4 S x copy z oldMember q candidateCopy edge member
  obtain ⟨hz, hraw⟩ := hnormalize hxq
  let oldEdge := rxOriginalBoundaryZGlueEdge P q edge
  let oldEdgeMember := rxOriginalBoundaryZGlueEdge_member P x q hxq edge
  let target : RXOriginalBoundaryZTarget P x z :=
    .glueQ oldEdge oldEdgeMember hz 1
  let path := rxOriginalBoundaryZTargetBoundaryPathHistorical
    P A4 S x copy z oldMember target
  have htarget : rxOriginalBoundaryZTargetBoundaryVertex
        P A4 S x copy z oldMember target =
      ⟨Vertex.q (Sum.inr
        ⟨q, (candidateCopy, Sum.inl (Sum.inr edge))⟩), member⟩ := by
    apply Subtype.ext
    exact congrArg Vertex.q hraw.symm
  exact htarget ▸ path
def rxOriginalBoundaryZQEndpointTag
    (P : TannerSquarePresentation) (S : OddScale) : RX1 P S → Bool
  | Sum.inr ⟨_, (_, Sum.inl (Sum.inr _))⟩ => true
  | _ => false
theorem rxOriginalBoundaryZRawQEndpointTag_true
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (newQ : Σ q : P.Q, QDoubleCylinderVertex P q S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z oldMember)
      (Vertex.q (Sum.inr newQ)) = true) :
    rxOriginalBoundaryZQEndpointTag P S (Sum.inr newQ) = true := by
  classical
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceQ = rxFaceQ P S from rfl]
    at member
  rw [decide_eq_true_eq] at member
  obtain ⟨candidate, hx, hqTag⟩ := member
  have hx' : rxFaceX P S candidate =
      rxOriginalBoundaryZXCoordinate P S x copy z oldMember := by
    simp only [xStarFaceMember, decide_eq_true_eq] at hx
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
    exact hx
  rcases candidate with candidateLocal | candidateGlue | candidateOld
  · rcases hqTag with hqTag | hqTag <;> cases hqTag
  · rcases candidateGlue with ⟨a, qEdge, endpoint⟩
    rcases hqTag with hqTag | hqTag
    · cases hqTag
    · rcases a with ⟨⟨oldX, oldQ⟩, hxq⟩
      have howner : oldX = x := congrArg Sigma.fst hx'
      subst oldX
      rcases qEdge with copied | vertical
      · rcases copied with ⟨candidateCopy, edge, segment⟩
        change Sum.inr newQ = glueFaceQ1 P S
          ⟨(⟨(x, oldQ), hxq⟩ : XQEdge P),
            Sum.inl (candidateCopy, (edge, segment)), endpoint⟩ at hqTag
        obtain ⟨_, hcandidate⟩ := rxOriginalBoundaryZGlueFace_eq
          P A4 S x copy z oldMember oldQ hxq edge segment
            candidateCopy endpoint (by simpa [rxFaceX] using hx')
        rw [congrArg (glueFaceQ1 P S) hcandidate] at hqTag
        rw [hqTag]
        have hlast : S.half - 1 + 1 = S.half := by
          have := S.half_pos
          omega
        simp [rxOriginalBoundaryZQEndpointTag,
          rxOriginalBoundaryZGlueFaceAt, glueFaceQ1, edgeEndpoint,
          qDoubleCylinderEdgeEnd, qSubdivisionEdgeEnd,
          rxStarEdgeInteriorLastIndex, qStarEdgeEnd, hlast]
      · obtain ⟨_, _, hcandidate⟩ :=
          rxOriginalBoundaryZVerticalGlueFace_eq
            P A4 S x copy z oldMember oldQ hxq vertical endpoint
              (by simpa [rxFaceX] using hx')
        change Sum.inr newQ = glueFaceQ1 P S
          ⟨(⟨(x, oldQ), hxq⟩ : XQEdge P),
            Sum.inr vertical, endpoint⟩ at hqTag
        rw [congrArg (glueFaceQ1 P S) hcandidate] at hqTag
        rw [← rxOriginalBoundaryZGlueVerticalQ1 P A4 S x copy
          (rxOriginalBoundaryZGlueEdge P oldQ vertical)
          (rxOriginalBoundaryZGlueEdge_member P x oldQ hxq vertical)] at hqTag
        rw [hqTag]
        have hlast : S.half - 1 + 1 = S.half := by
          have := S.half_pos
          omega
        simp [rxOriginalBoundaryZQEndpointTag,
          rxOriginalBoundaryZGlueFaceAt, glueFaceQ1, edgeEndpoint,
          qDoubleCylinderEdgeEnd, qSubdivisionEdgeEnd,
          rxStarEdgeInteriorLastIndex, qStarEdgeEnd, hlast]
  · rcases candidateOld with ⟨face, oldCopy⟩
    rcases hqTag with hqTag | hqTag
    · change Sum.inr newQ = oldZFaceQ P S 0 (face, oldCopy) at hqTag
      rw [hqTag]
      simp [rxOriginalBoundaryZQEndpointTag, oldZFaceQ]
    · change Sum.inr newQ = oldZFaceQ P S 1 (face, oldCopy) at hqTag
      rw [hqTag]
      simp [rxOriginalBoundaryZQEndpointTag, oldZFaceQ]
theorem rxOriginalBoundaryZRawLocalQ_endpoint
    (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (copy : Two) (z : P.Z)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (candidateX : P.X) (edge : DoubleCylinderEdge P candidateX S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z oldMember)
      (Vertex.q (Sum.inl ⟨candidateX, edge⟩)) = true) :
    candidateX = x ∧
      ∀ howner : candidateX = x,
        let transportedEdge : DoubleCylinderEdge P x S := howner ▸ edge
        tannerDoubleCylinderEdgeStart P x S transportedEdge =
            (copy, Sum.inl ⟨Vertex.z z, by
              simpa [xStarBoundaryVertexMember, xStarVertexMember]
                using oldMember⟩) ∨
          tannerDoubleCylinderEdgeEnd P x S transportedEdge =
            (copy, Sum.inl ⟨Vertex.z z, by
              simpa [xStarBoundaryVertexMember, xStarVertexMember]
                using oldMember⟩) := by
  classical
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceQ = rxFaceQ P S from rfl]
    at member
  rw [decide_eq_true_eq] at member
  obtain ⟨candidate, hx, hqTag⟩ := member
  have hx' : rxFaceX P S candidate =
      rxOriginalBoundaryZXCoordinate P S x copy z oldMember := by
    simp only [xStarFaceMember, decide_eq_true_eq] at hx
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
    exact hx
  have handle : ∀ cornerTag : Two,
      rxFaceQ P S candidate cornerTag = Sum.inl ⟨candidateX, edge⟩ →
        candidateX = x ∧
          ∀ howner : candidateX = x,
            let transportedEdge : DoubleCylinderEdge P x S := howner ▸ edge
            tannerDoubleCylinderEdgeStart P x S transportedEdge =
                (copy, Sum.inl ⟨Vertex.z z, by
                  simpa [xStarBoundaryVertexMember, xStarVertexMember]
                    using oldMember⟩) ∨
              tannerDoubleCylinderEdgeEnd P x S transportedEdge =
                (copy, Sum.inl ⟨Vertex.z z, by
                  simpa [xStarBoundaryVertexMember, xStarVertexMember]
                    using oldMember⟩) := by
    intro cornerTag hqTag
    obtain ⟨endpoint, hendpoint⟩ :=
      rxFaceX_eq_endpoint_of_faceQ_eq_xEdge
        P S candidate cornerTag candidateX edge hqTag
    have hcoordinate :
        (⟨candidateX,
          edgeEndpoint (tannerDoubleCylinderEdgeStart P candidateX S)
            (tannerDoubleCylinderEdgeEnd P candidateX S) edge endpoint⟩ :
            RX0 P S) =
          rxOriginalBoundaryZXCoordinate P S x copy z oldMember :=
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
theorem rxOriginalBoundaryZRawRectangleQ_normalize
    (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (copy : Two) (z : P.Z)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (candidateX : P.X) (candidateCopy : Two) (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P candidateX (Sum.inr edge) = true)
    (segment : Fin S.half)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z oldMember)
      (Vertex.q (Sum.inl ⟨candidateX,
        Sum.inl (candidateCopy,
          Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment))⟩)) = true) :
    candidateX = x ∧
      ∀ howner : candidateX = x,
        let transportedMember : xStarEdgeMember P x
            (Sum.inr edge) = true := howner ▸ edgeMember
        edge.1.2 = z ∧
          (Sum.inl ⟨candidateX,
            Sum.inl (candidateCopy,
              Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment))⟩ :
              RX1 P S) =
            localFaceQAt P S
              (rxOriginalBoundaryZRectangleLocalFaceAt
                P S x copy edge transportedMember) 0 := by
  obtain ⟨howner, hendpoint⟩ := rxOriginalBoundaryZRawLocalQ_endpoint
    P S x copy z oldMember candidateX
      (Sum.inl (candidateCopy,
        Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment))) member
  subst candidateX
  refine ⟨rfl, ?_⟩
  intro howner'
  have hproof : howner' = (rfl : x = x) := Subsingleton.elim _ _
  cases hproof
  rcases hendpoint rfl with hstart | hend
  · have hsubdivision := congrArg Prod.snd hstart
    by_cases hzero : segment.1 = 0
    · have himpossible :
          (Sum.inl (xStarEdgeStart P x ⟨Sum.inr edge, edgeMember⟩) :
            SubdivisionVertex P x S) =
          Sum.inl ⟨Vertex.z z, by
            simpa [xStarBoundaryVertexMember, xStarVertexMember]
              using oldMember⟩ := by
        simpa [tannerDoubleCylinderEdgeStart, subdivisionEdgeStart,
          subdivisionSegmentStart, hzero] using hsubdivision
      have hraw := congrArg Subtype.val (Sum.inl.inj himpossible)
      change Vertex.q edge.1.1 = Vertex.z z at hraw
      cases hraw
    · have himpossible :
          (Sum.inr (Sum.inl
            (⟨Sum.inr edge, edgeMember⟩,
              ⟨segment.1 - 1, by have := segment.2; omega⟩)) :
              SubdivisionVertex P x S) =
            Sum.inl ⟨Vertex.z z, by
              simpa [xStarBoundaryVertexMember, xStarVertexMember]
                using oldMember⟩ := by
        simpa [tannerDoubleCylinderEdgeStart, subdivisionEdgeStart,
          subdivisionSegmentStart, hzero] using hsubdivision
      cases himpossible
  · have hcopy : candidateCopy = copy := congrArg Prod.fst hend
    subst candidateCopy
    have hsubdivision := congrArg Prod.snd hend
    by_cases hlast : segment.1 + 1 = S.half
    · have hendOld : xStarEdgeEnd P x ⟨Sum.inr edge, edgeMember⟩ =
          ⟨Vertex.z z, by
            simpa [xStarBoundaryVertexMember, xStarVertexMember]
              using oldMember⟩ := by
        have hinl :
            (Sum.inl (xStarEdgeEnd P x
              ⟨Sum.inr edge, edgeMember⟩) :
                SubdivisionVertex P x S) =
              Sum.inl ⟨Vertex.z z, by
                simpa [xStarBoundaryVertexMember, xStarVertexMember]
                  using oldMember⟩ := by
          simpa [tannerDoubleCylinderEdgeEnd, subdivisionEdgeEnd,
            subdivisionSegmentEnd, hlast] using hsubdivision
        exact Sum.inl.inj hinl
      have hz : edge.1.2 = z :=
        Vertex.z.inj (congrArg Subtype.val hendOld)
      have hsegment : segment = rxStarEdgeInteriorLastIndex S := by
        apply Fin.ext
        change segment.1 = S.half - 1
        omega
      subst segment
      refine ⟨hz, ?_⟩
      exact (rxOriginalBoundaryZRectangleBoundaryQ0
        P S x copy edge edgeMember).symm
    · have himpossible :
          (Sum.inr (Sum.inl
            (⟨Sum.inr edge, edgeMember⟩,
              ⟨segment.1, by have := segment.2; omega⟩)) :
              SubdivisionVertex P x S) =
            Sum.inl ⟨Vertex.z z, by
              simpa [xStarBoundaryVertexMember, xStarVertexMember]
                using oldMember⟩ := by
        simpa [tannerDoubleCylinderEdgeEnd, subdivisionEdgeEnd,
          subdivisionSegmentEnd, hlast] using hsubdivision
      cases himpossible
noncomputable def rxOriginalBoundaryZRawRectangleQPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (candidateX : P.X) (candidateCopy : Two) (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P candidateX (Sum.inr edge) = true)
    (segment : Fin S.half)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z oldMember)
      (Vertex.q (Sum.inl ⟨candidateX,
        Sum.inl (candidateCopy,
          Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment))⟩)) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      (rxReplacementXBoundaryRoot P
        A4.toTannerSquareAdmissibleV3 S
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      ⟨Vertex.q (Sum.inl ⟨candidateX,
        Sum.inl (candidateCopy,
          Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment))⟩), member⟩ := by
  obtain ⟨howner, hnormalize⟩ :=
    rxOriginalBoundaryZRawRectangleQ_normalize
      P S x copy z oldMember candidateX candidateCopy
        edge edgeMember segment member
  subst candidateX
  obtain ⟨hz, hraw⟩ := hnormalize rfl
  let target : RXOriginalBoundaryZTarget P x z :=
    .rectangleQ edge edgeMember hz 0
  let path := rxOriginalBoundaryZTargetBoundaryPathHistorical
    P A4 S x copy z oldMember target
  have htarget : rxOriginalBoundaryZTargetBoundaryVertex
        P A4 S x copy z oldMember target =
      ⟨Vertex.q (Sum.inl ⟨x,
        Sum.inl (candidateCopy,
          Sum.inl (⟨Sum.inr edge, edgeMember⟩, segment))⟩), member⟩ := by
    apply Subtype.ext
    exact congrArg Vertex.q hraw.symm
  exact htarget ▸ path
theorem rxOriginalBoundaryZRectangleBoundaryQ1
    (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (copy : Two) (z : P.Z)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P x (Sum.inr edge) = true)
    (hz : edge.1.2 = z) :
    localFaceQAt P S
        (rxOriginalBoundaryZRectangleLocalFaceAt
          P S x copy edge edgeMember) 1 =
      Sum.inl ⟨x, Sum.inr
        (subdivisionOriginalBoundaryVertex P x S
          ⟨Vertex.z z, oldMember⟩)⟩ := by
  have hlast : S.half - 1 + 1 = S.half := by
    have := S.half_pos
    omega
  simp [rxOriginalBoundaryZRectangleLocalFaceAt, localFaceQAt,
    localFaceQ1, localFaceQ1Edge, localFaceQ1EdgeAt,
    doubleCylinderRectangleBoundaryEdge,
    rxStarEdgeInteriorBoundaryEdge, subdivisionOriginalBoundaryEdge,
    subdivisionBoundaryEdgeEnd, subdivisionEdgeEnd,
    subdivisionSegmentEnd, rxStarEdgeInteriorLastIndex, hlast,
    subdivisionOriginalBoundaryVertex]
  apply Subtype.ext
  apply congrArg Sum.inl
  apply Subtype.ext
  exact congrArg Vertex.z hz
theorem rxOriginalBoundaryZRawVerticalQ_normalize
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (candidateX : P.X)
    (boundaryVertex : SubdivisionBoundaryVertex P candidateX S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z oldMember)
      (Vertex.q (Sum.inl ⟨candidateX, Sum.inr boundaryVertex⟩)) = true) :
    candidateX = x ∧
      ∀ howner : candidateX = x,
        let transportedVertex : SubdivisionBoundaryVertex P x S :=
          howner ▸ boundaryVertex
        (Sum.inl ⟨candidateX, Sum.inr boundaryVertex⟩ : RX1 P S) =
          localFaceQAt P S
            (rxOriginalBoundaryZRectangleLocalFaceAt P S x copy
              (rxOriginalBoundaryZRootOwner P A4 x z oldMember).1.edge
              (rxOriginalBoundaryZRootOwner P A4 x z oldMember).1.member) 1 := by
  obtain ⟨howner, hendpoint⟩ := rxOriginalBoundaryZRawLocalQ_endpoint
    P S x copy z oldMember candidateX (Sum.inr boundaryVertex) member
  subst candidateX
  refine ⟨rfl, ?_⟩
  intro howner'
  have hproof : howner' = (rfl : x = x) := Subsingleton.elim _ _
  cases hproof
  have hvertex : boundaryVertex =
      subdivisionOriginalBoundaryVertex P x S ⟨Vertex.z z, oldMember⟩ := by
    rcases hendpoint rfl with hstart | hend
    · have hraw := congrArg Prod.snd hstart
      apply Subtype.ext
      simpa [tannerDoubleCylinderEdgeStart,
        subdivisionOriginalBoundaryVertex, xStarBoundaryVertexToStar] using hraw
    · have hraw := congrArg Prod.snd hend
      apply Subtype.ext
      simpa [tannerDoubleCylinderEdgeEnd,
        subdivisionOriginalBoundaryVertex, xStarBoundaryVertexToStar] using hraw
  rw [hvertex]
  exact (rxOriginalBoundaryZRectangleBoundaryQ1
    P S x copy z oldMember
      (rxOriginalBoundaryZRootOwner P A4 x z oldMember).1.edge
      (rxOriginalBoundaryZRootOwner P A4 x z oldMember).1.member
      (rxOriginalBoundaryZRootOwner P A4 x z oldMember).2).symm
noncomputable def rxOriginalBoundaryZRawVerticalQPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (candidateX : P.X)
    (boundaryVertex : SubdivisionBoundaryVertex P candidateX S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z oldMember)
      (Vertex.q (Sum.inl ⟨candidateX, Sum.inr boundaryVertex⟩)) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      (rxReplacementXBoundaryRoot P
        A4.toTannerSquareAdmissibleV3 S
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      ⟨Vertex.q (Sum.inl ⟨candidateX, Sum.inr boundaryVertex⟩),
        member⟩ := by
  obtain ⟨howner, hnormalize⟩ :=
    rxOriginalBoundaryZRawVerticalQ_normalize
      P A4 S x copy z oldMember candidateX boundaryVertex member
  subst candidateX
  have hraw := hnormalize rfl
  let owner := rxOriginalBoundaryZRootOwner P A4 x z oldMember
  let target : RXOriginalBoundaryZTarget P x z :=
    .rectangleQ owner.1.edge owner.1.member owner.2 1
  let path := rxOriginalBoundaryZTargetBoundaryPathHistorical
    P A4 S x copy z oldMember target
  have htarget : rxOriginalBoundaryZTargetBoundaryVertex
        P A4 S x copy z oldMember target =
      ⟨Vertex.q (Sum.inl ⟨x, Sum.inr boundaryVertex⟩), member⟩ := by
    apply Subtype.ext
    exact congrArg Vertex.q hraw.symm
  exact htarget ▸ path
theorem rxOriginalBoundaryZRawXQEdgeQ_false
    (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (copy : Two) (z : P.Z)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (candidateX : P.X) (candidateCopy : Two) (edge : XQEdge P)
    (edgeMember : xStarEdgeMember P candidateX (Sum.inl edge) = true)
    (segment : Fin S.half)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z oldMember)
      (Vertex.q (Sum.inl ⟨candidateX,
        Sum.inl (candidateCopy,
          Sum.inl (⟨Sum.inl edge, edgeMember⟩, segment))⟩)) = true) :
    False := by
  obtain ⟨howner, hendpoint⟩ := rxOriginalBoundaryZRawLocalQ_endpoint
    P S x copy z oldMember candidateX
      (Sum.inl (candidateCopy,
        Sum.inl (⟨Sum.inl edge, edgeMember⟩, segment))) member
  subst candidateX
  rcases hendpoint rfl with hstart | hend
  · have hsubdivision := congrArg Prod.snd hstart
    by_cases hzero : segment.1 = 0
    · have hinl :
          (Sum.inl (xStarEdgeStart P x ⟨Sum.inl edge, edgeMember⟩) :
            SubdivisionVertex P x S) =
          Sum.inl ⟨Vertex.z z, by
            simpa [xStarBoundaryVertexMember, xStarVertexMember]
              using oldMember⟩ := by
        simpa [tannerDoubleCylinderEdgeStart, subdivisionEdgeStart,
          subdivisionSegmentStart, hzero] using hsubdivision
      have hraw := congrArg Subtype.val (Sum.inl.inj hinl)
      change Vertex.x edge.1.1 = Vertex.z z at hraw
      cases hraw
    · have himpossible :
          (Sum.inr (Sum.inl
            (⟨Sum.inl edge, edgeMember⟩,
              ⟨segment.1 - 1, by have := segment.2; omega⟩)) :
              SubdivisionVertex P x S) =
            Sum.inl ⟨Vertex.z z, by
              simpa [xStarBoundaryVertexMember, xStarVertexMember]
                using oldMember⟩ := by
        simpa [tannerDoubleCylinderEdgeStart, subdivisionEdgeStart,
          subdivisionSegmentStart, hzero] using hsubdivision
      cases himpossible
  · have hsubdivision := congrArg Prod.snd hend
    by_cases hlast : segment.1 + 1 = S.half
    · have hinl :
          (Sum.inl (xStarEdgeEnd P x ⟨Sum.inl edge, edgeMember⟩) :
            SubdivisionVertex P x S) =
          Sum.inl ⟨Vertex.z z, by
            simpa [xStarBoundaryVertexMember, xStarVertexMember]
              using oldMember⟩ := by
        simpa [tannerDoubleCylinderEdgeEnd, subdivisionEdgeEnd,
          subdivisionSegmentEnd, hlast] using hsubdivision
      have hraw := congrArg Subtype.val (Sum.inl.inj hinl)
      change Vertex.q edge.1.2 = Vertex.z z at hraw
      cases hraw
    · have himpossible :
          (Sum.inr (Sum.inl
            (⟨Sum.inl edge, edgeMember⟩,
              ⟨segment.1, by have := segment.2; omega⟩)) :
              SubdivisionVertex P x S) =
            Sum.inl ⟨Vertex.z z, by
              simpa [xStarBoundaryVertexMember, xStarVertexMember]
                using oldMember⟩ := by
        simpa [tannerDoubleCylinderEdgeEnd, subdivisionEdgeEnd,
          subdivisionSegmentEnd, hlast] using hsubdivision
      cases himpossible
theorem rxOriginalBoundaryZRawInteriorQ_false
    (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (copy : Two) (z : P.Z)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (candidateX : P.X) (candidateCopy : Two)
    (interior :
      (XStarFace P candidateX × Fin S.half × Fin (S.half - 1)) ⊕
        (XStarFace P candidateX × Fin (S.half - 1) × Fin S.half))
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z oldMember)
      (Vertex.q (Sum.inl ⟨candidateX,
        Sum.inl (candidateCopy, Sum.inr interior)⟩)) = true) : False := by
  obtain ⟨howner, hendpoint⟩ := rxOriginalBoundaryZRawLocalQ_endpoint
    P S x copy z oldMember candidateX
      (Sum.inl (candidateCopy, Sum.inr interior)) member
  subst candidateX
  rcases hendpoint rfl with hstart | hend
  · have hsubdivision := congrArg Prod.snd hstart
    rcases interior with horizontal | vertical
    · rcases horizontal with ⟨face, column, row⟩
      have hgrid : subdivisionGridVertex P x S face
          ⟨column.1, by have := column.2; omega⟩
          ⟨row.1 + 1, by have := row.2; omega⟩ =
          Sum.inl ⟨Vertex.z z, by
            simpa [xStarBoundaryVertexMember, xStarVertexMember]
              using oldMember⟩ := by
        simp only [tannerDoubleCylinderEdgeStart, subdivisionEdgeStart] at hsubdivision
        exact hsubdivision
      obtain ⟨_, hrow, _⟩ := subdivisionGridVertex_eq_originalZ_coordinates
        P S x face _ _ z _ hgrid
      change row.1 + 1 = S.half at hrow
      have := row.2
      omega
    · rcases vertical with ⟨face, column, row⟩
      have hgrid : subdivisionGridVertex P x S face
          ⟨column.1 + 1, by have := column.2; omega⟩
          ⟨row.1, by have := row.2; omega⟩ =
          Sum.inl ⟨Vertex.z z, by
            simpa [xStarBoundaryVertexMember, xStarVertexMember]
              using oldMember⟩ := by
        simp only [tannerDoubleCylinderEdgeStart, subdivisionEdgeStart] at hsubdivision
        exact hsubdivision
      obtain ⟨hcolumn, _, _⟩ := subdivisionGridVertex_eq_originalZ_coordinates
        P S x face _ _ z _ hgrid
      change column.1 + 1 = S.half at hcolumn
      have := column.2
      omega
  · have hsubdivision := congrArg Prod.snd hend
    rcases interior with horizontal | vertical
    · rcases horizontal with ⟨face, column, row⟩
      have hgrid : subdivisionGridVertex P x S face
          ⟨column.1 + 1, by have := column.2; omega⟩
          ⟨row.1 + 1, by have := row.2; omega⟩ =
          Sum.inl ⟨Vertex.z z, by
            simpa [xStarBoundaryVertexMember, xStarVertexMember]
              using oldMember⟩ := by
        simp only [tannerDoubleCylinderEdgeEnd, subdivisionEdgeEnd] at hsubdivision
        exact hsubdivision
      obtain ⟨_, hrow, _⟩ := subdivisionGridVertex_eq_originalZ_coordinates
        P S x face _ _ z _ hgrid
      change row.1 + 1 = S.half at hrow
      have := row.2
      omega
    · rcases vertical with ⟨face, column, row⟩
      have hgrid : subdivisionGridVertex P x S face
          ⟨column.1 + 1, by have := column.2; omega⟩
          ⟨row.1 + 1, by have := row.2; omega⟩ =
          Sum.inl ⟨Vertex.z z, by
            simpa [xStarBoundaryVertexMember, xStarVertexMember]
              using oldMember⟩ := by
        simp only [tannerDoubleCylinderEdgeEnd, subdivisionEdgeEnd] at hsubdivision
        exact hsubdivision
      obtain ⟨hcolumn, _, _⟩ := subdivisionGridVertex_eq_originalZ_coordinates
        P S x face _ _ z _ hgrid
      change column.1 + 1 = S.half at hcolumn
      have := column.2
      omega
noncomputable def rxOriginalBoundaryZRawLocalQPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (candidateX : P.X) (edge : DoubleCylinderEdge P candidateX S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z oldMember)
      (Vertex.q (Sum.inl ⟨candidateX, edge⟩)) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      (rxReplacementXBoundaryRoot P
        A4.toTannerSquareAdmissibleV3 S
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      ⟨Vertex.q (Sum.inl ⟨candidateX, edge⟩), member⟩ := by
  rcases edge with copied | boundaryVertex
  · rcases copied with ⟨candidateCopy, subdivisionEdge⟩
    rcases subdivisionEdge with original | interior
    · rcases original with ⟨starEdge, segment⟩
      rcases starEdge with ⟨rawEdge, edgeMember⟩
      rcases rawEdge with xqEdge | qzEdge
      · exact False.elim (rxOriginalBoundaryZRawXQEdgeQ_false
          P S x copy z oldMember candidateX candidateCopy
            xqEdge edgeMember segment member)
      · exact rxOriginalBoundaryZRawRectangleQPath
          P A4 S x copy z oldMember candidateX candidateCopy
            qzEdge edgeMember segment member
    · exact False.elim (rxOriginalBoundaryZRawInteriorQ_false
        P S x copy z oldMember candidateX candidateCopy interior member)
  · exact rxOriginalBoundaryZRawVerticalQPath
      P A4 S x copy z oldMember candidateX boundaryVertex member
noncomputable def rxOriginalBoundaryZRawQPath
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (newQ : RX1 P S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z oldMember)
      (Vertex.q newQ) = true) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      (rxReplacementXBoundaryRoot P
        A4.toTannerSquareAdmissibleV3 S
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      ⟨Vertex.q newQ, member⟩ := by
  rcases newQ with localEdge | qVertex
  · rcases localEdge with ⟨candidateX, edge⟩
    exact rxOriginalBoundaryZRawLocalQPath
      P A4 S x copy z oldMember candidateX edge member
  · rcases qVertex with ⟨q, candidateCopy, subdivisionVertex⟩
    rcases subdivisionVertex with oldVertex | interior
    · rcases oldVertex with center | edge
      · have himpossible := rxOriginalBoundaryZRawQEndpointTag_true
          P A4 S x copy z oldMember
            ⟨q, (candidateCopy, Sum.inl (Sum.inl center))⟩ member
        simp [rxOriginalBoundaryZQEndpointTag] at himpossible
      · exact rxOriginalBoundaryZRawQEndpointPath
          P R A4 S x copy z oldMember q candidateCopy edge member
    · have himpossible := rxOriginalBoundaryZRawQEndpointTag_true
        P A4 S x copy z oldMember
          ⟨q, (candidateCopy, Sum.inr interior)⟩ member
      simp [rxOriginalBoundaryZQEndpointTag] at himpossible
noncomputable def rxReplacementXBoundaryPathOriginalZ
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (vertex : XStarBoundaryVertex (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z oldMember)) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      (rxReplacementXBoundaryRoot P
        A4.toTannerSquareAdmissibleV3 S
        (rxOriginalBoundaryZXCoordinate P S x copy z oldMember))
      vertex := by
  rcases vertex with ⟨value, member⟩
  rcases value with newX | newQ | newZ
  · simp [xStarBoundaryVertexMember] at member
  · exact rxOriginalBoundaryZRawQPath
      P R A4 S x copy z oldMember newQ member
  · exact rxOriginalBoundaryZRawZPath
      P R A4 S x copy z oldMember newZ member
noncomputable def rxFaceInteriorBoundaryPathSW
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (face : XStarFace P x) (i j : Fin (S.half - 1))
    (qCorner : Two) :=
  xStarFaceBoundaryPathToQ (rxReplacementPresentation P S)
    ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
    (rxFaceInteriorXStarFaceSW P S x copy face i j) qCorner
theorem rxFaceInteriorBoundaryQEqSWSE
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (face : XStarFace P x) (i j : Fin (S.half - 1)) :
    xBoundaryEdgeStart (rxReplacementPresentation P S)
        ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
          (rxFaceInteriorXStarFaceSW P S x copy face i j) 1) =
      xBoundaryEdgeStart (rxReplacementPresentation P S)
        ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
          (rxFaceInteriorXStarFaceSE P S x copy face i j) 1) := by
  apply Subtype.ext
  exact congrArg Vertex.q (rxFaceInteriorNeighborQ_eq P S x copy face i j).1
theorem rxFaceInteriorBoundaryQEqSWNW
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (face : XStarFace P x) (i j : Fin (S.half - 1)) :
    xBoundaryEdgeStart (rxReplacementPresentation P S)
        ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
          (rxFaceInteriorXStarFaceSW P S x copy face i j) 0) =
      xBoundaryEdgeStart (rxReplacementPresentation P S)
        ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
          (rxFaceInteriorXStarFaceNW P S x copy face i j) 0) := by
  apply Subtype.ext
  exact congrArg Vertex.q (rxFaceInteriorNeighborQ_eq P S x copy face i j).2.1
theorem rxFaceInteriorBoundaryQEqSENE
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (face : XStarFace P x) (i j : Fin (S.half - 1)) :
    xBoundaryEdgeStart (rxReplacementPresentation P S)
        ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
          (rxFaceInteriorXStarFaceSE P S x copy face i j) 0) =
      xBoundaryEdgeStart (rxReplacementPresentation P S)
        ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
        (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
          ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
          (rxFaceInteriorXStarFaceNE P S x copy face i j) 0) := by
  apply Subtype.ext
  exact congrArg Vertex.q
    (rxFaceInteriorNeighborQ_eq P S x copy face i j).2.2.1
noncomputable def rxFaceInteriorBoundaryPathSE
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (face : XStarFace P x) (i j : Fin (S.half - 1))
    (qCorner : Two) := by
  let first := xStarFaceBoundaryPathToQ (rxReplacementPresentation P S)
    ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
    (rxFaceInteriorXStarFaceSW P S x copy face i j) 1
  let second := (xStarFaceBoundaryPathToQ (rxReplacementPresentation P S)
    ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
    (rxFaceInteriorXStarFaceSE P S x copy face i j) 1).reverse
  let last := xStarFaceBoundaryPathToQ (rxReplacementPresentation P S)
    ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
    (rxFaceInteriorXStarFaceSE P S x copy face i j) qCorner
  exact first.append
    (((rxFaceInteriorBoundaryQEqSWSE P S x copy face i j).symm ▸ second).append last)
noncomputable def rxFaceInteriorBoundaryPathNW
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (face : XStarFace P x) (i j : Fin (S.half - 1))
    (qCorner : Two) := by
  let path := xStarFaceBoundaryPathToQ (rxReplacementPresentation P S)
    ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
    (rxFaceInteriorXStarFaceNW P S x copy face i j) qCorner
  exact (rxFaceInteriorBoundaryQEqSWNW P S x copy face i j).symm ▸ path
noncomputable def rxFaceInteriorBoundaryPathNE
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (face : XStarFace P x) (i j : Fin (S.half - 1))
    (qCorner : Two) := by
  let first := rxFaceInteriorBoundaryPathSE P S x copy face i j 0
  let last := xStarFaceBoundaryPathToQ (rxReplacementPresentation P S)
    ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
    (rxFaceInteriorXStarFaceNE P S x copy face i j) qCorner
  exact first.append
    ((rxFaceInteriorBoundaryQEqSENE P S x copy face i j).symm ▸ last)
noncomputable def rxFaceInteriorBoundaryPathToZSW
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (face : XStarFace P x) (i j : Fin (S.half - 1)) :=
  (rxFaceInteriorBoundaryPathSW P S x copy face i j 0).append
    (xStarFaceBoundaryPathToZ _ _
      (rxFaceInteriorXStarFaceSW P S x copy face i j))
noncomputable def rxFaceInteriorBoundaryPathToZNW
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (face : XStarFace P x) (i j : Fin (S.half - 1)) :=
  (rxFaceInteriorBoundaryPathNW P S x copy face i j 0).append
    (xStarFaceBoundaryPathToZ _ _
      (rxFaceInteriorXStarFaceNW P S x copy face i j))
noncomputable def rxFaceInteriorBoundaryPathToZSE
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (face : XStarFace P x) (i j : Fin (S.half - 1)) :=
  (rxFaceInteriorBoundaryPathSE P S x copy face i j 0).append
    (xStarFaceBoundaryPathToZ _ _
      (rxFaceInteriorXStarFaceSE P S x copy face i j))
noncomputable def rxFaceInteriorBoundaryPathToZNE
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (face : XStarFace P x) (i j : Fin (S.half - 1)) :=
  (rxFaceInteriorBoundaryPathNE P S x copy face i j 0).append
    (xStarFaceBoundaryPathToZ _ _
      (rxFaceInteriorXStarFaceNE P S x copy face i j))
theorem rxFaceInteriorBoundaryZ_cases
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (face : XStarFace P x) (i j : Fin (S.half - 1))
    (newZ : RX2 P S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ (Vertex.z newZ) = true) :
    newZ = localFaceZ P S (rxFaceInteriorLocalFaceSW P S x copy face i j) ∨
      newZ = localFaceZ P S (rxFaceInteriorLocalFaceSE P S x copy face i j) ∨
      newZ = localFaceZ P S (rxFaceInteriorLocalFaceNW P S x copy face i j) ∨
      newZ = localFaceZ P S (rxFaceInteriorLocalFaceNE P S x copy face i j) := by
  classical
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl]
    at member
  rw [decide_eq_true_eq] at member
  obtain ⟨candidate, hx, hz⟩ := member
  have hx' : rxFaceX P S candidate =
      ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ := by
    simp only [xStarFaceMember, decide_eq_true_eq] at hx
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
    exact hx
  rcases rxFaceInteriorFace_cases P S x copy face i j candidate hx' with
      hsw | hse | hnw | hne
  · left
    simp only [hsw, rxFaceZ] at hz
    exact hz
  · right; left
    simp only [hse, rxFaceZ] at hz
    exact hz
  · right; right; left
    simp only [hnw, rxFaceZ] at hz
    exact hz
  · right; right; right
    simp only [hne, rxFaceZ] at hz
    exact hz
theorem rxFaceInteriorBoundaryQ_cases
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (face : XStarFace P x) (i j : Fin (S.half - 1))
    (newQ : RX1 P S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ (Vertex.q newQ) = true) :
    newQ = localFaceQAt P S (rxFaceInteriorLocalFaceSW P S x copy face i j) 0 ∨
      newQ = localFaceQAt P S (rxFaceInteriorLocalFaceSW P S x copy face i j) 1 ∨
      newQ = localFaceQAt P S (rxFaceInteriorLocalFaceSE P S x copy face i j) 0 ∨
      newQ = localFaceQAt P S (rxFaceInteriorLocalFaceSE P S x copy face i j) 1 ∨
      newQ = localFaceQAt P S (rxFaceInteriorLocalFaceNW P S x copy face i j) 0 ∨
      newQ = localFaceQAt P S (rxFaceInteriorLocalFaceNW P S x copy face i j) 1 ∨
      newQ = localFaceQAt P S (rxFaceInteriorLocalFaceNE P S x copy face i j) 0 ∨
      newQ = localFaceQAt P S (rxFaceInteriorLocalFaceNE P S x copy face i j) 1 := by
  classical
  simp only [xStarBoundaryVertexMember, decide_eq_true_eq] at member
  change (∃ candidate : RXFace P S,
    xStarFaceMember (rxReplacementPresentation P S)
        ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ candidate = true ∧
      (newQ = rxFaceQ P S candidate 0 ∨
        newQ = rxFaceQ P S candidate 1)) at member
  obtain ⟨candidate, hx, hq⟩ := member
  have hx' : rxFaceX P S candidate =
      ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ := by
    simp only [xStarFaceMember, decide_eq_true_eq] at hx
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
    exact hx
  rcases rxFaceInteriorFace_cases P S x copy face i j candidate hx' with
      hsw | hse | hnw | hne
  · subst candidate
    rcases hq with hq | hq
    · left; simpa [rxFaceQ, localFaceQAt] using hq
    · right; left; simpa [rxFaceQ, localFaceQAt] using hq
  · subst candidate
    rcases hq with hq | hq
    · right; right; left; simpa [rxFaceQ, localFaceQAt] using hq
    · right; right; right; left; simpa [rxFaceQ, localFaceQAt] using hq
  · subst candidate
    rcases hq with hq | hq
    · right; right; right; right; left
      simpa [rxFaceQ, localFaceQAt] using hq
    · right; right; right; right; right; left
      simpa [rxFaceQ, localFaceQAt] using hq
  · subst candidate
    rcases hq with hq | hq
    · right; right; right; right; right; right; left
      simpa [rxFaceQ, localFaceQAt] using hq
    · right; right; right; right; right; right; right
      simpa [rxFaceQ, localFaceQAt] using hq
noncomputable def rxReplacementXBoundaryPathFaceInterior
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (x : P.X) (copy : Two) (face : XStarFace P x)
    (i j : Fin (S.half - 1))
    (vertex : XStarBoundaryVertex (rxReplacementPresentation P S)
      ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S)
        ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩)
      (xBoundaryEdgeEnd (rxReplacementPresentation P S)
        ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩)
      (rxReplacementXBoundaryRoot P A3 S
        ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩) vertex := by
  rw [rxReplacementXBoundaryRoot_faceInterior P A3 S x copy face i j]
  rcases vertex with ⟨value, member⟩
  rcases value with newX | newQ | newZ
  · simp [xStarBoundaryVertexMember] at member
  · by_cases hsw0 : newQ = localFaceQAt P S
        (rxFaceInteriorLocalFaceSW P S x copy face i j) 0
    · let path := rxFaceInteriorBoundaryPathSW P S x copy face i j 0
      have htarget : xBoundaryEdgeStart (rxReplacementPresentation P S)
          ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
          (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
            ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
            (rxFaceInteriorXStarFaceSW P S x copy face i j) 0) =
          ⟨Vertex.q newQ, member⟩ := by
        apply Subtype.ext
        exact congrArg Vertex.q hsw0.symm
      exact htarget ▸ path
    · by_cases hsw1 : newQ = localFaceQAt P S
          (rxFaceInteriorLocalFaceSW P S x copy face i j) 1
      · let path := rxFaceInteriorBoundaryPathSW P S x copy face i j 1
        have htarget : xBoundaryEdgeStart (rxReplacementPresentation P S)
            ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
            (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
              ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
              (rxFaceInteriorXStarFaceSW P S x copy face i j) 1) =
            ⟨Vertex.q newQ, member⟩ := by
          apply Subtype.ext
          exact congrArg Vertex.q hsw1.symm
        exact htarget ▸ path
      · by_cases hse0 : newQ = localFaceQAt P S
            (rxFaceInteriorLocalFaceSE P S x copy face i j) 0
        · let path := rxFaceInteriorBoundaryPathSE P S x copy face i j 0
          have htarget : xBoundaryEdgeStart (rxReplacementPresentation P S)
              ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
              (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
                ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
                (rxFaceInteriorXStarFaceSE P S x copy face i j) 0) =
              ⟨Vertex.q newQ, member⟩ := by
            apply Subtype.ext
            exact congrArg Vertex.q hse0.symm
          exact htarget ▸ path
        · by_cases hse1 : newQ = localFaceQAt P S
              (rxFaceInteriorLocalFaceSE P S x copy face i j) 1
          · let path := rxFaceInteriorBoundaryPathSE P S x copy face i j 1
            have htarget : xBoundaryEdgeStart (rxReplacementPresentation P S)
                ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
                (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
                  ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
                  (rxFaceInteriorXStarFaceSE P S x copy face i j) 1) =
                ⟨Vertex.q newQ, member⟩ := by
              apply Subtype.ext
              exact congrArg Vertex.q hse1.symm
            exact htarget ▸ path
          · by_cases hnw0 : newQ = localFaceQAt P S
                (rxFaceInteriorLocalFaceNW P S x copy face i j) 0
            · let path := rxFaceInteriorBoundaryPathNW P S x copy face i j 0
              have htarget : xBoundaryEdgeStart (rxReplacementPresentation P S)
                  ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
                  (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
                    ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
                    (rxFaceInteriorXStarFaceNW P S x copy face i j) 0) =
                  ⟨Vertex.q newQ, member⟩ := by
                apply Subtype.ext
                exact congrArg Vertex.q hnw0.symm
              exact htarget ▸ path
            · by_cases hnw1 : newQ = localFaceQAt P S
                  (rxFaceInteriorLocalFaceNW P S x copy face i j) 1
              · let path := rxFaceInteriorBoundaryPathNW P S x copy face i j 1
                have htarget : xBoundaryEdgeStart (rxReplacementPresentation P S)
                    ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
                    (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
                      ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
                      (rxFaceInteriorXStarFaceNW P S x copy face i j) 1) =
                    ⟨Vertex.q newQ, member⟩ := by
                  apply Subtype.ext
                  exact congrArg Vertex.q hnw1.symm
                exact htarget ▸ path
              · by_cases hne0 : newQ = localFaceQAt P S
                    (rxFaceInteriorLocalFaceNE P S x copy face i j) 0
                · let path := rxFaceInteriorBoundaryPathNE P S x copy face i j 0
                  have htarget : xBoundaryEdgeStart (rxReplacementPresentation P S)
                      ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
                      (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
                        ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
                        (rxFaceInteriorXStarFaceNE P S x copy face i j) 0) =
                      ⟨Vertex.q newQ, member⟩ := by
                    apply Subtype.ext
                    exact congrArg Vertex.q hne0.symm
                  exact htarget ▸ path
                · have cases := rxFaceInteriorBoundaryQ_cases P S x copy face i j
                      newQ member
                  have remaining := cases.resolve_left hsw0
                  have remaining := remaining.resolve_left hsw1
                  have remaining := remaining.resolve_left hse0
                  have remaining := remaining.resolve_left hse1
                  have remaining := remaining.resolve_left hnw0
                  have remaining := remaining.resolve_left hnw1
                  have hne1 := remaining.resolve_left hne0
                  let path := rxFaceInteriorBoundaryPathNE P S x copy face i j 1
                  have htarget : xBoundaryEdgeStart (rxReplacementPresentation P S)
                      ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
                      (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
                        ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
                        (rxFaceInteriorXStarFaceNE P S x copy face i j) 1) =
                      ⟨Vertex.q newQ, member⟩ := by
                    apply Subtype.ext
                    exact congrArg Vertex.q hne1.symm
                  exact htarget ▸ path
  · by_cases hsw : newZ = localFaceZ P S
        (rxFaceInteriorLocalFaceSW P S x copy face i j)
    · let path := rxFaceInteriorBoundaryPathToZSW P S x copy face i j
      have htarget : xBoundaryEdgeEnd (rxReplacementPresentation P S)
          ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
          (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
            ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
            (rxFaceInteriorXStarFaceSW P S x copy face i j) 0) =
          ⟨Vertex.z newZ, member⟩ := by
        apply Subtype.ext
        exact congrArg Vertex.z hsw.symm
      exact htarget ▸ path
    · by_cases hse : newZ = localFaceZ P S
          (rxFaceInteriorLocalFaceSE P S x copy face i j)
      · let path := rxFaceInteriorBoundaryPathToZSE P S x copy face i j
        have htarget : xBoundaryEdgeEnd (rxReplacementPresentation P S)
            ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
            (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
              ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
              (rxFaceInteriorXStarFaceSE P S x copy face i j) 0) =
            ⟨Vertex.z newZ, member⟩ := by
          apply Subtype.ext
          exact congrArg Vertex.z hse.symm
        exact htarget ▸ path
      · by_cases hnw : newZ = localFaceZ P S
            (rxFaceInteriorLocalFaceNW P S x copy face i j)
        · let path := rxFaceInteriorBoundaryPathToZNW P S x copy face i j
          have htarget : xBoundaryEdgeEnd (rxReplacementPresentation P S)
              ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
              (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
                ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
                (rxFaceInteriorXStarFaceNW P S x copy face i j) 0) =
              ⟨Vertex.z newZ, member⟩ := by
            apply Subtype.ext
            exact congrArg Vertex.z hnw.symm
          exact htarget ▸ path
        · have cases := rxFaceInteriorBoundaryZ_cases P S x copy face i j
              newZ member
          have remaining := cases.resolve_left hsw
          have remaining := remaining.resolve_left hse
          have hne := remaining.resolve_left hnw
          let path := rxFaceInteriorBoundaryPathToZNE P S x copy face i j
          have htarget : xBoundaryEdgeEnd (rxReplacementPresentation P S)
              ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
              (xStarFaceBoundaryEdge (rxReplacementPresentation P S)
                ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩
                (rxFaceInteriorXStarFaceNE P S x copy face i j) 0) =
              ⟨Vertex.z newZ, member⟩ := by
            apply Subtype.ext
            exact congrArg Vertex.z hne.symm
          exact htarget ▸ path
noncomputable def rxReplacementXBoundaryPath
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale)
    (successorX : (rxReplacementPresentation P S).X)
    (vertex : XStarBoundaryVertex (rxReplacementPresentation P S)
      successorX) :
    UndirectedPath
      (xBoundaryEdgeStart (rxReplacementPresentation P S) successorX)
      (xBoundaryEdgeEnd (rxReplacementPresentation P S) successorX)
      (rxReplacementXBoundaryRoot P
        A4.toTannerSquareAdmissibleV3 S successorX)
      vertex := by
  rcases successorX with ⟨x, copy, subdivisionVertex⟩
  rcases subdivisionVertex with original | interior
  · rcases original with ⟨oldValue, oldMember⟩
    rcases oldValue with oldX | oldQ | oldZ
    · have howner : oldX = x := by
        simpa [xStarVertexMember] using oldMember
      subst oldX
      exact rxReplacementXBoundaryPathOriginalCentral
        P A4 R S x copy vertex
    · have boundaryMember :
          xStarBoundaryVertexMember P x (Vertex.q oldQ) = true := by
        simpa [xStarBoundaryVertexMember, xStarVertexMember] using oldMember
      exact rxReplacementXBoundaryPathOriginalQ
        P A4 S x copy oldQ boundaryMember vertex
    · have boundaryMember :
          xStarBoundaryVertexMember P x (Vertex.z oldZ) = true := by
        simpa [xStarBoundaryVertexMember, xStarVertexMember] using oldMember
      exact rxReplacementXBoundaryPathOriginalZ
        P R A4 S x copy oldZ boundaryMember vertex
  · rcases interior with edgeInterior | faceInterior
    · rcases edgeInterior with ⟨edge, index⟩
      exact rxReplacementXBoundaryPathStarEdge
        P A4 S x copy edge index vertex
    · rcases faceInterior with ⟨face, i, j⟩
      exact rxReplacementXBoundaryPathFaceInterior
        P A4.toTannerSquareAdmissibleV3 S x copy face i j vertex
noncomputable def rxReplacementAdmissible
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) :
    TannerSquareAdmissible (rxReplacementPresentation P S) where
  xBoundaryRoot :=
    rxReplacementXBoundaryRoot P A4.toTannerSquareAdmissibleV3 S
  xBoundaryPath := rxReplacementXBoundaryPath P R A4 S
  zBoundaryRoot :=
    rxReplacementZBoundaryRoot P A4.toTannerSquareAdmissibleV3 S
  zBoundaryPath :=
    rxReplacementZBoundaryPath P A4.toTannerSquareAdmissibleV3 S
  qzRoot := rxReplacementQZRoot P A4.toTannerSquareAdmissibleV3 S
  xqRoot := rxReplacementXQRoot P A4.toTannerSquareAdmissibleV3 S
inductive RXXBoundaryA2FreeGap where
  | radial
  | vertical
  | oldZ
theorem rxXBoundaryQ_incidence
    (P : TannerSquarePresentation) (S : OddScale)
    (x : (rxReplacementPresentation P S).X)
    (q : (rxReplacementPresentation P S).Q)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S) x
      (Vertex.q q) = true) :
    (rxReplacementPresentation P S).xq x q = true := by
  simp only [xStarBoundaryVertexMember, decide_eq_true_eq] at member
  change (∃ face : RXFace P S,
    xStarFaceMember (rxReplacementPresentation P S) x face = true ∧
      (q = rxFaceQ P S face 0 ∨ q = rxFaceQ P S face 1)) at member
  obtain ⟨face, hx, hq | hq⟩ := member
  · have hx' : rxFaceX P S face = x := by
      simp only [xStarFaceMember, decide_eq_true_eq] at hx
      rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
      exact hx
    exact (rxXQIncidence_eq_true_iff P S x q).2
      ⟨face, 0, hx', hq.symm⟩
  · have hx' : rxFaceX P S face = x := by
      simp only [xStarFaceMember, decide_eq_true_eq] at hx
      rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
      exact hx
    exact (rxXQIncidence_eq_true_iff P S x q).2
      ⟨face, 1, hx', hq.symm⟩
noncomputable def rxXBoundaryOwnedAtQ
    (P : TannerSquarePresentation) (S : OddScale)
    (x : (rxReplacementPresentation P S).X)
    (q : (rxReplacementPresentation P S).Q)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S) x
      (Vertex.q q) = true)
    (root : QStarEdge (rxReplacementPresentation P S) q) :
    {owned : XStarBoundaryEdge (rxReplacementPresentation P S) x × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart (rxReplacementPresentation P S) x)
        (xBoundaryEdgeEnd (rxReplacementPresentation P S) x)
        owned.1 owned.2 = ⟨Vertex.q q, member⟩} := by
  let edge := qToXBoundaryEdge (rxReplacementPresentation P S) q x
    (rxXBoundaryQ_incidence P S x q member) root
  refine ⟨(edge, 0), ?_⟩
  rw [BDL26TannerLocalRegularity.edgeEndpoint_zero]
  apply Subtype.ext
  rfl
noncomputable def rxXBoundaryOwnedAtZ
    (P : TannerSquarePresentation) (S : OddScale)
    (x : (rxReplacementPresentation P S).X)
    (z : (rxReplacementPresentation P S).Z)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S) x
      (Vertex.z z) = true)
    (q : (rxReplacementPresentation P S).Q)
    (hxq : (rxReplacementPresentation P S).xq x q = true)
    (hqz : (rxReplacementPresentation P S).qz q z = true) :
    {owned : XStarBoundaryEdge (rxReplacementPresentation P S) x × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart (rxReplacementPresentation P S) x)
        (xBoundaryEdgeEnd (rxReplacementPresentation P S) x)
        owned.1 owned.2 = ⟨Vertex.z z, member⟩} := by
  let edge := qToXBoundaryEdge (rxReplacementPresentation P S) q x hxq
    (⟨z, hqz⟩ : QStarEdge (rxReplacementPresentation P S) q)
  refine ⟨(edge, 1), ?_⟩
  rw [BDL26TannerLocalRegularity.edgeEndpoint_one]
  apply Subtype.ext
  rfl
noncomputable def rxLocalEdgeCornerOwnerA2Free
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (edge : DoubleCylinderEdge P x S) :
    {owned : RXLocalFace P S × Two //
      localFaceQAt P S owned.1 owned.2 = Sum.inl ⟨x, edge⟩} ⊕
      RXXBoundaryA2FreeGap := by
  rcases edge with endEdge | boundaryVertex
  · rcases endEdge with ⟨copy, subdivisionEdge⟩
    rcases subdivisionEdge with original | interior
    · rcases original with ⟨starEdge, segment⟩
      rcases starEdge with ⟨rawEdge, hstar⟩
      rcases rawEdge with xqEdge | qzEdge
      · exact Sum.inr .radial
      · let boundaryEdge : XStarBoundaryEdge P x :=
          ⟨Sum.inr qzEdge, by
            simpa [xStarBoundaryEdgeMember, xStarEdgeMember] using hstar⟩
        let rectangle := subdivisionOriginalBoundaryEdge
          P x S boundaryEdge segment
        refine Sum.inl ⟨(⟨x, Sum.inr rectangle, (copy, 0)⟩, 0), ?_⟩
        simp [localFaceQAt, localFaceQ0, localFaceQ0Edge,
          localFaceQ0EdgeAt, rectangle, subdivisionOriginalBoundaryEdge,
          boundaryEdge]
        apply Subtype.ext
        rfl
    · rcases interior with horizontal | vertical
      · let face : SubdivisionFace P x S :=
          (horizontal.1, horizontal.2.1,
            rxInteriorFaceIndex S horizontal.2.2)
        refine Sum.inl ⟨(⟨x, Sum.inl (copy, face), (0, 1)⟩, 0), ?_⟩
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
        refine Sum.inl ⟨(⟨x, Sum.inl (copy, face), (1, 0)⟩, 1), ?_⟩
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
  · exact Sum.inr .vertical
noncomputable def rxLocalEdgeQZRootA2Free
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (edge : DoubleCylinderEdge P x S) :
    QStarEdge (rxReplacementPresentation P S) (Sum.inl ⟨x, edge⟩) ⊕
      RXXBoundaryA2FreeGap := by
  rcases rxLocalEdgeCornerOwnerA2Free P S x edge with owner | gap
  · let face : RXFace P S := Sum.inl owner.1.1
    let root : QStarEdge (rxReplacementPresentation P S)
        (rxFaceQ P S face owner.1.2) :=
      ⟨rxFaceZ P S face,
        (rxReplacementPresentation P S).data.faceQ_qz face owner.1.2⟩
    have hq : rxFaceQ P S face owner.1.2 = Sum.inl ⟨x, edge⟩ := by
      change localFaceQAt P S owner.1.1 owner.1.2 = Sum.inl ⟨x, edge⟩
      exact owner.2
    exact Sum.inl (hq ▸ root)
  · exact Sum.inr gap
theorem rxXBoundaryQVertex_oldXQ
    (P : TannerSquarePresentation) (S : OddScale)
    (x : RX0 P S) (q : P.Q) (vertex : QDoubleCylinderVertex P q S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S) x
      (Vertex.q (Sum.inr ⟨q, vertex⟩)) = true) :
    P.xq x.1 q = true := by
  have hsuccessor := rxXBoundaryQ_incidence P S x
    (Sum.inr ⟨q, vertex⟩) member
  obtain ⟨face, corner, hx, hq⟩ :=
    (rxXQIncidence_eq_true_iff P S x (Sum.inr ⟨q, vertex⟩)).1 hsuccessor
  rcases face with localFace | glue | oldFace
  · rcases localFace with ⟨oldX, cell, material⟩
    fin_cases corner <;> simp [rxFaceQ, localFaceQAt, localFaceQ0,
      localFaceQ1] at hq
  · rcases glue with ⟨edge, qEdge, endpoint⟩
    have hx' : edge.1.1 = x.1 := by
      exact congrArg Sigma.fst hx
    fin_cases corner
    · simp [rxFaceQ, glueFaceQ0] at hq
    · have hq' : edge.1.2 = q := by
        exact congrArg Sigma.fst (Sum.inr.inj hq)
      simpa [hx', hq'] using edge.2
  · rcases oldFace with ⟨face, copy⟩
    have hx' : P.faceX face = x.1 := by
      exact congrArg Sigma.fst hx
    have hq' : P.faceQ face corner = q := by
      exact congrArg Sigma.fst (Sum.inr.inj hq)
    simpa [hx', hq'] using P.data.faceQ_xq face corner
noncomputable def rxQVertexQZRootFromIncident
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : RX0 P S) (q : P.Q)
    (vertex : QDoubleCylinderVertex P q S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S) x
      (Vertex.q (Sum.inr ⟨q, vertex⟩)) = true) :
    QStarEdge (rxReplacementPresentation P S) (Sum.inr ⟨q, vertex⟩) := by
  obtain ⟨⟨edge, endpoint⟩, hendpoint⟩ :=
    rxQDoubleCylinderVertexIncidentEdge P A q S vertex
  let oldXQ : XQEdge P :=
    ⟨(x.1, q), rxXBoundaryQVertex_oldXQ P S x q vertex member⟩
  let face : RXFace P S := Sum.inr (Sum.inl ⟨oldXQ, edge, endpoint⟩)
  refine ⟨Sum.inl (Sum.inr ⟨q, edge⟩), ?_⟩
  apply (rxQZIncidence_eq_true_iff P S _ _).2
  refine ⟨face, 1, ?_, rfl⟩
  change glueFaceQ1 P S ⟨oldXQ, edge, endpoint⟩ = Sum.inr ⟨q, vertex⟩
  apply congrArg Sum.inr
  dsimp [oldXQ]
  rw [Sigma.ext_iff]
  refine ⟨rfl, ?_⟩
  simp only [heq_eq_eq]
  exact rxTwoElim (motive := fun endpoint =>
      BDL26TannerLocalRegularity.edgeEndpoint
          (qDoubleCylinderEdgeStart P q S)
          (qDoubleCylinderEdgeEnd P q S) edge endpoint = vertex →
        edgeEndpoint (qDoubleCylinderEdgeStart P q S)
          (qDoubleCylinderEdgeEnd P q S) edge endpoint = vertex)
    (fun h => h) (fun h => h) endpoint hendpoint
theorem rxQVertexTerminalQZ
    (P : TannerSquarePresentation) (S : OddScale) (x : RX0 P S)
    (q : P.Q) (copy : Two) (edge : QStarEdge P q)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S) x
      (Vertex.q (Sum.inr ⟨q, (copy, Sum.inl (Sum.inr edge))⟩)) = true) :
    (rxReplacementPresentation P S).qz
      (Sum.inr ⟨q, (copy, Sum.inl (Sum.inr edge))⟩)
      (Sum.inr (edge.1, copy)) = true := by
  let hxq := rxXBoundaryQVertex_oldXQ P S x q
    (copy, Sum.inl (Sum.inr edge)) member
  let oldBoundary := qToZBoundaryEdge P q edge.1 edge.2
    (⟨x.1, hxq⟩ : QStarEdge (transposePresentation P) q)
  let oldVertex := zBoundaryEdgeEnd P edge.1 oldBoundary
  let mapped := rxOldZBoundaryVertexMap P S edge.1 copy oldVertex
  have mappedMember : zStarBoundaryVertexMember
      (rxReplacementPresentation P S) (Sum.inr (edge.1, copy))
      (Vertex.q (Sum.inr ⟨q,
        (copy, Sum.inl (Sum.inr edge))⟩)) = true := by
    simpa [mapped, oldVertex, oldBoundary, rxOldZBoundaryVertexMap,
      rxOldZCopyQCoordinate, qToZBoundaryEdge, zBoundaryEdgeEnd] using mapped.2
  exact rxOldZBoundaryQZIncidence (rxReplacementPresentation P S)
    (Sum.inr ⟨q, (copy, Sum.inl (Sum.inr edge))⟩)
    (Sum.inr (edge.1, copy)) mappedMember
noncomputable def rxQVertexQZRootA2Free
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : RX0 P S) (q : P.Q)
    (vertex : QDoubleCylinderVertex P q S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S) x
      (Vertex.q (Sum.inr ⟨q, vertex⟩)) = true) :
    QStarEdge (rxReplacementPresentation P S) (Sum.inr ⟨q, vertex⟩) := by
  rcases vertex with ⟨copy, vertex⟩
  rcases vertex with original | interior
  · rcases original with center | endpoint
    · exact rxQVertexQZRootFromIncident P A S x q
        (copy, Sum.inl (Sum.inl center)) member
    · exact ⟨Sum.inr (endpoint.1, copy),
        rxQVertexTerminalQZ P S x q copy endpoint member⟩
  · exact rxQVertexQZRootFromIncident P A S x q
      (copy, Sum.inr interior) member
noncomputable def rxLocalCellXBoundaryOwnedAtZ
    (P : TannerSquarePresentation) (S : OddScale) (oldX : P.X)
    (cell : DoubleCylinderFace P oldX S) (corner : Two × Two)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxLocalCellXAt P S oldX cell corner)
      (Vertex.z (Sum.inl (Sum.inl ⟨oldX, cell⟩))) = true) :
    {owned : XStarBoundaryEdge (rxReplacementPresentation P S)
        (rxLocalCellXAt P S oldX cell corner) × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart (rxReplacementPresentation P S)
          (rxLocalCellXAt P S oldX cell corner))
        (xBoundaryEdgeEnd (rxReplacementPresentation P S)
          (rxLocalCellXAt P S oldX cell corner))
        owned.1 owned.2 =
          ⟨Vertex.z (Sum.inl (Sum.inl ⟨oldX, cell⟩)), member⟩} := by
  let face : RXFace P S := Sum.inl ⟨oldX, cell, corner⟩
  let q := rxFaceQ P S face 0
  have hxq : (rxReplacementPresentation P S).xq
      (rxLocalCellXAt P S oldX cell corner) q = true := by
    change (rxReplacementPresentation P S).xq (rxFaceX P S face) (rxFaceQ P S face 0) = true
    exact (rxReplacementPresentation P S).data.faceQ_xq face 0
  have hqz : (rxReplacementPresentation P S).qz q
      (Sum.inl (Sum.inl ⟨oldX, cell⟩)) = true := by
    change (rxReplacementPresentation P S).qz (rxFaceQ P S face 0) (rxFaceZ P S face) = true
    exact (rxReplacementPresentation P S).data.faceQ_qz face 0
  exact rxXBoundaryOwnedAtZ P S
    (rxLocalCellXAt P S oldX cell corner)
    (Sum.inl (Sum.inl ⟨oldX, cell⟩)) member q hxq hqz
noncomputable def rxQEdgeXBoundaryOwnedAtZEndpoint
    (P : TannerSquarePresentation) (S : OddScale)
    (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S)
    (oldX : P.X) (hxq : P.xq oldX qEdge.1 = true) (endpoint : Two)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (glueFaceX P S ⟨(⟨(oldX, qEdge.1), hxq⟩ : XQEdge P),
        qEdge.2, endpoint⟩)
      (Vertex.z (Sum.inl (Sum.inr qEdge))) = true) :
    {owned : XStarBoundaryEdge (rxReplacementPresentation P S)
        (glueFaceX P S ⟨(⟨(oldX, qEdge.1), hxq⟩ : XQEdge P),
          qEdge.2, endpoint⟩) × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart (rxReplacementPresentation P S)
          (glueFaceX P S ⟨(⟨(oldX, qEdge.1), hxq⟩ : XQEdge P),
            qEdge.2, endpoint⟩))
        (xBoundaryEdgeEnd (rxReplacementPresentation P S)
          (glueFaceX P S ⟨(⟨(oldX, qEdge.1), hxq⟩ : XQEdge P),
            qEdge.2, endpoint⟩))
        owned.1 owned.2 = ⟨Vertex.z (Sum.inl (Sum.inr qEdge)), member⟩} := by
  let glue : RXXQGlueFace P S :=
    ⟨(⟨(oldX, qEdge.1), hxq⟩ : XQEdge P), qEdge.2, endpoint⟩
  let face : RXFace P S := Sum.inr (Sum.inl glue)
  let q := rxFaceQ P S face 0
  have hsuccessorXQ : (rxReplacementPresentation P S).xq
      (glueFaceX P S glue) q = true := by
    change (rxReplacementPresentation P S).xq (rxFaceX P S face) (rxFaceQ P S face 0) = true
    exact (rxReplacementPresentation P S).data.faceQ_xq face 0
  have hsuccessorQZ : (rxReplacementPresentation P S).qz q
      (Sum.inl (Sum.inr qEdge)) = true := by
    change (rxReplacementPresentation P S).qz (rxFaceQ P S face 0) (rxFaceZ P S face) = true
    exact (rxReplacementPresentation P S).data.faceQ_qz face 0
  exact rxXBoundaryOwnedAtZ P S (glueFaceX P S glue)
    (Sum.inl (Sum.inr qEdge)) member q hsuccessorXQ hsuccessorQZ
noncomputable def rxLocalEdgeXBoundaryOwnedA2Free
    (P : TannerSquarePresentation) (S : OddScale) (x : RX0 P S)
    (oldX : P.X) (edge : DoubleCylinderEdge P oldX S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S) x
      (Vertex.q (Sum.inl ⟨oldX, edge⟩)) = true) :
    {owned : XStarBoundaryEdge (rxReplacementPresentation P S) x × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart (rxReplacementPresentation P S) x)
        (xBoundaryEdgeEnd (rxReplacementPresentation P S) x)
        owned.1 owned.2 = ⟨Vertex.q (Sum.inl ⟨oldX, edge⟩), member⟩} ⊕
      RXXBoundaryA2FreeGap := by
  rcases rxLocalEdgeQZRootA2Free P S oldX edge with root | gap
  · exact Sum.inl (rxXBoundaryOwnedAtQ P S x
      (Sum.inl ⟨oldX, edge⟩) member root)
  · exact Sum.inr gap
noncomputable def rxQVertexXBoundaryOwnedA2Free
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : RX0 P S) (oldQ : P.Q)
    (vertex : QDoubleCylinderVertex P oldQ S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S) x
      (Vertex.q (Sum.inr ⟨oldQ, vertex⟩)) = true) :
    {owned : XStarBoundaryEdge (rxReplacementPresentation P S) x × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart (rxReplacementPresentation P S) x)
        (xBoundaryEdgeEnd (rxReplacementPresentation P S) x)
        owned.1 owned.2 = ⟨Vertex.q (Sum.inr ⟨oldQ, vertex⟩), member⟩} := by
  let root := rxQVertexQZRootA2Free P A S x oldQ vertex member
  exact rxXBoundaryOwnedAtQ P S x
    (Sum.inr ⟨oldQ, vertex⟩) member root
noncomputable def rxVerticalLocalEdgeCornerOwner
    (P : TannerSquarePresentation) (A2 : TannerSquareAdmissibleV2 P)
    (S : OddScale) (oldX : P.X)
    (boundaryVertex : SubdivisionBoundaryVertex P oldX S) :
    {owned : RXLocalFace P S × Two //
      localFaceQAt P S owned.1 owned.2 =
        Sum.inl ⟨oldX, Sum.inr boundaryVertex⟩} := by
  obtain ⟨⟨boundaryEdge, endpoint⟩, hendpoint⟩ :=
    subdivisionBoundaryIncidentEdge P A2 oldX S boundaryVertex
  refine ⟨(⟨oldX, Sum.inr boundaryEdge, (0, endpoint)⟩, 1), ?_⟩
  simp only [localFaceQAt, twoSelect_one, localFaceQ1,
    localFaceQ1Edge, localFaceQ1EdgeAt]
  congr 3
  fin_cases endpoint
  · change BDL26TannerLocalRegularity.edgeEndpoint
      (subdivisionBoundaryEdgeStart P oldX S)
      (subdivisionBoundaryEdgeEnd P oldX S) boundaryEdge 0 =
        boundaryVertex at hendpoint
    rw [BDL26TannerLocalRegularity.edgeEndpoint_zero] at hendpoint
    simpa [hendpoint] using doubleCylinderRectangleBoundaryEdge_one_zero
      P oldX S boundaryEdge
  · change BDL26TannerLocalRegularity.edgeEndpoint
      (subdivisionBoundaryEdgeStart P oldX S)
      (subdivisionBoundaryEdgeEnd P oldX S) boundaryEdge 1 =
        boundaryVertex at hendpoint
    rw [BDL26TannerLocalRegularity.edgeEndpoint_one] at hendpoint
    simpa [hendpoint] using doubleCylinderRectangleBoundaryEdge_one_one
      P oldX S boundaryEdge
noncomputable def rxVerticalLocalEdgeQZRoot
    (P : TannerSquarePresentation) (A2 : TannerSquareAdmissibleV2 P)
    (S : OddScale) (oldX : P.X)
    (boundaryVertex : SubdivisionBoundaryVertex P oldX S) :
    QStarEdge (rxReplacementPresentation P S)
      (Sum.inl ⟨oldX, Sum.inr boundaryVertex⟩) := by
  let owner := rxVerticalLocalEdgeCornerOwner
    P A2 S oldX boundaryVertex
  let face : RXFace P S := Sum.inl owner.1.1
  let root : QStarEdge (rxReplacementPresentation P S)
      (rxFaceQ P S face owner.1.2) :=
    ⟨rxFaceZ P S face,
      (rxReplacementPresentation P S).data.faceQ_qz face owner.1.2⟩
  have hq : rxFaceQ P S face owner.1.2 =
      Sum.inl ⟨oldX, Sum.inr boundaryVertex⟩ := by
    change localFaceQAt P S owner.1.1 owner.1.2 =
      Sum.inl ⟨oldX, Sum.inr boundaryVertex⟩
    exact owner.2
  exact hq ▸ root
noncomputable def rxVerticalLocalEdgeXBoundaryOwned
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : RX0 P S) (oldX : P.X)
    (boundaryVertex : SubdivisionBoundaryVertex P oldX S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S) x
      (Vertex.q (Sum.inl ⟨oldX, Sum.inr boundaryVertex⟩)) = true) :
    {owned : XStarBoundaryEdge (rxReplacementPresentation P S) x × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart (rxReplacementPresentation P S) x)
        (xBoundaryEdgeEnd (rxReplacementPresentation P S) x)
        owned.1 owned.2 =
          ⟨Vertex.q (Sum.inl ⟨oldX, Sum.inr boundaryVertex⟩), member⟩} := by
  let root := rxVerticalLocalEdgeQZRoot P
    A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2
    S oldX boundaryVertex
  exact rxXBoundaryOwnedAtQ P S x
    (Sum.inl ⟨oldX, Sum.inr boundaryVertex⟩) member root
def rxOldZSelectedQCoordinate
    (P : TannerSquarePresentation) (S : OddScale) (copy : Two)
    (edge : QZEdge P) : RX1 P S :=
  Sum.inr ⟨edge.1.1,
    (copy, Sum.inl (Sum.inr
      (⟨edge.1.2, edge.2⟩ : QStarEdge P edge.1.1)))⟩
theorem rxOldZSelectedSuccessorIncidence
    (P : TannerSquarePresentation) (S : OddScale)
    (oldX : P.X) (copy : Two) (oldZ : P.Z)
    (oldMember : xStarBoundaryVertexMember P oldX
      (Vertex.z oldZ) = true)
    (edge : QZEdge P)
    (edgeMember : xStarEdgeMember P oldX (Sum.inr edge) = true)
    (hz : edge.1.2 = oldZ) :
    (rxReplacementPresentation P S).xq
        (rxOriginalBoundaryZXCoordinate P S oldX copy oldZ oldMember)
        (rxOldZSelectedQCoordinate P S copy edge) = true ∧
      (rxReplacementPresentation P S).qz
        (rxOldZSelectedQCoordinate P S copy edge)
        (Sum.inr (oldZ, copy)) = true := by
  change decide (∃ face : P.Face,
    xStarFaceMember P oldX face = true ∧
      decide (edge = faceQZEdge P face 0 ∨
        edge = faceQZEdge P face 1) = true) = true at edgeMember
  obtain ⟨face, hface, huse⟩ := of_decide_eq_true edgeMember
  have hfaceX : P.faceX face = oldX := by
    simpa [xStarFaceMember] using hface
  have handle : ∀ corner : Two, edge = faceQZEdge P face corner →
      (rxReplacementPresentation P S).xq
          (rxOriginalBoundaryZXCoordinate P S oldX copy oldZ oldMember)
          (rxOldZSelectedQCoordinate P S copy edge) = true ∧
        (rxReplacementPresentation P S).qz
          (rxOldZSelectedQCoordinate P S copy edge)
          (Sum.inr (oldZ, copy)) = true := by
    intro corner hedge
    subst edge
    change P.faceZ face = oldZ at hz
    let successorFace : RXFace P S :=
      Sum.inr (Sum.inr (face, copy))
    have hfaceX' : rxFaceX P S successorFace =
        rxOriginalBoundaryZXCoordinate P S oldX copy oldZ oldMember := by
      simp only [successorFace, rxFaceX, oldZFaceX,
        rxOriginalBoundaryZXCoordinate, xStarFaceZVertex, oldFaceInXStar]
      rw [Sigma.ext_iff]
      refine ⟨hfaceX, ?_⟩
      congr 5
      · exact congrArg (fun x => XStarEdge P x × Fin (S.half - 1)) hfaceX
      · exact congrArg (fun x =>
          XStarFace P x × Fin (S.half - 1) × Fin (S.half - 1)) hfaceX
      · exact congrArg (fun x => fun v =>
          xStarVertexMember P x v = true) hfaceX
      · exact congrArg Vertex.z hz
      · exact proof_irrel_heq _ _
    have hfaceQ : rxFaceQ P S successorFace corner =
        rxOldZSelectedQCoordinate P S copy (faceQZEdge P face corner) := by
      rfl
    have hfaceZ : rxFaceZ P S successorFace = Sum.inr (oldZ, copy) := by
      simp only [successorFace, rxFaceZ, oldZFaceZ]
      rw [hz]
    constructor
    · have hxq := (rxReplacementPresentation P S).data.faceQ_xq
        successorFace corner
      change (rxReplacementPresentation P S).xq
        (rxFaceX P S successorFace) (rxFaceQ P S successorFace corner) =
          true at hxq
      rw [hfaceX', hfaceQ] at hxq
      exact hxq
    · have hqz := (rxReplacementPresentation P S).data.faceQ_qz
        successorFace corner
      change (rxReplacementPresentation P S).qz
        (rxFaceQ P S successorFace corner)
        (rxFaceZ P S successorFace) = true at hqz
      rw [hfaceQ, hfaceZ] at hqz
      exact hqz
  rcases of_decide_eq_true huse with hzero | hone
  · exact handle 0 hzero
  · exact handle 1 hone
noncomputable def rxOldZXBoundaryOwned
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (oldX : P.X) (copy : Two) (oldZ : P.Z)
    (oldMember : xStarBoundaryVertexMember P oldX
      (Vertex.z oldZ) = true)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S oldX copy oldZ oldMember)
      (Vertex.z (Sum.inr (oldZ, copy))) = true) :
    {owned : XStarBoundaryEdge (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate P S oldX copy oldZ oldMember) × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart (rxReplacementPresentation P S)
          (rxOriginalBoundaryZXCoordinate P S oldX copy oldZ oldMember))
        (xBoundaryEdgeEnd (rxReplacementPresentation P S)
          (rxOriginalBoundaryZXCoordinate P S oldX copy oldZ oldMember))
        owned.1 owned.2 =
          ⟨Vertex.z (Sum.inr (oldZ, copy)), member⟩} := by
  let incident :=
    A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2
      |>.xBoundaryIncidentEdge oldX ⟨Vertex.z oldZ, oldMember⟩
  rcases incident with ⟨⟨boundary, endpoint⟩, hendpoint⟩
  rcases boundary with ⟨raw, boundaryMember⟩
  rcases raw with impossible | edge
  · simp [xStarBoundaryEdgeMember] at boundaryMember
  · have edgeMember : xStarEdgeMember P oldX (Sum.inr edge) = true := by
      simpa [xStarBoundaryEdgeMember, xStarEdgeMember] using boundaryMember
    change BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart P oldX) (xBoundaryEdgeEnd P oldX)
        ⟨Sum.inr edge, boundaryMember⟩ endpoint =
          ⟨Vertex.z oldZ, oldMember⟩ at hendpoint
    exact rxTwoElim (motive := fun endpoint =>
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart P oldX) (xBoundaryEdgeEnd P oldX)
          ⟨Sum.inr edge, boundaryMember⟩ endpoint =
            ⟨Vertex.z oldZ, oldMember⟩ → _) (fun h => by
      rw [BDL26TannerLocalRegularity.edgeEndpoint_zero] at h
      have hraw := congrArg Subtype.val h
      cases hraw) (fun h => by
      rw [BDL26TannerLocalRegularity.edgeEndpoint_one] at h
      have hz : edge.1.2 = oldZ :=
        Vertex.z.inj (congrArg Subtype.val h)
      let successorQ := rxOldZSelectedQCoordinate P S copy edge
      have incidence := rxOldZSelectedSuccessorIncidence
        P S oldX copy oldZ oldMember edge edgeMember hz
      exact rxXBoundaryOwnedAtZ P S
        (rxOriginalBoundaryZXCoordinate P S oldX copy oldZ oldMember)
        (Sum.inr (oldZ, copy)) member successorQ incidence.1 incidence.2)
      endpoint hendpoint
noncomputable def rxRadialLocalEdgeXBoundaryOwned
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) (x : RX0 P S)
    (oldX : P.X) (copy : Two) (xqEdge : XQEdge P)
    (hstar : xStarEdgeMember P oldX (Sum.inl xqEdge) = true)
    (segment : Fin S.half)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S) x
      (Vertex.q (Sum.inl ⟨oldX,
        Sum.inl (copy, Sum.inl
          (⟨Sum.inl xqEdge, hstar⟩, segment))⟩)) = true) :
    {owned : XStarBoundaryEdge (rxReplacementPresentation P S) x × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart (rxReplacementPresentation P S) x)
        (xBoundaryEdgeEnd (rxReplacementPresentation P S) x)
        owned.1 owned.2 =
          ⟨Vertex.q (Sum.inl ⟨oldX,
            Sum.inl (copy, Sum.inl
              (⟨Sum.inl xqEdge, hstar⟩, segment))⟩), member⟩} := by
  let A' := rxReplacementAdmissible P R A4 S
  let requestedQ : (rxReplacementPresentation P S).Q :=
    Sum.inl ⟨oldX,
      Sum.inl (copy, Sum.inl
        (⟨Sum.inl xqEdge, hstar⟩, segment))⟩
  exact rxXBoundaryOwnedAtQ P S x requestedQ member (A'.qzRoot requestedQ)
noncomputable def rxLocalEdgeXBoundaryOwned
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) (x : RX0 P S)
    (oldX : P.X) (edge : DoubleCylinderEdge P oldX S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S) x
      (Vertex.q (Sum.inl ⟨oldX, edge⟩)) = true) :
    {owned : XStarBoundaryEdge (rxReplacementPresentation P S) x × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart (rxReplacementPresentation P S) x)
        (xBoundaryEdgeEnd (rxReplacementPresentation P S) x)
        owned.1 owned.2 = ⟨Vertex.q (Sum.inl ⟨oldX, edge⟩), member⟩} := by
  rcases edge with endEdge | boundaryVertex
  · rcases endEdge with ⟨copy, subdivisionEdge⟩
    rcases subdivisionEdge with original | interior
    · rcases original with ⟨starEdge, segment⟩
      rcases starEdge with ⟨rawEdge, hstar⟩
      rcases rawEdge with xqEdge | qzEdge
      · exact rxRadialLocalEdgeXBoundaryOwned
          P R A4 S x oldX copy xqEdge hstar segment member
      · generalize hselected : rxLocalEdgeXBoundaryOwnedA2Free P S x oldX
            (Sum.inl (copy, Sum.inl
              (⟨Sum.inr qzEdge, hstar⟩, segment))) member = selected
        rcases selected with owned | gap
        · exact owned
        · simp [rxLocalEdgeXBoundaryOwnedA2Free,
            rxLocalEdgeQZRootA2Free, rxLocalEdgeCornerOwnerA2Free] at hselected
    · rcases interior with horizontal | vertical
      · generalize hselected : rxLocalEdgeXBoundaryOwnedA2Free P S x oldX
            (Sum.inl (copy, Sum.inr (Sum.inl horizontal))) member = selected
        rcases selected with owned | gap
        · exact owned
        · simp [rxLocalEdgeXBoundaryOwnedA2Free,
            rxLocalEdgeQZRootA2Free, rxLocalEdgeCornerOwnerA2Free] at hselected
      · generalize hselected : rxLocalEdgeXBoundaryOwnedA2Free P S x oldX
            (Sum.inl (copy, Sum.inr (Sum.inr vertical))) member = selected
        rcases selected with owned | gap
        · exact owned
        · simp [rxLocalEdgeXBoundaryOwnedA2Free,
            rxLocalEdgeQZRootA2Free, rxLocalEdgeCornerOwnerA2Free] at hselected
  · exact rxVerticalLocalEdgeXBoundaryOwned
      P A4 S x oldX boundaryVertex member
noncomputable def rxQBoundaryXOwned
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) (x : RX0 P S)
    (q : RX1 P S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S) x
      (Vertex.q q) = true) :
    {owned : XStarBoundaryEdge (rxReplacementPresentation P S) x × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart (rxReplacementPresentation P S) x)
        (xBoundaryEdgeEnd (rxReplacementPresentation P S) x)
        owned.1 owned.2 = ⟨Vertex.q q, member⟩} := by
  rcases q with localEdge | qVertex
  · rcases localEdge with ⟨oldX, edge⟩
    exact rxLocalEdgeXBoundaryOwned P R A4 S x oldX edge member
  · rcases qVertex with ⟨oldQ, vertex⟩
    exact rxQVertexXBoundaryOwnedA2Free P
      A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissible S
      x oldQ vertex member
theorem rxXBoundaryZ_to_zBoundaryX
    (P : TannerSquarePresentation) (S : OddScale)
    (x : RX0 P S) (z : RX2 P S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S) x
      (Vertex.z z) = true) :
    zStarBoundaryVertexMember (rxReplacementPresentation P S) z
      (Vertex.x x) = true := by
  classical
  simp only [xStarBoundaryVertexMember] at member
  rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl]
    at member
  simp only [zStarBoundaryVertexMember]
  rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
  rw [decide_eq_true_eq] at member ⊢
  obtain ⟨face, hx, hz⟩ := member
  refine ⟨face, ?_, ?_⟩
  · simp only [zStarFaceMember, decide_eq_true_eq]
    rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl]
    exact hz.symm
  · have hx' : (rxReplacementPresentation P S).faceX face = x := by
      simpa [xStarFaceMember] using hx
    exact hx'.symm
noncomputable def rxLocalCellBoundaryXOwned
    (P : TannerSquarePresentation) (S : OddScale) (x : RX0 P S)
    (oldX : P.X) (cell : DoubleCylinderFace P oldX S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S) x
      (Vertex.z (Sum.inl (Sum.inl ⟨oldX, cell⟩))) = true) :
    {owned : XStarBoundaryEdge (rxReplacementPresentation P S) x × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart (rxReplacementPresentation P S) x)
        (xBoundaryEdgeEnd (rxReplacementPresentation P S) x)
        owned.1 owned.2 =
          ⟨Vertex.z (Sum.inl (Sum.inl ⟨oldX, cell⟩)), member⟩} := by
  let zMember := rxXBoundaryZ_to_zBoundaryX P S x
    (Sum.inl (Sum.inl ⟨oldX, cell⟩)) member
  by_cases h00 : x = rxLocalCellXAt P S oldX cell (0, 0)
  · subst x
    exact rxLocalCellXBoundaryOwnedAtZ P S oldX cell (0, 0) member
  · by_cases h01 : x = rxLocalCellXAt P S oldX cell (0, 1)
    · subst x
      exact rxLocalCellXBoundaryOwnedAtZ P S oldX cell (0, 1) member
    · by_cases h10 : x = rxLocalCellXAt P S oldX cell (1, 0)
      · subst x
        exact rxLocalCellXBoundaryOwnedAtZ P S oldX cell (1, 0) member
      · have h11 := (((rxLocalCellBoundaryX_cases P S oldX cell x zMember)
            |>.resolve_left h00).resolve_left h01).resolve_left h10
        subst x
        exact rxLocalCellXBoundaryOwnedAtZ P S oldX cell (1, 1) member
noncomputable def rxXBoundaryOwnedAtZTransport
    (P : TannerSquarePresentation) (S : OddScale) (z : RX2 P S)
    {x y : RX0 P S} (hxy : x = y)
    (memberX : xStarBoundaryVertexMember (rxReplacementPresentation P S) x
      (Vertex.z z) = true)
    (memberY : xStarBoundaryVertexMember (rxReplacementPresentation P S) y
      (Vertex.z z) = true)
    (ownedY : {owned :
        XStarBoundaryEdge (rxReplacementPresentation P S) y × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart (rxReplacementPresentation P S) y)
        (xBoundaryEdgeEnd (rxReplacementPresentation P S) y)
        owned.1 owned.2 = ⟨Vertex.z z, memberY⟩}) :
    {owned : XStarBoundaryEdge (rxReplacementPresentation P S) x × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart (rxReplacementPresentation P S) x)
        (xBoundaryEdgeEnd (rxReplacementPresentation P S) x)
        owned.1 owned.2 = ⟨Vertex.z z, memberX⟩} := by
  subst y
  exact ownedY
noncomputable def rxQEdgeBoundaryXOwned
    (P : TannerSquarePresentation) (S : OddScale) (x : RX0 P S)
    (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S) x
      (Vertex.z (Sum.inl (Sum.inr qEdge))) = true) :
    {owned : XStarBoundaryEdge (rxReplacementPresentation P S) x × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart (rxReplacementPresentation P S) x)
        (xBoundaryEdgeEnd (rxReplacementPresentation P S) x)
        owned.1 owned.2 =
          ⟨Vertex.z (Sum.inl (Sum.inr qEdge)), member⟩} := by
  let zMember := rxXBoundaryZ_to_zBoundaryX P S x
    (Sum.inl (Sum.inr qEdge)) member
  let hxq := rxQEdgeBoundaryX_incidence P S qEdge x zMember
  by_cases hzero : x = glueFaceX P S
      ⟨(⟨(x.1, qEdge.1), hxq⟩ : XQEdge P), qEdge.2, 0⟩
  · let memberZero : xStarBoundaryVertexMember
        (rxReplacementPresentation P S)
        (glueFaceX P S
          ⟨(⟨(x.1, qEdge.1), hxq⟩ : XQEdge P), qEdge.2, 0⟩)
        (Vertex.z (Sum.inl (Sum.inr qEdge))) = true := by
        simpa only [← hzero] using member
    let owned := rxQEdgeXBoundaryOwnedAtZEndpoint
      P S qEdge x.1 hxq 0 memberZero
    exact rxXBoundaryOwnedAtZTransport P S
      (Sum.inl (Sum.inr qEdge)) hzero member memberZero owned
  · have hone := (rxQEdgeBoundaryX_endpoints P S qEdge x zMember)
        |>.resolve_left hzero
    let memberOne : xStarBoundaryVertexMember
        (rxReplacementPresentation P S)
        (glueFaceX P S
          ⟨(⟨(x.1, qEdge.1), hxq⟩ : XQEdge P), qEdge.2, 1⟩)
        (Vertex.z (Sum.inl (Sum.inr qEdge))) = true := by
      simpa only [← hone] using member
    let owned := rxQEdgeXBoundaryOwnedAtZEndpoint
      P S qEdge x.1 hxq 1 memberOne
    exact rxXBoundaryOwnedAtZTransport P S
      (Sum.inl (Sum.inr qEdge)) hone member memberOne owned
noncomputable def rxOldZBoundaryXOwned
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : RX0 P S) (oldZ : P.Z) (copy : Two)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S) x
      (Vertex.z (Sum.inr (oldZ, copy))) = true) :
    {owned : XStarBoundaryEdge (rxReplacementPresentation P S) x × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart (rxReplacementPresentation P S) x)
        (xBoundaryEdgeEnd (rxReplacementPresentation P S) x)
        owned.1 owned.2 = ⟨Vertex.z (Sum.inr (oldZ, copy)), member⟩} := by
  let zMember := rxXBoundaryZ_to_zBoundaryX P S x
    (Sum.inr (oldZ, copy)) member
  let successorVertex : ZStarBoundaryVertex
      (rxReplacementPresentation P S) (Sum.inr (oldZ, copy)) :=
    ⟨Vertex.x x, zMember⟩
  generalize hproject : rxOldZBoundaryVertexProject
    P S oldZ copy successorVertex = oldVertex
  have mapped := rxOldZBoundaryVertexMap_project
    P S oldZ copy successorVertex
  rw [hproject] at mapped
  rcases oldVertex with ⟨oldValue, oldMember⟩
  rcases oldValue with oldX | oldQ | impossible
  · have hraw := congrArg Subtype.val mapped
    simp [rxOldZBoundaryVertexMap, successorVertex] at hraw
    have hxCopy : x = rxOldZCopyXCoordinate
        P S oldZ copy oldX oldMember := Vertex.x.inj hraw.symm
    have oldBoundaryMember : xStarBoundaryVertexMember P oldX
        (Vertex.z oldZ) = true := by
      simpa [xStarBoundaryVertexMember, xStarVertexMember] using
        (rxOldZBoundaryXStarMember P oldX oldZ oldMember)
    have hx : x = rxOriginalBoundaryZXCoordinate
        P S oldX copy oldZ oldBoundaryMember := by
      simpa [rxOldZCopyXCoordinate, rxOriginalBoundaryZXCoordinate] using hxCopy
    let targetMember : xStarBoundaryVertexMember
        (rxReplacementPresentation P S)
        (rxOriginalBoundaryZXCoordinate
          P S oldX copy oldZ oldBoundaryMember)
        (Vertex.z (Sum.inr (oldZ, copy))) = true := by
      simpa only [← hx] using member
    let owned := rxOldZXBoundaryOwned
      P A4 S oldX copy oldZ oldBoundaryMember targetMember
    exact rxXBoundaryOwnedAtZTransport P S
      (Sum.inr (oldZ, copy)) hx member targetMember owned
  · have hraw := congrArg Subtype.val mapped
    simp [rxOldZBoundaryVertexMap, successorVertex] at hraw
  · simp [zStarBoundaryVertexMember] at oldMember
noncomputable def rxReplacementXBoundaryIncidentEdge
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale)
    (x : (rxReplacementPresentation P S).X)
    (vertex : XStarBoundaryVertex (rxReplacementPresentation P S) x) :
    {owned : XStarBoundaryEdge (rxReplacementPresentation P S) x × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (xBoundaryEdgeStart (rxReplacementPresentation P S) x)
        (xBoundaryEdgeEnd (rxReplacementPresentation P S) x)
        owned.1 owned.2 = vertex} := by
  rcases vertex with ⟨value, member⟩
  rcases value with impossible | q | z
  · simp [xStarBoundaryVertexMember] at member
  · exact rxQBoundaryXOwned P R A4 S x q member
  · rcases z with localZ | oldZ
    · rcases localZ with localCell | qEdge
      · rcases localCell with ⟨oldX, cell⟩
        exact rxLocalCellBoundaryXOwned P S x oldX cell member
      · exact rxQEdgeBoundaryXOwned P S x qEdge member
    · rcases oldZ with ⟨z, copy⟩
      exact rxOldZBoundaryXOwned P A4 S x z copy member
noncomputable def rxZFaceBoundaryOwnedAtX
    (P : TannerSquarePresentation) (S : OddScale) (z : RX2 P S)
    (face : ZStarFace (rxReplacementPresentation P S) z) (corner : Two)
    (member : zStarBoundaryVertexMember (rxReplacementPresentation P S) z
      (Vertex.x (rxFaceX P S face.1)) = true) :
    {owned : ZStarBoundaryEdge (rxReplacementPresentation P S) z × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart (rxReplacementPresentation P S) z)
        (zBoundaryEdgeEnd (rxReplacementPresentation P S) z)
        owned.1 owned.2 = ⟨Vertex.x (rxFaceX P S face.1), member⟩} := by
  let edge := zStarFaceBoundaryEdge
    (rxReplacementPresentation P S) z face corner
  refine ⟨(edge, 0), ?_⟩
  rw [BDL26TannerLocalRegularity.edgeEndpoint_zero]
  apply Subtype.ext
  rfl
noncomputable def rxZFaceBoundaryOwnedAtQ
    (P : TannerSquarePresentation) (S : OddScale) (z : RX2 P S)
    (face : ZStarFace (rxReplacementPresentation P S) z) (corner : Two)
    (member : zStarBoundaryVertexMember (rxReplacementPresentation P S) z
      (Vertex.q (rxFaceQ P S face.1 corner)) = true) :
    {owned : ZStarBoundaryEdge (rxReplacementPresentation P S) z × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart (rxReplacementPresentation P S) z)
        (zBoundaryEdgeEnd (rxReplacementPresentation P S) z)
        owned.1 owned.2 =
          ⟨Vertex.q (rxFaceQ P S face.1 corner), member⟩} := by
  let edge := zStarFaceBoundaryEdge
    (rxReplacementPresentation P S) z face corner
  refine ⟨(edge, 1), ?_⟩
  rw [BDL26TannerLocalRegularity.edgeEndpoint_one]
  apply Subtype.ext
  rfl
noncomputable def rxZBoundaryOwnedTransport
    (P : TannerSquarePresentation) (S : OddScale) (z : RX2 P S)
    {first second : Vertex (rxReplacementPresentation P S)}
    (h : first = second)
    (firstMember : zStarBoundaryVertexMember
      (rxReplacementPresentation P S) z first = true)
    (secondMember : zStarBoundaryVertexMember
      (rxReplacementPresentation P S) z second = true)
    (ownedSecond : {owned :
        ZStarBoundaryEdge (rxReplacementPresentation P S) z × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart (rxReplacementPresentation P S) z)
        (zBoundaryEdgeEnd (rxReplacementPresentation P S) z)
        owned.1 owned.2 = ⟨second, secondMember⟩}) :
    {owned : ZStarBoundaryEdge (rxReplacementPresentation P S) z × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart (rxReplacementPresentation P S) z)
        (zBoundaryEdgeEnd (rxReplacementPresentation P S) z)
        owned.1 owned.2 = ⟨first, firstMember⟩} := by
  subst second
  exact ownedSecond
noncomputable def rxLocalCellZBoundaryOwnedAtXCorner
    (P : TannerSquarePresentation) (S : OddScale) (oldX : P.X)
    (cell : DoubleCylinderFace P oldX S) (newX : RX0 P S)
    (member : zStarBoundaryVertexMember (rxReplacementPresentation P S)
      (Sum.inl (Sum.inl ⟨oldX, cell⟩)) (Vertex.x newX) = true)
    (corner : Two × Two)
    (h : newX = rxLocalCellXAt P S oldX cell corner) :
    {owned : ZStarBoundaryEdge (rxReplacementPresentation P S)
        (Sum.inl (Sum.inl ⟨oldX, cell⟩)) × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart (rxReplacementPresentation P S)
          (Sum.inl (Sum.inl ⟨oldX, cell⟩)))
        (zBoundaryEdgeEnd (rxReplacementPresentation P S)
          (Sum.inl (Sum.inl ⟨oldX, cell⟩)))
        owned.1 owned.2 = ⟨Vertex.x newX, member⟩} := by
  let face := rxLocalCellZStarFace P S oldX cell corner
  have hface : newX = rxFaceX P S face.1 := by
    simpa [face, rxLocalCellXAt, rxLocalCellZStarFace, rxFaceX] using h
  let targetMember : zStarBoundaryVertexMember
      (rxReplacementPresentation P S) (Sum.inl (Sum.inl ⟨oldX, cell⟩))
      (Vertex.x (rxFaceX P S face.1)) = true := by
    simpa only [← hface] using member
  let owned := rxZFaceBoundaryOwnedAtX P S
    (Sum.inl (Sum.inl ⟨oldX, cell⟩)) face 0 targetMember
  exact rxZBoundaryOwnedTransport P S
    (Sum.inl (Sum.inl ⟨oldX, cell⟩))
    (congrArg Vertex.x hface) member targetMember owned
noncomputable def rxLocalCellZBoundaryOwnedAtQCorner
    (P : TannerSquarePresentation) (S : OddScale) (oldX : P.X)
    (cell : DoubleCylinderFace P oldX S) (newQ : RX1 P S)
    (member : zStarBoundaryVertexMember (rxReplacementPresentation P S)
      (Sum.inl (Sum.inl ⟨oldX, cell⟩)) (Vertex.q newQ) = true)
    (corner : Two × Two) (qCorner : Two)
    (h : newQ = rxLocalCellQAt P S oldX cell corner qCorner) :
    {owned : ZStarBoundaryEdge (rxReplacementPresentation P S)
        (Sum.inl (Sum.inl ⟨oldX, cell⟩)) × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart (rxReplacementPresentation P S)
          (Sum.inl (Sum.inl ⟨oldX, cell⟩)))
        (zBoundaryEdgeEnd (rxReplacementPresentation P S)
          (Sum.inl (Sum.inl ⟨oldX, cell⟩)))
        owned.1 owned.2 = ⟨Vertex.q newQ, member⟩} := by
  let face := rxLocalCellZStarFace P S oldX cell corner
  have hface : newQ = rxFaceQ P S face.1 qCorner := by
    change newQ = localFaceQAt P S ⟨oldX, cell, corner⟩ qCorner
    exact h
  let targetMember : zStarBoundaryVertexMember
      (rxReplacementPresentation P S) (Sum.inl (Sum.inl ⟨oldX, cell⟩))
      (Vertex.q (rxFaceQ P S face.1 qCorner)) = true := by
    simpa only [← hface] using member
  let owned := rxZFaceBoundaryOwnedAtQ P S
    (Sum.inl (Sum.inl ⟨oldX, cell⟩)) face qCorner targetMember
  exact rxZBoundaryOwnedTransport P S
    (Sum.inl (Sum.inl ⟨oldX, cell⟩))
    (congrArg Vertex.q hface) member targetMember owned
noncomputable def rxLocalCellZBoundaryIncidentEdgeA2Free
    (P : TannerSquarePresentation) (S : OddScale) (oldX : P.X)
    (cell : DoubleCylinderFace P oldX S)
    (vertex : ZStarBoundaryVertex (rxReplacementPresentation P S)
      (Sum.inl (Sum.inl ⟨oldX, cell⟩))) :
    {owned : ZStarBoundaryEdge (rxReplacementPresentation P S)
        (Sum.inl (Sum.inl ⟨oldX, cell⟩)) × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart (rxReplacementPresentation P S)
          (Sum.inl (Sum.inl ⟨oldX, cell⟩)))
        (zBoundaryEdgeEnd (rxReplacementPresentation P S)
          (Sum.inl (Sum.inl ⟨oldX, cell⟩)))
        owned.1 owned.2 = vertex} := by
  rcases vertex with ⟨value, member⟩
  rcases value with newX | newQ | impossible
  · by_cases h00 : newX = rxLocalCellXAt P S oldX cell (0, 0)
    · exact rxLocalCellZBoundaryOwnedAtXCorner
        P S oldX cell newX member (0, 0) h00
    · by_cases h01 : newX = rxLocalCellXAt P S oldX cell (0, 1)
      · exact rxLocalCellZBoundaryOwnedAtXCorner
          P S oldX cell newX member (0, 1) h01
      · by_cases h10 : newX = rxLocalCellXAt P S oldX cell (1, 0)
        · exact rxLocalCellZBoundaryOwnedAtXCorner
            P S oldX cell newX member (1, 0) h10
        · have h11 := (((rxLocalCellBoundaryX_cases
              P S oldX cell newX member).resolve_left h00)
              |>.resolve_left h01).resolve_left h10
          exact rxLocalCellZBoundaryOwnedAtXCorner
            P S oldX cell newX member (1, 1) h11
  · have cases := rxLocalCellBoundaryQ_cases
      P S oldX cell newQ member
    by_cases h000 : newQ = rxLocalCellQAt P S oldX cell (0, 0) 0
    · exact rxLocalCellZBoundaryOwnedAtQCorner
        P S oldX cell newQ member (0, 0) 0 h000
    · by_cases h001 : newQ = rxLocalCellQAt P S oldX cell (0, 0) 1
      · exact rxLocalCellZBoundaryOwnedAtQCorner
          P S oldX cell newQ member (0, 0) 1 h001
      · by_cases h010 : newQ = rxLocalCellQAt P S oldX cell (0, 1) 0
        · exact rxLocalCellZBoundaryOwnedAtQCorner
            P S oldX cell newQ member (0, 1) 0 h010
        · by_cases h011 : newQ = rxLocalCellQAt P S oldX cell (0, 1) 1
          · exact rxLocalCellZBoundaryOwnedAtQCorner
              P S oldX cell newQ member (0, 1) 1 h011
          · by_cases h100 : newQ = rxLocalCellQAt P S oldX cell (1, 0) 0
            · exact rxLocalCellZBoundaryOwnedAtQCorner
                P S oldX cell newQ member (1, 0) 0 h100
            · by_cases h101 : newQ = rxLocalCellQAt P S oldX cell (1, 0) 1
              · exact rxLocalCellZBoundaryOwnedAtQCorner
                  P S oldX cell newQ member (1, 0) 1 h101
              · by_cases h110 : newQ = rxLocalCellQAt P S oldX cell (1, 1) 0
                · exact rxLocalCellZBoundaryOwnedAtQCorner
                    P S oldX cell newQ member (1, 1) 0 h110
                · have remaining001 := cases.resolve_left h000
                  have remaining010 := remaining001.resolve_left h001
                  have remaining011 := remaining010.resolve_left h010
                  have remaining100 := remaining011.resolve_left h011
                  have remaining101 := remaining100.resolve_left h100
                  have remaining110 := remaining101.resolve_left h101
                  have h111 := remaining110.resolve_left h110
                  exact rxLocalCellZBoundaryOwnedAtQCorner
                    P S oldX cell newQ member (1, 1) 1 h111
  · simp [zStarBoundaryVertexMember] at member
noncomputable def rxQEdgeZBoundaryOwnedAtXEndpoint
    (P : TannerSquarePresentation) (S : OddScale)
    (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S)
    (newX : RX0 P S)
    (member : zStarBoundaryVertexMember (rxReplacementPresentation P S)
      (Sum.inl (Sum.inr qEdge)) (Vertex.x newX) = true)
    (oldX : P.X) (hxq : P.xq oldX qEdge.1 = true) (endpoint : Two)
    (h : newX = glueFaceX P S
      ⟨(⟨(oldX, qEdge.1), hxq⟩ : XQEdge P), qEdge.2, endpoint⟩) :
    {owned : ZStarBoundaryEdge (rxReplacementPresentation P S)
        (Sum.inl (Sum.inr qEdge)) × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart (rxReplacementPresentation P S)
          (Sum.inl (Sum.inr qEdge)))
        (zBoundaryEdgeEnd (rxReplacementPresentation P S)
          (Sum.inl (Sum.inr qEdge))) owned.1 owned.2 =
            ⟨Vertex.x newX, member⟩} := by
  let face := rxQEdgeGlueZStarFace P S qEdge oldX hxq endpoint
  have hface : newX = rxFaceX P S face.1 := by
    simpa [face, rxQEdgeGlueZStarFace, rxFaceX] using h
  let targetMember : zStarBoundaryVertexMember
      (rxReplacementPresentation P S) (Sum.inl (Sum.inr qEdge))
      (Vertex.x (rxFaceX P S face.1)) = true := by
    simpa only [← hface] using member
  let owned := rxZFaceBoundaryOwnedAtX P S
    (Sum.inl (Sum.inr qEdge)) face 0 targetMember
  exact rxZBoundaryOwnedTransport P S (Sum.inl (Sum.inr qEdge))
    (congrArg Vertex.x hface) member targetMember owned
noncomputable def rxQEdgeZBoundaryOwnedAtLocalQ
    (P : TannerSquarePresentation) (S : OddScale)
    (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S)
    (localEdge : Σ x : P.X, DoubleCylinderEdge P x S)
    (member : zStarBoundaryVertexMember (rxReplacementPresentation P S)
      (Sum.inl (Sum.inr qEdge)) (Vertex.q (Sum.inl localEdge)) = true) :
    {owned : ZStarBoundaryEdge (rxReplacementPresentation P S)
        (Sum.inl (Sum.inr qEdge)) × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart (rxReplacementPresentation P S)
          (Sum.inl (Sum.inr qEdge)))
        (zBoundaryEdgeEnd (rxReplacementPresentation P S)
          (Sum.inl (Sum.inr qEdge))) owned.1 owned.2 =
            ⟨Vertex.q (Sum.inl localEdge), member⟩} := by
  let hxq := rxQEdgeBoundaryLocalQ_incidence P S qEdge localEdge member
  let face := rxQEdgeGlueZStarFace P S qEdge localEdge.1 hxq 0
  have hedge := rxQEdgeBoundaryLocalQ_edge P S qEdge localEdge member
  have hface : (Sum.inl localEdge : RX1 P S) = rxFaceQ P S face.1 0 := by
    change Sum.inl localEdge = Sum.inl
      ⟨localEdge.1,
        qToXDoubleCylinderEdgeRaw P qEdge.1 localEdge.1 hxq S qEdge.2⟩
    apply congrArg Sum.inl
    rw [Sigma.ext_iff]
    exact ⟨rfl, by simpa only [heq_eq_eq] using hedge⟩
  let targetMember : zStarBoundaryVertexMember
      (rxReplacementPresentation P S) (Sum.inl (Sum.inr qEdge))
      (Vertex.q (rxFaceQ P S face.1 0)) = true := by
    simpa only [← hface] using member
  let owned := rxZFaceBoundaryOwnedAtQ P S
    (Sum.inl (Sum.inr qEdge)) face 0 targetMember
  exact rxZBoundaryOwnedTransport P S (Sum.inl (Sum.inr qEdge))
    (congrArg Vertex.q hface) member targetMember owned
noncomputable def rxQEdgeZBoundaryOwnedAtQVertexEndpoint
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S)
    (qVertex : Σ q : P.Q, QDoubleCylinderVertex P q S)
    (member : zStarBoundaryVertexMember (rxReplacementPresentation P S)
      (Sum.inl (Sum.inr qEdge)) (Vertex.q (Sum.inr qVertex)) = true)
    (endpoint : Two)
    (h : qVertex = ⟨qEdge.1,
      edgeEndpoint
        (qDoubleCylinderEdgeStart P qEdge.1 S)
        (qDoubleCylinderEdgeEnd P qEdge.1 S) qEdge.2 endpoint⟩) :
    {owned : ZStarBoundaryEdge (rxReplacementPresentation P S)
        (Sum.inl (Sum.inr qEdge)) × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart (rxReplacementPresentation P S)
          (Sum.inl (Sum.inr qEdge)))
        (zBoundaryEdgeEnd (rxReplacementPresentation P S)
          (Sum.inl (Sum.inr qEdge))) owned.1 owned.2 =
            ⟨Vertex.q (Sum.inr qVertex), member⟩} := by
  let oldX := (A.xqRoot qEdge.1).1
  let hxq := (A.xqRoot qEdge.1).2
  let face := rxQEdgeGlueZStarFace P S qEdge oldX hxq endpoint
  have hface : (Sum.inr qVertex : RX1 P S) =
      rxFaceQ P S face.1 1 := by
    apply congrArg Sum.inr
    simpa [face, glueFaceQ1] using h
  let targetMember : zStarBoundaryVertexMember
      (rxReplacementPresentation P S) (Sum.inl (Sum.inr qEdge))
      (Vertex.q (rxFaceQ P S face.1 1)) = true := by
    simpa only [← hface] using member
  let owned := rxZFaceBoundaryOwnedAtQ P S
    (Sum.inl (Sum.inr qEdge)) face 1 targetMember
  exact rxZBoundaryOwnedTransport P S (Sum.inl (Sum.inr qEdge))
    (congrArg Vertex.q hface) member targetMember owned
noncomputable def rxQEdgeZBoundaryIncidentEdgeA2Free
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S)
    (vertex : ZStarBoundaryVertex (rxReplacementPresentation P S)
      (Sum.inl (Sum.inr qEdge))) :
    {owned : ZStarBoundaryEdge (rxReplacementPresentation P S)
        (Sum.inl (Sum.inr qEdge)) × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart (rxReplacementPresentation P S)
          (Sum.inl (Sum.inr qEdge)))
        (zBoundaryEdgeEnd (rxReplacementPresentation P S)
          (Sum.inl (Sum.inr qEdge))) owned.1 owned.2 = vertex} := by
  rcases vertex with ⟨value, member⟩
  rcases value with newX | newQ | impossible
  · let hxq := rxQEdgeBoundaryX_incidence P S qEdge newX member
    by_cases hzero : newX = glueFaceX P S
        ⟨(⟨(newX.1, qEdge.1), hxq⟩ : XQEdge P), qEdge.2, 0⟩
    · exact rxQEdgeZBoundaryOwnedAtXEndpoint
        P S qEdge newX member newX.1 hxq 0 hzero
    · have hone := (rxQEdgeBoundaryX_endpoints P S qEdge newX member)
          |>.resolve_left hzero
      exact rxQEdgeZBoundaryOwnedAtXEndpoint
        P S qEdge newX member newX.1 hxq 1 hone
  · rcases newQ with localEdge | qVertex
    · exact rxQEdgeZBoundaryOwnedAtLocalQ
        P S qEdge localEdge member
    · by_cases hstart : qVertex = ⟨qEdge.1,
          qDoubleCylinderEdgeStart P qEdge.1 S qEdge.2⟩
      · exact rxQEdgeZBoundaryOwnedAtQVertexEndpoint
          P A S qEdge qVertex member 0 (by simpa [edgeEndpoint] using hstart)
      · have hend := (rxQEdgeBoundaryQVertex_endpoints
            P S qEdge qVertex member).resolve_left hstart
        exact rxQEdgeZBoundaryOwnedAtQVertexEndpoint
          P A S qEdge qVertex member 1 (by simpa [edgeEndpoint] using hend)
  · simp [zStarBoundaryVertexMember] at member
noncomputable def rxOldZBoundaryIncidentEdgeA2
    (P : TannerSquarePresentation) (A2 : TannerSquareAdmissibleV2 P)
    (S : OddScale) (oldZ : P.Z) (copy : Two)
    (vertex : ZStarBoundaryVertex (rxReplacementPresentation P S)
      (Sum.inr (oldZ, copy))) :
    {owned : ZStarBoundaryEdge (rxReplacementPresentation P S)
        (Sum.inr (oldZ, copy)) × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart (rxReplacementPresentation P S)
          (Sum.inr (oldZ, copy)))
        (zBoundaryEdgeEnd (rxReplacementPresentation P S)
          (Sum.inr (oldZ, copy))) owned.1 owned.2 = vertex} := by
  let oldVertex := rxOldZBoundaryVertexProject P S oldZ copy vertex
  let selected := A2.zBoundaryIncidentEdge oldZ oldVertex
  rcases selected with ⟨⟨oldEdge, oldBit⟩, hendpoint⟩
  let successorEdge := rxOldZBoundaryEdgeMap P S oldZ copy oldEdge
  have mappedVertex := rxOldZBoundaryVertexMap_project
    P S oldZ copy vertex
  rcases vertex with ⟨value, member⟩
  rcases value with newX | newQ | impossible
  · exact rxTwoElim (motive := fun bit =>
        BDL26TannerLocalRegularity.edgeEndpoint
          (zBoundaryEdgeStart P oldZ) (zBoundaryEdgeEnd P oldZ)
          oldEdge bit = oldVertex →
        {owned : ZStarBoundaryEdge (rxReplacementPresentation P S)
            (Sum.inr (oldZ, copy)) × Two //
          BDL26TannerLocalRegularity.edgeEndpoint
            (zBoundaryEdgeStart (rxReplacementPresentation P S)
              (Sum.inr (oldZ, copy)))
            (zBoundaryEdgeEnd (rxReplacementPresentation P S)
              (Sum.inr (oldZ, copy))) owned.1 owned.2 =
                ⟨Vertex.x newX, member⟩}) (fun hendpoint => by
      refine ⟨(successorEdge, 0), ?_⟩
      rw [BDL26TannerLocalRegularity.edgeEndpoint_zero]
      calc
        zBoundaryEdgeStart (rxReplacementPresentation P S)
            (Sum.inr (oldZ, copy)) successorEdge =
            rxOldZBoundaryVertexMap P S oldZ copy
              (zBoundaryEdgeStart P oldZ oldEdge) :=
          rxOldZBoundaryEdgeMap_start P S oldZ copy oldEdge
        _ = rxOldZBoundaryVertexMap P S oldZ copy oldVertex := by
          rw [BDL26TannerLocalRegularity.edgeEndpoint_zero] at hendpoint
          exact congrArg (rxOldZBoundaryVertexMap P S oldZ copy) hendpoint
        _ = ⟨Vertex.x newX, member⟩ := mappedVertex) (fun hendpoint => by
      have hwrong : zBoundaryEdgeEnd (rxReplacementPresentation P S)
          (Sum.inr (oldZ, copy)) successorEdge =
          ⟨Vertex.x newX, member⟩ := by
        calc
          zBoundaryEdgeEnd (rxReplacementPresentation P S)
              (Sum.inr (oldZ, copy)) successorEdge =
              rxOldZBoundaryVertexMap P S oldZ copy
                (zBoundaryEdgeEnd P oldZ oldEdge) :=
            rxOldZBoundaryEdgeMap_end P S oldZ copy oldEdge
          _ = rxOldZBoundaryVertexMap P S oldZ copy oldVertex := by
            rw [BDL26TannerLocalRegularity.edgeEndpoint_one] at hendpoint
            exact congrArg (rxOldZBoundaryVertexMap P S oldZ copy) hendpoint
          _ = ⟨Vertex.x newX, member⟩ := mappedVertex
      have hraw := congrArg Subtype.val hwrong
      rcases oldEdge with ⟨rawEdge, oldEdgeMember⟩
      rcases rawEdge with xqEdge | impossibleEdge
      · simp [successorEdge, rxOldZBoundaryEdgeMap,
          zBoundaryEdgeEnd] at hraw
      · simp [zStarBoundaryEdgeMember] at oldEdgeMember) oldBit hendpoint
  · exact rxTwoElim (motive := fun bit =>
        BDL26TannerLocalRegularity.edgeEndpoint
          (zBoundaryEdgeStart P oldZ) (zBoundaryEdgeEnd P oldZ)
          oldEdge bit = oldVertex →
        {owned : ZStarBoundaryEdge (rxReplacementPresentation P S)
            (Sum.inr (oldZ, copy)) × Two //
          BDL26TannerLocalRegularity.edgeEndpoint
            (zBoundaryEdgeStart (rxReplacementPresentation P S)
              (Sum.inr (oldZ, copy)))
            (zBoundaryEdgeEnd (rxReplacementPresentation P S)
              (Sum.inr (oldZ, copy))) owned.1 owned.2 =
                ⟨Vertex.q newQ, member⟩}) (fun hendpoint => by
      have hwrong : zBoundaryEdgeStart (rxReplacementPresentation P S)
          (Sum.inr (oldZ, copy)) successorEdge =
          ⟨Vertex.q newQ, member⟩ := by
        calc
          zBoundaryEdgeStart (rxReplacementPresentation P S)
              (Sum.inr (oldZ, copy)) successorEdge =
              rxOldZBoundaryVertexMap P S oldZ copy
                (zBoundaryEdgeStart P oldZ oldEdge) :=
            rxOldZBoundaryEdgeMap_start P S oldZ copy oldEdge
          _ = rxOldZBoundaryVertexMap P S oldZ copy oldVertex := by
            rw [BDL26TannerLocalRegularity.edgeEndpoint_zero] at hendpoint
            exact congrArg (rxOldZBoundaryVertexMap P S oldZ copy) hendpoint
          _ = ⟨Vertex.q newQ, member⟩ := mappedVertex
      have hraw := congrArg Subtype.val hwrong
      rcases oldEdge with ⟨rawEdge, oldEdgeMember⟩
      rcases rawEdge with xqEdge | impossibleEdge
      · simp [successorEdge, rxOldZBoundaryEdgeMap,
          zBoundaryEdgeStart] at hraw
      · simp [zStarBoundaryEdgeMember] at oldEdgeMember) (fun hendpoint => by
      refine ⟨(successorEdge, 1), ?_⟩
      rw [BDL26TannerLocalRegularity.edgeEndpoint_one]
      calc
        zBoundaryEdgeEnd (rxReplacementPresentation P S)
            (Sum.inr (oldZ, copy)) successorEdge =
            rxOldZBoundaryVertexMap P S oldZ copy
              (zBoundaryEdgeEnd P oldZ oldEdge) :=
          rxOldZBoundaryEdgeMap_end P S oldZ copy oldEdge
        _ = rxOldZBoundaryVertexMap P S oldZ copy oldVertex := by
          rw [BDL26TannerLocalRegularity.edgeEndpoint_one] at hendpoint
          exact congrArg (rxOldZBoundaryVertexMap P S oldZ copy) hendpoint
        _ = ⟨Vertex.q newQ, member⟩ := mappedVertex) oldBit hendpoint
  · simp [zStarBoundaryVertexMember] at member
noncomputable def rxReplacementZBoundaryIncidentEdge
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : (rxReplacementPresentation P S).Z)
    (vertex : ZStarBoundaryVertex (rxReplacementPresentation P S) z) :
    {owned : ZStarBoundaryEdge (rxReplacementPresentation P S) z × Two //
      BDL26TannerLocalRegularity.edgeEndpoint
        (zBoundaryEdgeStart (rxReplacementPresentation P S) z)
        (zBoundaryEdgeEnd (rxReplacementPresentation P S) z)
        owned.1 owned.2 = vertex} := by
  let A2 := A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissibleV2
  let A := A2.toTannerSquareAdmissible
  rcases z with localOrQEdge | oldZ
  · rcases localOrQEdge with localCell | qEdge
    · exact rxLocalCellZBoundaryIncidentEdgeA2Free
        P S localCell.1 localCell.2 vertex
    · exact rxQEdgeZBoundaryIncidentEdgeA2Free
        P A S qEdge vertex
  · exact rxOldZBoundaryIncidentEdgeA2
      P A2 S oldZ.1 oldZ.2 vertex
noncomputable def rxReplacementAdmissibleV2
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) :
    TannerSquareAdmissibleV2 (rxReplacementPresentation P S) where
  toTannerSquareAdmissible := rxReplacementAdmissible P R A4 S
  xBoundaryIncidentEdge := rxReplacementXBoundaryIncidentEdge P R A4 S
  zBoundaryIncidentEdge := rxReplacementZBoundaryIncidentEdge P A4 S
theorem rxXRadialEdge_ownerX
    (P : TannerSquarePresentation) (S : OddScale)
    (x : (rxReplacementPresentation P S).X)
    (edge : XQEdge (rxReplacementPresentation P S))
    (member : xStarEdgeMember (rxReplacementPresentation P S) x
      (Sum.inl edge) = true) :
    edge.1.1 = x := by
  let starEdge : XStarEdge (rxReplacementPresentation P S) x :=
    ⟨Sum.inl edge, member⟩
  have startMember :=
    (xStarEdgeStart (rxReplacementPresentation P S) x starEdge).2
  change decide (edge.1.1 = x) = true at startMember
  exact of_decide_eq_true startMember
theorem rxLocalEdgeXCoordinate_endpoint_cases
    (P : TannerSquarePresentation) (S : OddScale)
    (xCoordinate : RX0 P S) (oldX : P.X)
    (edge : DoubleCylinderEdge P oldX S)
    (incidence : rxXQIncidence P S xCoordinate
      (Sum.inl ⟨oldX, edge⟩) = true) :
    xCoordinate =
        ⟨oldX, tannerDoubleCylinderEdgeStart P oldX S edge⟩ ∨
      xCoordinate =
        ⟨oldX, tannerDoubleCylinderEdgeEnd P oldX S edge⟩ := by
  obtain ⟨face, corner, hfaceX, hfaceQ⟩ :=
    (rxXQIncidence_eq_true_iff P S xCoordinate
      (Sum.inl ⟨oldX, edge⟩)).1 incidence
  obtain ⟨endpoint, hendpoint⟩ :=
    rxFaceX_eq_endpoint_of_faceQ_eq_xEdge
      P S face corner oldX edge hfaceQ
  have hx : xCoordinate =
      ⟨oldX, edgeEndpoint
        (tannerDoubleCylinderEdgeStart P oldX S)
        (tannerDoubleCylinderEdgeEnd P oldX S) edge endpoint⟩ :=
    hfaceX.symm.trans hendpoint
  exact rxTwoElim (motive := fun endpoint =>
      xCoordinate =
          ⟨oldX, edgeEndpoint
            (tannerDoubleCylinderEdgeStart P oldX S)
            (tannerDoubleCylinderEdgeEnd P oldX S) edge endpoint⟩ →
        xCoordinate =
            ⟨oldX, tannerDoubleCylinderEdgeStart P oldX S edge⟩ ∨
          xCoordinate =
            ⟨oldX, tannerDoubleCylinderEdgeEnd P oldX S edge⟩)
    (fun h => Or.inl (by simpa [edgeEndpoint] using h))
    (fun h => Or.inr (by simpa [edgeEndpoint] using h)) endpoint hx
noncomputable def rxLocalEdgeXRadialFaceOwnerAtEndpoint
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (xCoordinate : RX0 P S) (oldX : P.X)
    (edge : DoubleCylinderEdge P oldX S)
    (incidence : rxXQIncidence P S xCoordinate
      (Sum.inl ⟨oldX, edge⟩) = true)
    (starMember : xStarEdgeMember (rxReplacementPresentation P S) xCoordinate
      (Sum.inl
        (⟨(xCoordinate, Sum.inl ⟨oldX, edge⟩), incidence⟩ :
          XQEdge (rxReplacementPresentation P S))) = true)
    (endpoint : Two)
    (hendpoint : xCoordinate =
      ⟨oldX, edgeEndpoint
        (tannerDoubleCylinderEdgeStart P oldX S)
        (tannerDoubleCylinderEdgeEnd P oldX S) edge endpoint⟩) :
    {owner : XStarFace (rxReplacementPresentation P S) xCoordinate × Two //
      xStarFaceXQEdge (rxReplacementPresentation P S) xCoordinate
          owner.1 owner.2 =
        ⟨Sum.inl
          (⟨(xCoordinate, Sum.inl ⟨oldX, edge⟩), incidence⟩ :
            XQEdge (rxReplacementPresentation P S)), starMember⟩} := by
  obtain ⟨⟨⟨ownerX, localCell, materialCorner⟩, qCorner⟩, hq⟩ :=
    rxLocalEdgeCornerOwner P A3 S oldX edge
  have hsigma : (⟨ownerX,
      if qCorner = 0 then
        localFaceQ0EdgeAt P ownerX S localCell materialCorner
      else localFaceQ1EdgeAt P ownerX S localCell materialCorner⟩ :
        Σ ownerX : P.X, DoubleCylinderEdge P ownerX S) =
      ⟨oldX, edge⟩ := by
    fin_cases qCorner
    · simpa [localFaceQAt, localFaceQ0, localFaceQ0Edge] using hq
    · simpa [localFaceQAt, localFaceQ1, localFaceQ1Edge] using hq
  have hownerX : ownerX = oldX := congrArg Sigma.fst hsigma
  subst ownerX
  have hedge :
      (if qCorner = 0 then
          localFaceQ0EdgeAt P oldX S localCell materialCorner
        else localFaceQ1EdgeAt P oldX S localCell materialCorner) = edge :=
    eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2
  let newMaterial := localMaterialCornerAtEndpoint
    P oldX S localCell materialCorner qCorner endpoint
  let localFace : RXLocalFace P S := ⟨oldX, localCell, newMaterial⟩
  let rawFace : RXFace P S := Sum.inl localFace
  have hfaceX : rxFaceX P S rawFace = xCoordinate := by
    change localFaceX P S localFace = xCoordinate
    rw [show localFaceX P S localFace =
        ⟨oldX, edgeEndpoint
          (tannerDoubleCylinderEdgeStart P oldX S)
          (tannerDoubleCylinderEdgeEnd P oldX S)
          (if qCorner = 0 then
            localFaceQ0EdgeAt P oldX S localCell materialCorner
          else localFaceQ1EdgeAt P oldX S localCell materialCorner)
          endpoint⟩ by
      simpa [localFace, newMaterial] using
        localFaceX_atEndpoint P oldX S localCell materialCorner
          qCorner endpoint]
    rw [hedge]
    exact hendpoint.symm
  have hfaceQ : rxFaceQ P S rawFace qCorner =
      Sum.inl ⟨oldX, edge⟩ := by
    change localFaceQAt P S localFace qCorner = Sum.inl ⟨oldX, edge⟩
    calc
      localFaceQAt P S localFace qCorner =
          localFaceQAt P S ⟨oldX, localCell, materialCorner⟩ qCorner := by
        simpa [localFace, newMaterial, localFaceQAt] using
          localFaceQ_atEndpoint P oldX S localCell materialCorner
            qCorner endpoint
      _ = Sum.inl ⟨oldX, edge⟩ := hq
  let starFace : XStarFace
      (rxReplacementPresentation P S) xCoordinate :=
    ⟨rawFace, by
      simp only [xStarFaceMember, decide_eq_true_eq]
      rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
      exact hfaceX⟩
  refine ⟨(starFace, qCorner), ?_⟩
  apply Subtype.ext
  apply congrArg Sum.inl
  apply Subtype.ext
  exact Prod.ext hfaceX hfaceQ
noncomputable def rxLocalEdgeXRadialFaceOwner
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (xCoordinate : RX0 P S) (oldX : P.X)
    (edge : DoubleCylinderEdge P oldX S)
    (incidence : rxXQIncidence P S xCoordinate
      (Sum.inl ⟨oldX, edge⟩) = true)
    (starMember : xStarEdgeMember (rxReplacementPresentation P S) xCoordinate
      (Sum.inl
        (⟨(xCoordinate, Sum.inl ⟨oldX, edge⟩), incidence⟩ :
          XQEdge (rxReplacementPresentation P S))) = true) :
    {owner : XStarFace (rxReplacementPresentation P S) xCoordinate × Two //
      xStarFaceXQEdge (rxReplacementPresentation P S) xCoordinate
          owner.1 owner.2 =
        ⟨Sum.inl
          (⟨(xCoordinate, Sum.inl ⟨oldX, edge⟩), incidence⟩ :
            XQEdge (rxReplacementPresentation P S)), starMember⟩} := by
  by_cases hstart : xCoordinate =
      ⟨oldX, tannerDoubleCylinderEdgeStart P oldX S edge⟩
  · exact rxLocalEdgeXRadialFaceOwnerAtEndpoint
      P A3 S xCoordinate oldX edge incidence starMember 0
      (by simpa [edgeEndpoint] using hstart)
  · have hend :=
      (rxLocalEdgeXCoordinate_endpoint_cases
        P S xCoordinate oldX edge incidence).resolve_left hstart
    exact rxLocalEdgeXRadialFaceOwnerAtEndpoint
      P A3 S xCoordinate oldX edge incidence starMember 1
      (by simpa [edgeEndpoint] using hend)
theorem rxQVertexXRadial_oldXQ
    (P : TannerSquarePresentation) (S : OddScale)
    (xCoordinate : RX0 P S) (q : P.Q)
    (vertex : QDoubleCylinderVertex P q S)
    (incidence : rxXQIncidence P S xCoordinate
      (Sum.inr ⟨q, vertex⟩) = true) :
    P.xq xCoordinate.1 q = true := by
  obtain ⟨face, corner, hx, hq⟩ :=
    (rxXQIncidence_eq_true_iff P S xCoordinate
      (Sum.inr ⟨q, vertex⟩)).1 incidence
  rcases face with localFace | glue | oldFace
  · rcases localFace with ⟨oldX, cell, material⟩
    fin_cases corner <;> simp [rxFaceQ, localFaceQAt, localFaceQ0,
      localFaceQ1] at hq
  · rcases glue with ⟨edge, qEdge, endpoint⟩
    have hx' : edge.1.1 = xCoordinate.1 :=
      congrArg Sigma.fst hx
    fin_cases corner
    · simp [rxFaceQ, glueFaceQ0] at hq
    · have hq' : edge.1.2 = q :=
        congrArg Sigma.fst (Sum.inr.inj hq)
      simpa [hx', hq'] using edge.2
  · rcases oldFace with ⟨face, copy⟩
    have hx' : P.faceX face = xCoordinate.1 :=
      congrArg Sigma.fst hx
    have hq' : P.faceQ face corner = q :=
      congrArg Sigma.fst (Sum.inr.inj hq)
    simpa [hx', hq'] using P.data.faceQ_xq face corner
theorem rxQVertexGlueFaceX_eq
    (P : TannerSquarePresentation) (S : OddScale)
    (xCoordinate : RX0 P S) (q : P.Q)
    (vertex : QDoubleCylinderVertex P q S)
    (incidence : rxXQIncidence P S xCoordinate
      (Sum.inr ⟨q, vertex⟩) = true)
    (hxq : P.xq xCoordinate.1 q = true)
    (qEdge : QDoubleCylinderEdge P q S) (endpoint : Two)
    (hendpoint : edgeEndpoint
      (qDoubleCylinderEdgeStart P q S)
      (qDoubleCylinderEdgeEnd P q S) qEdge endpoint = vertex) :
    glueFaceX P S
        ⟨(⟨(xCoordinate.1, q), hxq⟩ : XQEdge P), qEdge, endpoint⟩ =
      xCoordinate := by
  rcases xCoordinate with ⟨oldX, xVertex⟩
  obtain ⟨face, corner, hfaceX, hfaceQ⟩ :=
    (rxXQIncidence_eq_true_iff P S ⟨oldX, xVertex⟩
      (Sum.inr ⟨q, vertex⟩)).1 incidence
  rcases face with localFace | glue | oldFace
  · rcases localFace with ⟨ownerX, cell, material⟩
    fin_cases corner <;> simp [rxFaceQ, localFaceQAt, localFaceQ0,
      localFaceQ1] at hfaceQ
  · rcases glue with
      ⟨⟨⟨firstX, firstQ⟩, firstHXQ⟩, firstEdge, firstEndpoint⟩
    fin_cases corner
    · cases hfaceQ
    · have htag :
          (⟨firstQ, edgeEndpoint
            (qDoubleCylinderEdgeStart P firstQ S)
            (qDoubleCylinderEdgeEnd P firstQ S)
            firstEdge firstEndpoint⟩ :
              Σ oldQ : P.Q, QDoubleCylinderVertex P oldQ S) =
            ⟨q, vertex⟩ :=
        Sum.inr.inj hfaceQ
      have hbase : firstQ = q := congrArg Sigma.fst htag
      subst firstQ
      have hfirstVertex : edgeEndpoint
          (qDoubleCylinderEdgeStart P q S)
          (qDoubleCylinderEdgeEnd P q S) firstEdge firstEndpoint = vertex :=
        eq_of_heq (Sigma.mk.inj_iff.mp htag).2
      have hfirstX : firstX = oldX := congrArg Sigma.fst hfaceX
      subst firstX
      have hmapped := qToXDoubleCylinderEdgeRaw_endpoint_congr
        P q oldX hxq S qEdge firstEdge endpoint firstEndpoint
          (hendpoint.trans hfirstVertex.symm)
      calc
        glueFaceX P S
            ⟨(⟨(oldX, q), hxq⟩ : XQEdge P), qEdge, endpoint⟩ =
            glueFaceX P S
              ⟨(⟨(oldX, q), firstHXQ⟩ : XQEdge P),
                firstEdge, firstEndpoint⟩ := by
          simpa [glueFaceX] using
            congrArg (fun target => (⟨oldX, target⟩ : RX0 P S)) hmapped
        _ = ⟨oldX, xVertex⟩ := by
          simpa [rxFaceX] using hfaceX
  · rcases oldFace with ⟨oldFace, copy⟩
    have htag :
        (⟨P.faceQ oldFace corner,
            (copy, Sum.inl (Sum.inr
            (⟨P.faceZ oldFace,
              P.data.faceQ_qz oldFace corner⟩ :
                QStarEdge P (P.faceQ oldFace corner))))⟩ :
            Σ oldQ : P.Q, QDoubleCylinderVertex P oldQ S) =
          ⟨q, vertex⟩ :=
      Sum.inr.inj hfaceQ
    have hbase : P.faceQ oldFace corner = q :=
      congrArg Sigma.fst htag
    have hownerX : P.faceX oldFace = oldX :=
      congrArg Sigma.fst hfaceX
    let hqz : P.qz q (P.faceZ oldFace) = true := by
      simpa [hbase] using P.data.faceQ_qz oldFace corner
    have hterminal :
        (copy, Sum.inl (Sum.inr
          (⟨P.faceZ oldFace, hqz⟩ : QStarEdge P q))) = vertex := by
      cases hbase
      exact eq_of_heq (Sigma.mk.inj_iff.mp htag).2
    have hbridge := qToXDoubleCylinderEdgeRaw_endpoint_eq_oldZFaceX
      P S oldX q (P.faceZ oldFace) hxq hqz qEdge endpoint
        oldFace corner copy hownerX rfl hbase
        (hendpoint.trans hterminal.symm)
    calc
      glueFaceX P S
          ⟨(⟨(oldX, q), hxq⟩ : XQEdge P), qEdge, endpoint⟩ =
          oldZFaceX P S (oldFace, copy) := by
        simpa [glueFaceX] using hbridge
      _ = ⟨oldX, xVertex⟩ := by
        simpa [rxFaceX] using hfaceX
noncomputable def rxQVertexXRadialFaceOwner
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (xCoordinate : RX0 P S) (q : P.Q)
    (vertex : QDoubleCylinderVertex P q S)
    (incidence : rxXQIncidence P S xCoordinate
      (Sum.inr ⟨q, vertex⟩) = true)
    (starMember : xStarEdgeMember (rxReplacementPresentation P S) xCoordinate
      (Sum.inl
        (⟨(xCoordinate, Sum.inr ⟨q, vertex⟩), incidence⟩ :
          XQEdge (rxReplacementPresentation P S))) = true) :
    {owner : XStarFace (rxReplacementPresentation P S) xCoordinate × Two //
      xStarFaceXQEdge (rxReplacementPresentation P S) xCoordinate
          owner.1 owner.2 =
        ⟨Sum.inl
          (⟨(xCoordinate, Sum.inr ⟨q, vertex⟩), incidence⟩ :
            XQEdge (rxReplacementPresentation P S)), starMember⟩} := by
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  obtain ⟨⟨qEdge, endpoint⟩, hendpoint⟩ :=
    rxQDoubleCylinderVertexIncidentEdge P A q S vertex
  have hendpoint' : edgeEndpoint
      (qDoubleCylinderEdgeStart P q S)
      (qDoubleCylinderEdgeEnd P q S) qEdge endpoint = vertex :=
    rxTwoElim (motive := fun endpoint =>
      BDL26TannerLocalRegularity.edgeEndpoint
          (qDoubleCylinderEdgeStart P q S)
          (qDoubleCylinderEdgeEnd P q S) qEdge endpoint = vertex →
        edgeEndpoint (qDoubleCylinderEdgeStart P q S)
          (qDoubleCylinderEdgeEnd P q S) qEdge endpoint = vertex)
      (fun h => h) (fun h => h) endpoint hendpoint
  let hxq := rxQVertexXRadial_oldXQ P S xCoordinate q vertex incidence
  let glue : RXXQGlueFace P S :=
    ⟨(⟨(xCoordinate.1, q), hxq⟩ : XQEdge P), qEdge, endpoint⟩
  have hfaceX : glueFaceX P S glue = xCoordinate :=
    rxQVertexGlueFaceX_eq P S xCoordinate q vertex incidence hxq
      qEdge endpoint hendpoint'
  have hfaceQ : glueFaceQ1 P S glue = Sum.inr ⟨q, vertex⟩ := by
    apply congrArg Sum.inr
    change (⟨q, edgeEndpoint
      (qDoubleCylinderEdgeStart P q S)
      (qDoubleCylinderEdgeEnd P q S) qEdge endpoint⟩ :
        Σ oldQ : P.Q, QDoubleCylinderVertex P oldQ S) = ⟨q, vertex⟩
    rw [Sigma.ext_iff]
    exact ⟨rfl, by simpa only [heq_eq_eq] using hendpoint'⟩
  let rawFace : RXFace P S := Sum.inr (Sum.inl glue)
  let starFace : XStarFace
      (rxReplacementPresentation P S) xCoordinate :=
    ⟨rawFace, by
      simp only [xStarFaceMember, decide_eq_true_eq]
      rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
      exact hfaceX⟩
  refine ⟨(starFace, 1), ?_⟩
  apply Subtype.ext
  apply congrArg Sum.inl
  apply Subtype.ext
  exact Prod.ext hfaceX hfaceQ
noncomputable def rxReplacementXRadialFaceOwner
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (x : (rxReplacementPresentation P S).X)
    (edge : XQEdge (rxReplacementPresentation P S))
    (member : xStarEdgeMember (rxReplacementPresentation P S) x
      (Sum.inl edge) = true) :
    {owner : XStarFace (rxReplacementPresentation P S) x × Two //
      xStarFaceXQEdge (rxReplacementPresentation P S) x
          owner.1 owner.2 = ⟨Sum.inl edge, member⟩} := by
  rcases edge with ⟨⟨xCoordinate, rawQ⟩, incidence⟩
  have howner : xCoordinate = x :=
    rxXRadialEdge_ownerX P S x
      ⟨(xCoordinate, rawQ), incidence⟩ member
  subst xCoordinate
  rcases rawQ with localEdge | qVertex
  · rcases localEdge with ⟨oldX, localEdge⟩
    exact rxLocalEdgeXRadialFaceOwner
      P A3 S x oldX localEdge incidence member
  · rcases qVertex with ⟨q, vertex⟩
    exact rxQVertexXRadialFaceOwner
      P A3 S x q vertex incidence member
theorem rxLocalCellZRadial_qBoundaryMember
    (P : TannerSquarePresentation) (S : OddScale) (oldX : P.X)
    (cell : DoubleCylinderFace P oldX S) (newQ : RX1 P S)
    (incidence : rxQZIncidence P S newQ
      (Sum.inl (Sum.inl ⟨oldX, cell⟩)) = true)
    (member : zStarEdgeMember (rxReplacementPresentation P S)
      (Sum.inl (Sum.inl ⟨oldX, cell⟩))
      (Sum.inr
        (⟨(newQ, Sum.inl (Sum.inl ⟨oldX, cell⟩)), incidence⟩ :
          QZEdge (rxReplacementPresentation P S))) = true) :
    zStarBoundaryVertexMember (rxReplacementPresentation P S)
      (Sum.inl (Sum.inl ⟨oldX, cell⟩)) (Vertex.q newQ) = true := by
  classical
  simp only [zStarEdgeMember, decide_eq_true_eq] at member
  obtain ⟨face, hz, huse⟩ := member
  change decide
        ((⟨(newQ, Sum.inl (Sum.inl ⟨oldX, cell⟩)), incidence⟩ :
              QZEdge (rxReplacementPresentation P S)) =
            faceQZEdge (rxReplacementPresentation P S) face 0 ∨
          (⟨(newQ, Sum.inl (Sum.inl ⟨oldX, cell⟩)), incidence⟩ :
              QZEdge (rxReplacementPresentation P S)) =
            faceQZEdge (rxReplacementPresentation P S) face 1) = true at huse
  rw [decide_eq_true_eq] at huse
  simp only [zStarBoundaryVertexMember, decide_eq_true_eq]
  change (exists face : RXFace P S,
    zStarFaceMember (rxReplacementPresentation P S)
        (Sum.inl (Sum.inl ⟨oldX, cell⟩)) face = true ∧
      (newQ = rxFaceQ P S face 0 ∨ newQ = rxFaceQ P S face 1))
  refine ⟨face, hz, ?_⟩
  rcases huse with hzero | hone
  · exact Or.inl (congrArg
      (fun selected : QZEdge (rxReplacementPresentation P S) =>
        selected.1.1) hzero)
  · exact Or.inr (congrArg
      (fun selected : QZEdge (rxReplacementPresentation P S) =>
        selected.1.1) hone)
noncomputable def rxLocalCellZRadialFaceOwnerAtQCorner
    (P : TannerSquarePresentation) (S : OddScale) (oldX : P.X)
    (cell : DoubleCylinderFace P oldX S) (newQ : RX1 P S)
    (incidence : rxQZIncidence P S newQ
      (Sum.inl (Sum.inl ⟨oldX, cell⟩)) = true)
    (member : zStarEdgeMember (rxReplacementPresentation P S)
      (Sum.inl (Sum.inl ⟨oldX, cell⟩))
      (Sum.inr
        (⟨(newQ, Sum.inl (Sum.inl ⟨oldX, cell⟩)), incidence⟩ :
          QZEdge (rxReplacementPresentation P S))) = true)
    (corner : Two × Two) (qCorner : Two)
    (h : newQ = rxLocalCellQAt P S oldX cell corner qCorner) :
    {owner : ZStarFace (rxReplacementPresentation P S)
        (Sum.inl (Sum.inl ⟨oldX, cell⟩)) × Two //
      zStarFaceQZEdge (rxReplacementPresentation P S)
          (Sum.inl (Sum.inl ⟨oldX, cell⟩)) owner.1 owner.2 =
        ⟨Sum.inr
          (⟨(newQ, Sum.inl (Sum.inl ⟨oldX, cell⟩)), incidence⟩ :
            QZEdge (rxReplacementPresentation P S)), member⟩} := by
  let face := rxLocalCellZStarFace P S oldX cell corner
  have hfaceQ : rxFaceQ P S face.1 qCorner = newQ := by
    change localFaceQAt P S ⟨oldX, cell, corner⟩ qCorner = newQ
    exact h.symm
  have hfaceZ : rxFaceZ P S face.1 =
      Sum.inl (Sum.inl ⟨oldX, cell⟩) := rfl
  refine ⟨(face, qCorner), ?_⟩
  apply Subtype.ext
  apply congrArg Sum.inr
  apply Subtype.ext
  exact Prod.ext hfaceQ hfaceZ
noncomputable def rxLocalCellZRadialFaceOwner
    (P : TannerSquarePresentation) (S : OddScale) (oldX : P.X)
    (cell : DoubleCylinderFace P oldX S) (newQ : RX1 P S)
    (incidence : rxQZIncidence P S newQ
      (Sum.inl (Sum.inl ⟨oldX, cell⟩)) = true)
    (member : zStarEdgeMember (rxReplacementPresentation P S)
      (Sum.inl (Sum.inl ⟨oldX, cell⟩))
      (Sum.inr
        (⟨(newQ, Sum.inl (Sum.inl ⟨oldX, cell⟩)), incidence⟩ :
          QZEdge (rxReplacementPresentation P S))) = true) :
    {owner : ZStarFace (rxReplacementPresentation P S)
        (Sum.inl (Sum.inl ⟨oldX, cell⟩)) × Two //
      zStarFaceQZEdge (rxReplacementPresentation P S)
          (Sum.inl (Sum.inl ⟨oldX, cell⟩)) owner.1 owner.2 =
        ⟨Sum.inr
          (⟨(newQ, Sum.inl (Sum.inl ⟨oldX, cell⟩)), incidence⟩ :
            QZEdge (rxReplacementPresentation P S)), member⟩} := by
  let qMember := rxLocalCellZRadial_qBoundaryMember
    P S oldX cell newQ incidence member
  have cases := rxLocalCellBoundaryQ_cases
    P S oldX cell newQ qMember
  by_cases h000 : newQ = rxLocalCellQAt P S oldX cell (0, 0) 0
  · exact rxLocalCellZRadialFaceOwnerAtQCorner
      P S oldX cell newQ incidence member (0, 0) 0 h000
  · by_cases h001 : newQ = rxLocalCellQAt P S oldX cell (0, 0) 1
    · exact rxLocalCellZRadialFaceOwnerAtQCorner
        P S oldX cell newQ incidence member (0, 0) 1 h001
    · by_cases h010 : newQ = rxLocalCellQAt P S oldX cell (0, 1) 0
      · exact rxLocalCellZRadialFaceOwnerAtQCorner
          P S oldX cell newQ incidence member (0, 1) 0 h010
      · by_cases h011 : newQ = rxLocalCellQAt P S oldX cell (0, 1) 1
        · exact rxLocalCellZRadialFaceOwnerAtQCorner
            P S oldX cell newQ incidence member (0, 1) 1 h011
        · by_cases h100 : newQ = rxLocalCellQAt P S oldX cell (1, 0) 0
          · exact rxLocalCellZRadialFaceOwnerAtQCorner
              P S oldX cell newQ incidence member (1, 0) 0 h100
          · by_cases h101 : newQ = rxLocalCellQAt P S oldX cell (1, 0) 1
            · exact rxLocalCellZRadialFaceOwnerAtQCorner
                P S oldX cell newQ incidence member (1, 0) 1 h101
            · by_cases h110 : newQ = rxLocalCellQAt P S oldX cell (1, 1) 0
              · exact rxLocalCellZRadialFaceOwnerAtQCorner
                  P S oldX cell newQ incidence member (1, 1) 0 h110
              · have remaining001 := cases.resolve_left h000
                have remaining010 := remaining001.resolve_left h001
                have remaining011 := remaining010.resolve_left h010
                have remaining100 := remaining011.resolve_left h011
                have remaining101 := remaining100.resolve_left h100
                have remaining110 := remaining101.resolve_left h101
                have h111 := remaining110.resolve_left h110
                exact rxLocalCellZRadialFaceOwnerAtQCorner
                  P S oldX cell newQ incidence member (1, 1) 1 h111
theorem rxQEdgeZRadial_qBoundaryMember
    (P : TannerSquarePresentation) (S : OddScale)
    (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S) (newQ : RX1 P S)
    (incidence : rxQZIncidence P S newQ (Sum.inl (Sum.inr qEdge)) = true)
    (member : zStarEdgeMember (rxReplacementPresentation P S)
      (Sum.inl (Sum.inr qEdge))
      (Sum.inr
        (⟨(newQ, Sum.inl (Sum.inr qEdge)), incidence⟩ :
          QZEdge (rxReplacementPresentation P S))) = true) :
    zStarBoundaryVertexMember (rxReplacementPresentation P S)
      (Sum.inl (Sum.inr qEdge)) (Vertex.q newQ) = true := by
  classical
  simp only [zStarEdgeMember, decide_eq_true_eq] at member
  obtain ⟨face, hz, huse⟩ := member
  change decide
        ((⟨(newQ, Sum.inl (Sum.inr qEdge)), incidence⟩ :
              QZEdge (rxReplacementPresentation P S)) =
            faceQZEdge (rxReplacementPresentation P S) face 0 ∨
          (⟨(newQ, Sum.inl (Sum.inr qEdge)), incidence⟩ :
              QZEdge (rxReplacementPresentation P S)) =
            faceQZEdge (rxReplacementPresentation P S) face 1) = true at huse
  rw [decide_eq_true_eq] at huse
  simp only [zStarBoundaryVertexMember, decide_eq_true_eq]
  change (exists face : RXFace P S,
    zStarFaceMember (rxReplacementPresentation P S)
        (Sum.inl (Sum.inr qEdge)) face = true ∧
      (newQ = rxFaceQ P S face 0 ∨ newQ = rxFaceQ P S face 1))
  refine ⟨face, hz, ?_⟩
  rcases huse with hzero | hone
  · exact Or.inl (congrArg
      (fun selected : QZEdge (rxReplacementPresentation P S) =>
        selected.1.1) hzero)
  · exact Or.inr (congrArg
      (fun selected : QZEdge (rxReplacementPresentation P S) =>
        selected.1.1) hone)
theorem rxZRadialEdge_ownerZ
    (P : TannerSquarePresentation) (S : OddScale)
    (z : RX2 P S) (edge : QZEdge (rxReplacementPresentation P S))
    (member : zStarEdgeMember (rxReplacementPresentation P S) z
      (Sum.inr edge) = true) :
    edge.1.2 = z := by
  classical
  simp only [zStarEdgeMember, decide_eq_true_eq] at member
  obtain ⟨face, hz, huse⟩ := member
  change decide (edge = faceQZEdge (rxReplacementPresentation P S) face 0 ∨
    edge = faceQZEdge (rxReplacementPresentation P S) face 1) = true at huse
  rw [decide_eq_true_eq] at huse
  have hfaceZ : rxFaceZ P S face = z := by
    simp only [zStarFaceMember, decide_eq_true_eq] at hz
    rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl] at hz
    exact hz
  rcases huse with hzero | hone
  · exact (congrArg
      (fun selected : QZEdge (rxReplacementPresentation P S) =>
        selected.1.2) hzero).trans hfaceZ
  · exact (congrArg
      (fun selected : QZEdge (rxReplacementPresentation P S) =>
        selected.1.2) hone).trans hfaceZ
noncomputable def rxQEdgeZRadialFaceOwnerLocalEdge
    (P : TannerSquarePresentation) (S : OddScale)
    (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S)
    (localEdge : Σ x : P.X, DoubleCylinderEdge P x S)
    (incidence : rxQZIncidence P S (Sum.inl localEdge)
      (Sum.inl (Sum.inr qEdge)) = true)
    (member : zStarEdgeMember (rxReplacementPresentation P S)
      (Sum.inl (Sum.inr qEdge))
      (Sum.inr
        (⟨(Sum.inl localEdge, Sum.inl (Sum.inr qEdge)), incidence⟩ :
          QZEdge (rxReplacementPresentation P S))) = true) :
    {owner : ZStarFace (rxReplacementPresentation P S)
        (Sum.inl (Sum.inr qEdge)) × Two //
      zStarFaceQZEdge (rxReplacementPresentation P S)
          (Sum.inl (Sum.inr qEdge)) owner.1 owner.2 =
        ⟨Sum.inr
          (⟨(Sum.inl localEdge, Sum.inl (Sum.inr qEdge)), incidence⟩ :
            QZEdge (rxReplacementPresentation P S)), member⟩} := by
  let qMember := rxQEdgeZRadial_qBoundaryMember
    P S qEdge (Sum.inl localEdge) incidence member
  let hxq := rxQEdgeBoundaryLocalQ_incidence
    P S qEdge localEdge qMember
  let face := rxQEdgeGlueZStarFace P S qEdge localEdge.1 hxq 0
  have hfaceQ : rxFaceQ P S face.1 0 = Sum.inl localEdge := by
    apply congrArg Sum.inl
    apply Sigma.ext
    · rfl
    · simp only [heq_eq_eq]
      exact (rxQEdgeBoundaryLocalQ_edge
        P S qEdge localEdge qMember).symm
  have hfaceZ : rxFaceZ P S face.1 =
      Sum.inl (Sum.inr qEdge) := rfl
  refine ⟨(face, 0), ?_⟩
  apply Subtype.ext
  apply congrArg Sum.inr
  apply Subtype.ext
  exact Prod.ext hfaceQ hfaceZ
noncomputable def rxQEdgeZRadialFaceOwnerQVertexAtEndpoint
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S)
    (qVertex : Σ q : P.Q, QDoubleCylinderVertex P q S)
    (incidence : rxQZIncidence P S (Sum.inr qVertex)
      (Sum.inl (Sum.inr qEdge)) = true)
    (member : zStarEdgeMember (rxReplacementPresentation P S)
      (Sum.inl (Sum.inr qEdge))
      (Sum.inr
        (⟨(Sum.inr qVertex, Sum.inl (Sum.inr qEdge)), incidence⟩ :
          QZEdge (rxReplacementPresentation P S))) = true)
    (endpoint : Two)
    (hendpoint : qVertex = ⟨qEdge.1, edgeEndpoint
      (qDoubleCylinderEdgeStart P qEdge.1 S)
      (qDoubleCylinderEdgeEnd P qEdge.1 S) qEdge.2 endpoint⟩) :
    {owner : ZStarFace (rxReplacementPresentation P S)
        (Sum.inl (Sum.inr qEdge)) × Two //
      zStarFaceQZEdge (rxReplacementPresentation P S)
          (Sum.inl (Sum.inr qEdge)) owner.1 owner.2 =
        ⟨Sum.inr
          (⟨(Sum.inr qVertex, Sum.inl (Sum.inr qEdge)), incidence⟩ :
            QZEdge (rxReplacementPresentation P S)), member⟩} := by
  let face := rxQEdgeGlueZStarFace P S qEdge
    (A.xqRoot qEdge.1).1 (A.xqRoot qEdge.1).2 endpoint
  have hfaceQ : rxFaceQ P S face.1 1 = Sum.inr qVertex := by
    apply congrArg Sum.inr
    simpa [face, rxFaceQ, glueFaceQ1] using hendpoint.symm
  have hfaceZ : rxFaceZ P S face.1 =
      Sum.inl (Sum.inr qEdge) := rfl
  refine ⟨(face, 1), ?_⟩
  apply Subtype.ext
  apply congrArg Sum.inr
  apply Subtype.ext
  exact Prod.ext hfaceQ hfaceZ
noncomputable def rxQEdgeZRadialFaceOwnerQVertex
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S)
    (qVertex : Σ q : P.Q, QDoubleCylinderVertex P q S)
    (incidence : rxQZIncidence P S (Sum.inr qVertex)
      (Sum.inl (Sum.inr qEdge)) = true)
    (member : zStarEdgeMember (rxReplacementPresentation P S)
      (Sum.inl (Sum.inr qEdge))
      (Sum.inr
        (⟨(Sum.inr qVertex, Sum.inl (Sum.inr qEdge)), incidence⟩ :
          QZEdge (rxReplacementPresentation P S))) = true) :
    {owner : ZStarFace (rxReplacementPresentation P S)
        (Sum.inl (Sum.inr qEdge)) × Two //
      zStarFaceQZEdge (rxReplacementPresentation P S)
          (Sum.inl (Sum.inr qEdge)) owner.1 owner.2 =
        ⟨Sum.inr
          (⟨(Sum.inr qVertex, Sum.inl (Sum.inr qEdge)), incidence⟩ :
            QZEdge (rxReplacementPresentation P S)), member⟩} := by
  let qMember := rxQEdgeZRadial_qBoundaryMember
    P S qEdge (Sum.inr qVertex) incidence member
  by_cases hstart : qVertex = ⟨qEdge.1,
      qDoubleCylinderEdgeStart P qEdge.1 S qEdge.2⟩
  · exact rxQEdgeZRadialFaceOwnerQVertexAtEndpoint
      P A S qEdge qVertex incidence member 0
      (by simpa [edgeEndpoint] using hstart)
  · have hend := (rxQEdgeBoundaryQVertex_endpoints
      P S qEdge qVertex qMember).resolve_left hstart
    exact rxQEdgeZRadialFaceOwnerQVertexAtEndpoint
      P A S qEdge qVertex incidence member 1
      (by simpa [edgeEndpoint] using hend)
noncomputable def rxReplacementZRadialFaceOwnerNonOldZ
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale)
    (z : (Σ x : P.X, DoubleCylinderFace P x S) ⊕
      (Σ q : P.Q, QDoubleCylinderEdge P q S))
    (edge : QZEdge (rxReplacementPresentation P S))
    (member : zStarEdgeMember (rxReplacementPresentation P S)
      (Sum.inl z) (Sum.inr edge) = true) :
    {owner : ZStarFace (rxReplacementPresentation P S) (Sum.inl z) × Two //
      zStarFaceQZEdge (rxReplacementPresentation P S) (Sum.inl z)
          owner.1 owner.2 = ⟨Sum.inr edge, member⟩} := by
  rcases edge with ⟨⟨newQ, edgeZ⟩, incidence⟩
  have howner : edgeZ = Sum.inl z :=
    rxZRadialEdge_ownerZ P S (Sum.inl z)
      ⟨(newQ, edgeZ), incidence⟩ member
  subst edgeZ
  rcases z with localCell | qEdge
  · rcases localCell with ⟨oldX, cell⟩
    exact rxLocalCellZRadialFaceOwner
      P S oldX cell newQ incidence member
  · rcases newQ with localEdge | qVertex
    · exact rxQEdgeZRadialFaceOwnerLocalEdge
        P S qEdge localEdge incidence member
    · exact rxQEdgeZRadialFaceOwnerQVertex
        P A S qEdge qVertex incidence member
theorem rxOldZRadial_qBoundaryMember
    (P : TannerSquarePresentation) (S : OddScale)
    (oldZ : P.Z) (copy : Two) (newQ : RX1 P S)
    (incidence : rxQZIncidence P S newQ (Sum.inr (oldZ, copy)) = true)
    (member : zStarEdgeMember (rxReplacementPresentation P S)
      (Sum.inr (oldZ, copy))
      (Sum.inr
        (⟨(newQ, Sum.inr (oldZ, copy)), incidence⟩ :
          QZEdge (rxReplacementPresentation P S))) = true) :
    zStarBoundaryVertexMember (rxReplacementPresentation P S)
      (Sum.inr (oldZ, copy)) (Vertex.q newQ) = true := by
  classical
  simp only [zStarEdgeMember, decide_eq_true_eq] at member
  obtain ⟨face, hz, huse⟩ := member
  change decide
        ((⟨(newQ, Sum.inr (oldZ, copy)), incidence⟩ :
              QZEdge (rxReplacementPresentation P S)) =
            faceQZEdge (rxReplacementPresentation P S) face 0 ∨
          (⟨(newQ, Sum.inr (oldZ, copy)), incidence⟩ :
              QZEdge (rxReplacementPresentation P S)) =
            faceQZEdge (rxReplacementPresentation P S) face 1) = true at huse
  rw [decide_eq_true_eq] at huse
  simp only [zStarBoundaryVertexMember, decide_eq_true_eq]
  change (exists face : RXFace P S,
    zStarFaceMember (rxReplacementPresentation P S)
        (Sum.inr (oldZ, copy)) face = true ∧
      (newQ = rxFaceQ P S face 0 ∨ newQ = rxFaceQ P S face 1))
  refine ⟨face, hz, ?_⟩
  rcases huse with hzero | hone
  · exact Or.inl (congrArg
      (fun selected : QZEdge (rxReplacementPresentation P S) =>
        selected.1.1) hzero)
  · exact Or.inr (congrArg
      (fun selected : QZEdge (rxReplacementPresentation P S) =>
        selected.1.1) hone)
theorem rxOldZBoundaryQ_terminal
    (P : TannerSquarePresentation) (S : OddScale)
    (oldZ : P.Z) (copy : Two) (newQ : RX1 P S)
    (member : zStarBoundaryVertexMember (rxReplacementPresentation P S)
      (Sum.inr (oldZ, copy)) (Vertex.q newQ) = true) :
    match newQ with
    | Sum.inr ⟨_, (_, Sum.inl (Sum.inr _))⟩ => True
    | _ => False := by
  classical
  simp only [zStarBoundaryVertexMember, decide_eq_true_eq] at member
  change (exists face : RXFace P S,
    zStarFaceMember (rxReplacementPresentation P S)
        (Sum.inr (oldZ, copy)) face = true ∧
      (newQ = rxFaceQ P S face 0 ∨ newQ = rxFaceQ P S face 1))
      at member
  obtain ⟨face, hz, hq⟩ := member
  rcases face with localFace | glue | oldFace
  · simp only [zStarFaceMember, decide_eq_true_eq] at hz
    cases hz
  · simp only [zStarFaceMember, decide_eq_true_eq] at hz
    cases hz
  · rcases newQ with localEdge | qVertex
    · rcases hq with hq | hq <;> cases hq
    · rcases qVertex with ⟨q, newCopy, vertex⟩
      rcases vertex with original | interior
      · rcases original with center | endpoint
        · rcases hq with hq | hq <;> cases hq
        · trivial
      · rcases hq with hq | hq <;> cases hq
theorem rxOldZBoundaryQ_radialMember
    (P : TannerSquarePresentation) (oldZ : P.Z) (q : P.Q)
    (member : zStarBoundaryVertexMember P oldZ (Vertex.q q) = true) :
    zStarEdgeMember P oldZ
      (Sum.inr
        (⟨(q, oldZ), rxOldZBoundaryQZIncidence P q oldZ member⟩ :
          QZEdge P)) = true := by
  change decide (exists face : P.Face,
    zStarFaceMember P oldZ face = true ∧
      (q = P.faceQ face 0 ∨ q = P.faceQ face 1)) = true at member
  change decide (exists face : P.Face,
    zStarFaceMember P oldZ face = true ∧
      decide
        ((⟨(q, oldZ), rxOldZBoundaryQZIncidence P q oldZ member⟩ :
              QZEdge P) = faceQZEdge P face 0 ∨
          (⟨(q, oldZ), rxOldZBoundaryQZIncidence P q oldZ member⟩ :
              QZEdge P) = faceQZEdge P face 1) = true) = true
  rw [decide_eq_true_eq]
  obtain ⟨face, hz, hq | hq⟩ := of_decide_eq_true member
  · refine ⟨face, hz, ?_⟩
    rw [decide_eq_true_eq]
    left
    apply Subtype.ext
    have hz' : P.faceZ face = oldZ := by
      simpa [zStarFaceMember] using hz
    exact Prod.ext hq hz'.symm
  · refine ⟨face, hz, ?_⟩
    rw [decide_eq_true_eq]
    right
    apply Subtype.ext
    have hz' : P.faceZ face = oldZ := by
      simpa [zStarFaceMember] using hz
    exact Prod.ext hq hz'.symm
noncomputable def rxOldZRadialFaceOwnerTerminal
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (oldZ : P.Z) (copy newCopy : Two) (q : P.Q)
    (endpoint : QStarEdge P q)
    (incidence : rxQZIncidence P S
      (Sum.inr ⟨q, (newCopy, Sum.inl (Sum.inr endpoint))⟩)
      (Sum.inr (oldZ, copy)) = true)
    (member : zStarEdgeMember (rxReplacementPresentation P S)
      (Sum.inr (oldZ, copy))
      (Sum.inr
        (⟨(Sum.inr ⟨q, (newCopy, Sum.inl (Sum.inr endpoint))⟩,
            Sum.inr (oldZ, copy)), incidence⟩ :
          QZEdge (rxReplacementPresentation P S))) = true) :
    {owner : ZStarFace (rxReplacementPresentation P S)
        (Sum.inr (oldZ, copy)) × Two //
      zStarFaceQZEdge (rxReplacementPresentation P S)
          (Sum.inr (oldZ, copy)) owner.1 owner.2 =
        ⟨Sum.inr
          (⟨(Sum.inr ⟨q, (newCopy, Sum.inl (Sum.inr endpoint))⟩,
              Sum.inr (oldZ, copy)), incidence⟩ :
            QZEdge (rxReplacementPresentation P S)), member⟩} := by
  let newQ : RX1 P S :=
    Sum.inr ⟨q, (newCopy, Sum.inl (Sum.inr endpoint))⟩
  let qMember := rxOldZRadial_qBoundaryMember
    P S oldZ copy newQ incidence member
  let successorVertex : ZStarBoundaryVertex
      (rxReplacementPresentation P S) (Sum.inr (oldZ, copy)) :=
    ⟨Vertex.q newQ, qMember⟩
  let oldVertex := rxOldZBoundaryVertexProject
    P S oldZ copy successorVertex
  have oldQMember : zStarBoundaryVertexMember P oldZ
      (Vertex.q q) = true := by
    exact oldVertex.2
  have mappedVertex := rxOldZBoundaryVertexMap_project
    P S oldZ copy successorVertex
  have hmappedQ : rxOldZCopyQCoordinate
      P S oldZ copy q oldQMember = newQ := by
    have hvalue := congrArg Subtype.val mappedVertex
    exact Vertex.q.inj hvalue
  let oldIncidence := rxOldZBoundaryQZIncidence P q oldZ oldQMember
  let oldEdge : QZEdge P := ⟨(q, oldZ), oldIncidence⟩
  let oldMember := rxOldZBoundaryQ_radialMember
    P oldZ q oldQMember
  let selected := A3.zRadialFaceOwner oldZ oldEdge oldMember
  have hselected := congrArg Subtype.val selected.2
  have hedge : faceQZEdge P selected.1.1.1 selected.1.2 = oldEdge :=
    Sum.inr.inj hselected
  have hfaceQ : P.faceQ selected.1.1.1 selected.1.2 = q :=
    (congrArg (fun chosen : QZEdge P => chosen.1.1) hedge).trans rfl
  have hfaceZ : P.faceZ selected.1.1.1 = oldZ := by
    simpa [zStarFaceMember] using selected.1.1.2
  let face : ZStarFace (rxReplacementPresentation P S)
      (Sum.inr (oldZ, copy)) :=
    ⟨Sum.inr (Sum.inr (selected.1.1.1, copy)), by
      simp only [zStarFaceMember, decide_eq_true_eq]
      change rxFaceZ P S
        (Sum.inr (Sum.inr (selected.1.1.1, copy))) =
          Sum.inr (oldZ, copy)
      simp [rxFaceZ, oldZFaceZ, hfaceZ]⟩
  have hlift := congrArg (fun chosen : QZEdge P =>
      (Sum.inr ⟨chosen.1.1,
        (copy, Sum.inl (Sum.inr
          (⟨chosen.1.2, chosen.2⟩ : QStarEdge P chosen.1.1)))⟩ :
        RX1 P S)) hedge
  have hsuccessorQ : rxFaceQ P S face.1 selected.1.2 = newQ := by
    rw [show rxFaceQ P S face.1 selected.1.2 =
        rxOldZCopyQCoordinate P S oldZ copy q oldQMember by
      simpa [face, rxFaceQ, oldZFaceQ, rxOldZCopyQCoordinate,
        oldEdge, oldIncidence, faceQZEdge] using hlift]
    exact hmappedQ
  have hsuccessorZ : rxFaceZ P S face.1 =
      Sum.inr (oldZ, copy) := by
    simp [face, rxFaceZ, oldZFaceZ, hfaceZ]
  refine ⟨(face, selected.1.2), ?_⟩
  apply Subtype.ext
  apply congrArg Sum.inr
  apply Subtype.ext
  exact Prod.ext hsuccessorQ hsuccessorZ
noncomputable def rxReplacementZRadialFaceOwner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : (rxReplacementPresentation P S).Z)
    (edge : QZEdge (rxReplacementPresentation P S))
    (member : zStarEdgeMember (rxReplacementPresentation P S) z
      (Sum.inr edge) = true) :
    {owner : ZStarFace (rxReplacementPresentation P S) z × Two //
      zStarFaceQZEdge (rxReplacementPresentation P S) z
          owner.1 owner.2 = ⟨Sum.inr edge, member⟩} := by
  let A3 := A4.toTannerSquareAdmissibleV3
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  rcases edge with ⟨⟨newQ, edgeZ⟩, incidence⟩
  have howner : edgeZ = z := rxZRadialEdge_ownerZ
    P S z ⟨(newQ, edgeZ), incidence⟩ member
  subst edgeZ
  rcases z with nonOldZ | oldZCopy
  · exact rxReplacementZRadialFaceOwnerNonOldZ
      P A S nonOldZ ⟨(newQ, Sum.inl nonOldZ), incidence⟩ member
  · rcases oldZCopy with ⟨oldZ, copy⟩
    let qMember := rxOldZRadial_qBoundaryMember
      P S oldZ copy newQ incidence member
    have terminal := rxOldZBoundaryQ_terminal
      P S oldZ copy newQ qMember
    rcases newQ with localEdge | qVertex
    · exact terminal.elim
    · rcases qVertex with ⟨q, newCopy, vertex⟩
      rcases vertex with original | interior
      · rcases original with center | endpoint
        · exact terminal.elim
        · exact rxOldZRadialFaceOwnerTerminal
            P A3 S oldZ copy newCopy q endpoint incidence member
      · exact terminal.elim
theorem rxXBoundaryLocalCell_pair_cases
    (P : TannerSquarePresentation) (S : OddScale)
    (xCoordinate : RX0 P S) (oldX : P.X)
    (cell : DoubleCylinderFace P oldX S) (newQ : RX1 P S)
    (incidence : rxQZIncidence P S newQ
      (Sum.inl (Sum.inl ⟨oldX, cell⟩)) = true)
    (member : xStarEdgeMember (rxReplacementPresentation P S) xCoordinate
      (Sum.inr
        (⟨(newQ, Sum.inl (Sum.inl ⟨oldX, cell⟩)), incidence⟩ :
          QZEdge (rxReplacementPresentation P S))) = true) :
    (xCoordinate = rxLocalCellXAt P S oldX cell (0, 0) ∧
        newQ = rxLocalCellQAt P S oldX cell (0, 0) 0) ∨
      (xCoordinate = rxLocalCellXAt P S oldX cell (0, 0) ∧
        newQ = rxLocalCellQAt P S oldX cell (0, 0) 1) ∨
      (xCoordinate = rxLocalCellXAt P S oldX cell (0, 1) ∧
        newQ = rxLocalCellQAt P S oldX cell (0, 1) 0) ∨
      (xCoordinate = rxLocalCellXAt P S oldX cell (0, 1) ∧
        newQ = rxLocalCellQAt P S oldX cell (0, 1) 1) ∨
      (xCoordinate = rxLocalCellXAt P S oldX cell (1, 0) ∧
        newQ = rxLocalCellQAt P S oldX cell (1, 0) 0) ∨
      (xCoordinate = rxLocalCellXAt P S oldX cell (1, 0) ∧
        newQ = rxLocalCellQAt P S oldX cell (1, 0) 1) ∨
      (xCoordinate = rxLocalCellXAt P S oldX cell (1, 1) ∧
        newQ = rxLocalCellQAt P S oldX cell (1, 1) 0) ∨
      (xCoordinate = rxLocalCellXAt P S oldX cell (1, 1) ∧
        newQ = rxLocalCellQAt P S oldX cell (1, 1) 1) := by
  classical
  let edge : QZEdge (rxReplacementPresentation P S) :=
    ⟨(newQ, Sum.inl (Sum.inl ⟨oldX, cell⟩)), incidence⟩
  simp only [xStarEdgeMember, decide_eq_true_eq] at member
  obtain ⟨face, hface, huse⟩ := member
  change decide (edge = faceQZEdge (rxReplacementPresentation P S) face 0 ∨
    edge = faceQZEdge (rxReplacementPresentation P S) face 1) = true at huse
  rw [decide_eq_true_eq] at huse
  have hfaceX : rxFaceX P S face = xCoordinate := by
    simp only [xStarFaceMember, decide_eq_true_eq] at hface
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hface
    exact hface
  have route : ∀ (corner : Two × Two) (qCorner : Two),
      xCoordinate = rxLocalCellXAt P S oldX cell corner →
      newQ = rxLocalCellQAt P S oldX cell corner qCorner →
      (xCoordinate = rxLocalCellXAt P S oldX cell (0, 0) ∧
          newQ = rxLocalCellQAt P S oldX cell (0, 0) 0) ∨
        (xCoordinate = rxLocalCellXAt P S oldX cell (0, 0) ∧
          newQ = rxLocalCellQAt P S oldX cell (0, 0) 1) ∨
        (xCoordinate = rxLocalCellXAt P S oldX cell (0, 1) ∧
          newQ = rxLocalCellQAt P S oldX cell (0, 1) 0) ∨
        (xCoordinate = rxLocalCellXAt P S oldX cell (0, 1) ∧
          newQ = rxLocalCellQAt P S oldX cell (0, 1) 1) ∨
        (xCoordinate = rxLocalCellXAt P S oldX cell (1, 0) ∧
          newQ = rxLocalCellQAt P S oldX cell (1, 0) 0) ∨
        (xCoordinate = rxLocalCellXAt P S oldX cell (1, 0) ∧
          newQ = rxLocalCellQAt P S oldX cell (1, 0) 1) ∨
        (xCoordinate = rxLocalCellXAt P S oldX cell (1, 1) ∧
          newQ = rxLocalCellQAt P S oldX cell (1, 1) 0) ∨
        (xCoordinate = rxLocalCellXAt P S oldX cell (1, 1) ∧
          newQ = rxLocalCellQAt P S oldX cell (1, 1) 1) := by
    rintro ⟨first, second⟩ qCorner hx hq
    fin_cases first <;> fin_cases second <;> fin_cases qCorner
    · exact Or.inl ⟨hx, hq⟩
    · exact Or.inr (Or.inl ⟨hx, hq⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hx, hq⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hx, hq⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hx, hq⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hx, hq⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl ⟨hx, hq⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr ⟨hx, hq⟩))))))
  have routeFace : ∀ qCorner : Two,
      edge = faceQZEdge (rxReplacementPresentation P S) face qCorner →
      (xCoordinate = rxLocalCellXAt P S oldX cell (0, 0) ∧
          newQ = rxLocalCellQAt P S oldX cell (0, 0) 0) ∨
        (xCoordinate = rxLocalCellXAt P S oldX cell (0, 0) ∧
          newQ = rxLocalCellQAt P S oldX cell (0, 0) 1) ∨
        (xCoordinate = rxLocalCellXAt P S oldX cell (0, 1) ∧
          newQ = rxLocalCellQAt P S oldX cell (0, 1) 0) ∨
        (xCoordinate = rxLocalCellXAt P S oldX cell (0, 1) ∧
          newQ = rxLocalCellQAt P S oldX cell (0, 1) 1) ∨
        (xCoordinate = rxLocalCellXAt P S oldX cell (1, 0) ∧
          newQ = rxLocalCellQAt P S oldX cell (1, 0) 0) ∨
        (xCoordinate = rxLocalCellXAt P S oldX cell (1, 0) ∧
          newQ = rxLocalCellQAt P S oldX cell (1, 0) 1) ∨
        (xCoordinate = rxLocalCellXAt P S oldX cell (1, 1) ∧
          newQ = rxLocalCellQAt P S oldX cell (1, 1) 0) ∨
        (xCoordinate = rxLocalCellXAt P S oldX cell (1, 1) ∧
          newQ = rxLocalCellQAt P S oldX cell (1, 1) 1) := by
    intro qCorner hedge
    have hraw := congrArg Subtype.val hedge
    have hq : newQ = rxFaceQ P S face qCorner :=
      congrArg Prod.fst hraw
    have hz : (Sum.inl (Sum.inl ⟨oldX, cell⟩) : RX2 P S) =
        rxFaceZ P S face := congrArg Prod.snd hraw
    rcases face with localFaceData | glue | old
    · rcases localFaceData with ⟨ownerX, ownerCell, corner⟩
      change (Sum.inl (Sum.inl ⟨oldX, cell⟩) : RX2 P S) =
          Sum.inl (Sum.inl ⟨ownerX, ownerCell⟩) at hz
      have howner : (⟨oldX, cell⟩ :
          Σ x : P.X, DoubleCylinderFace P x S) =
          ⟨ownerX, ownerCell⟩ := Sum.inl.inj (Sum.inl.inj hz)
      cases howner
      have hx' : xCoordinate = rxLocalCellXAt P S oldX cell corner := by
        simpa [rxLocalCellXAt, rxFaceX] using hfaceX.symm
      have hq' : newQ =
          rxLocalCellQAt P S oldX cell corner qCorner := by
        simpa [rxLocalCellQAt, rxFaceQ, localFaceQAt] using hq
      exact route corner qCorner hx' hq'
    · rcases glue with ⟨a, qEdge, endpoint⟩
      simp [rxFaceZ, glueFaceZ] at hz
    · rcases old with ⟨oldFace, copy⟩
      simp [rxFaceZ, oldZFaceZ] at hz
  exact huse.elim (routeFace 0) (routeFace 1)
noncomputable def rxLocalCellXBoundaryFaceOwnerAtCorner
    (P : TannerSquarePresentation) (S : OddScale)
    (xCoordinate : RX0 P S) (oldX : P.X)
    (cell : DoubleCylinderFace P oldX S) (newQ : RX1 P S)
    (incidence : rxQZIncidence P S newQ
      (Sum.inl (Sum.inl ⟨oldX, cell⟩)) = true)
    (member : xStarEdgeMember (rxReplacementPresentation P S) xCoordinate
      (Sum.inr
        (⟨(newQ, Sum.inl (Sum.inl ⟨oldX, cell⟩)), incidence⟩ :
          QZEdge (rxReplacementPresentation P S))) = true)
    (corner : Two × Two) (qCorner : Two)
    (hx : xCoordinate = rxLocalCellXAt P S oldX cell corner)
    (hq : newQ = rxLocalCellQAt P S oldX cell corner qCorner) :
    {owner : XStarFace (rxReplacementPresentation P S) xCoordinate × Two //
      xStarFaceQZEdge (rxReplacementPresentation P S) xCoordinate
          owner.1 owner.2 =
        ⟨Sum.inr
          (⟨(newQ, Sum.inl (Sum.inl ⟨oldX, cell⟩)), incidence⟩ :
            QZEdge (rxReplacementPresentation P S)), member⟩} := by
  let rawFace : RXFace P S := Sum.inl ⟨oldX, cell, corner⟩
  have hfaceX : rxFaceX P S rawFace = xCoordinate := by
    change localFaceX P S ⟨oldX, cell, corner⟩ = xCoordinate
    exact hx.symm
  have hfaceQ : rxFaceQ P S rawFace qCorner = newQ := by
    change localFaceQAt P S ⟨oldX, cell, corner⟩ qCorner = newQ
    exact hq.symm
  have hfaceZ : rxFaceZ P S rawFace =
      Sum.inl (Sum.inl ⟨oldX, cell⟩) := rfl
  let face : XStarFace (rxReplacementPresentation P S) xCoordinate :=
    ⟨rawFace, by
      simp only [xStarFaceMember, decide_eq_true_eq]
      rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
      exact hfaceX⟩
  refine ⟨(face, qCorner), ?_⟩
  apply Subtype.ext
  apply congrArg Sum.inr
  apply Subtype.ext
  exact Prod.ext hfaceQ hfaceZ
noncomputable def rxLocalCellXBoundaryFaceOwner
    (P : TannerSquarePresentation) (S : OddScale)
    (xCoordinate : RX0 P S) (oldX : P.X)
    (cell : DoubleCylinderFace P oldX S) (newQ : RX1 P S)
    (incidence : rxQZIncidence P S newQ
      (Sum.inl (Sum.inl ⟨oldX, cell⟩)) = true)
    (member : xStarEdgeMember (rxReplacementPresentation P S) xCoordinate
      (Sum.inr
        (⟨(newQ, Sum.inl (Sum.inl ⟨oldX, cell⟩)), incidence⟩ :
          QZEdge (rxReplacementPresentation P S))) = true) :
    {owner : XStarFace (rxReplacementPresentation P S) xCoordinate × Two //
      xStarFaceQZEdge (rxReplacementPresentation P S) xCoordinate
          owner.1 owner.2 =
        ⟨Sum.inr
          (⟨(newQ, Sum.inl (Sum.inl ⟨oldX, cell⟩)), incidence⟩ :
            QZEdge (rxReplacementPresentation P S)), member⟩} := by
  classical
  have cases := rxXBoundaryLocalCell_pair_cases
    P S xCoordinate oldX cell newQ incidence member
  by_cases h000 : xCoordinate = rxLocalCellXAt P S oldX cell (0, 0) ∧
      newQ = rxLocalCellQAt P S oldX cell (0, 0) 0
  · exact rxLocalCellXBoundaryFaceOwnerAtCorner
      P S xCoordinate oldX cell newQ incidence member (0, 0) 0 h000.1 h000.2
  · by_cases h001 : xCoordinate = rxLocalCellXAt P S oldX cell (0, 0) ∧
        newQ = rxLocalCellQAt P S oldX cell (0, 0) 1
    · exact rxLocalCellXBoundaryFaceOwnerAtCorner
        P S xCoordinate oldX cell newQ incidence member (0, 0) 1 h001.1 h001.2
    · by_cases h010 : xCoordinate = rxLocalCellXAt P S oldX cell (0, 1) ∧
          newQ = rxLocalCellQAt P S oldX cell (0, 1) 0
      · exact rxLocalCellXBoundaryFaceOwnerAtCorner
          P S xCoordinate oldX cell newQ incidence member (0, 1) 0 h010.1 h010.2
      · by_cases h011 :
            xCoordinate = rxLocalCellXAt P S oldX cell (0, 1) ∧
              newQ = rxLocalCellQAt P S oldX cell (0, 1) 1
        · exact rxLocalCellXBoundaryFaceOwnerAtCorner
            P S xCoordinate oldX cell newQ incidence member
              (0, 1) 1 h011.1 h011.2
        · by_cases h100 :
              xCoordinate = rxLocalCellXAt P S oldX cell (1, 0) ∧
                newQ = rxLocalCellQAt P S oldX cell (1, 0) 0
          · exact rxLocalCellXBoundaryFaceOwnerAtCorner
              P S xCoordinate oldX cell newQ incidence member
                (1, 0) 0 h100.1 h100.2
          · by_cases h101 :
                xCoordinate = rxLocalCellXAt P S oldX cell (1, 0) ∧
                  newQ = rxLocalCellQAt P S oldX cell (1, 0) 1
            · exact rxLocalCellXBoundaryFaceOwnerAtCorner
                P S xCoordinate oldX cell newQ incidence member
                  (1, 0) 1 h101.1 h101.2
            · by_cases h110 :
                  xCoordinate = rxLocalCellXAt P S oldX cell (1, 1) ∧
                    newQ = rxLocalCellQAt P S oldX cell (1, 1) 0
              · exact rxLocalCellXBoundaryFaceOwnerAtCorner
                  P S xCoordinate oldX cell newQ incidence member
                    (1, 1) 0 h110.1 h110.2
              · have remaining001 := cases.resolve_left h000
                have remaining010 := remaining001.resolve_left h001
                have remaining011 := remaining010.resolve_left h010
                have remaining100 := remaining011.resolve_left h011
                have remaining101 := remaining100.resolve_left h100
                have remaining110 := remaining101.resolve_left h101
                have h111 := remaining110.resolve_left h110
                exact rxLocalCellXBoundaryFaceOwnerAtCorner
                  P S xCoordinate oldX cell newQ incidence member
                    (1, 1) 1 h111.1 h111.2
theorem rxXBoundaryQZ_to_zBoundaryX
    (P : TannerSquarePresentation) (S : OddScale)
    (xCoordinate : RX0 P S) (newQ : RX1 P S) (newZ : RX2 P S)
    (incidence : rxQZIncidence P S newQ newZ = true)
    (member : xStarEdgeMember (rxReplacementPresentation P S) xCoordinate
      (Sum.inr
        (⟨(newQ, newZ), incidence⟩ :
          QZEdge (rxReplacementPresentation P S))) = true) :
    zStarBoundaryVertexMember (rxReplacementPresentation P S) newZ
      (Vertex.x xCoordinate) = true := by
  classical
  simp only [xStarEdgeMember, decide_eq_true_eq] at member
  obtain ⟨face, hx, huse⟩ := member
  change decide
        ((⟨(newQ, newZ), incidence⟩ :
              QZEdge (rxReplacementPresentation P S)) =
            faceQZEdge (rxReplacementPresentation P S) face 0 ∨
          (⟨(newQ, newZ), incidence⟩ :
              QZEdge (rxReplacementPresentation P S)) =
            faceQZEdge (rxReplacementPresentation P S) face 1) = true at huse
  rw [decide_eq_true_eq] at huse
  simp only [zStarBoundaryVertexMember]
  rw [decide_eq_true_eq]
  refine ⟨face, ?_, ?_⟩
  · simp only [zStarFaceMember, decide_eq_true_eq]
    rcases huse with hzero | hone
    · exact (congrArg
        (fun selected : QZEdge (rxReplacementPresentation P S) =>
          selected.1.2) hzero).symm
    · exact (congrArg
        (fun selected : QZEdge (rxReplacementPresentation P S) =>
          selected.1.2) hone).symm
  · have hfaceX : rxFaceX P S face = xCoordinate := by
      simp only [xStarFaceMember, decide_eq_true_eq] at hx
      rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
      exact hx
    exact hfaceX.symm
theorem rxXBoundaryQZ_to_zBoundaryQ
    (P : TannerSquarePresentation) (S : OddScale)
    (xCoordinate : RX0 P S) (newQ : RX1 P S) (newZ : RX2 P S)
    (incidence : rxQZIncidence P S newQ newZ = true)
    (member : xStarEdgeMember (rxReplacementPresentation P S) xCoordinate
      (Sum.inr
        (⟨(newQ, newZ), incidence⟩ :
          QZEdge (rxReplacementPresentation P S))) = true) :
    zStarBoundaryVertexMember (rxReplacementPresentation P S) newZ
      (Vertex.q newQ) = true := by
  classical
  simp only [xStarEdgeMember, decide_eq_true_eq] at member
  obtain ⟨face, _hx, huse⟩ := member
  change decide
        ((⟨(newQ, newZ), incidence⟩ :
              QZEdge (rxReplacementPresentation P S)) =
            faceQZEdge (rxReplacementPresentation P S) face 0 ∨
          (⟨(newQ, newZ), incidence⟩ :
              QZEdge (rxReplacementPresentation P S)) =
            faceQZEdge (rxReplacementPresentation P S) face 1) = true at huse
  rw [decide_eq_true_eq] at huse
  simp only [zStarBoundaryVertexMember]
  rw [decide_eq_true_eq]
  rcases huse with hzero | hone
  · refine ⟨face, ?_, Or.inl ?_⟩
    · simp only [zStarFaceMember, decide_eq_true_eq]
      exact (congrArg
        (fun selected : QZEdge (rxReplacementPresentation P S) =>
          selected.1.2) hzero).symm
    · exact congrArg
        (fun selected : QZEdge (rxReplacementPresentation P S) =>
          selected.1.1) hzero
  · refine ⟨face, ?_, Or.inr ?_⟩
    · simp only [zStarFaceMember, decide_eq_true_eq]
      exact (congrArg
        (fun selected : QZEdge (rxReplacementPresentation P S) =>
          selected.1.2) hone).symm
    · exact congrArg
        (fun selected : QZEdge (rxReplacementPresentation P S) =>
          selected.1.1) hone
theorem rxXBoundaryQZ_xqIncidence
    (P : TannerSquarePresentation) (S : OddScale)
    (xCoordinate : RX0 P S) (newQ : RX1 P S) (newZ : RX2 P S)
    (incidence : rxQZIncidence P S newQ newZ = true)
    (member : xStarEdgeMember (rxReplacementPresentation P S) xCoordinate
      (Sum.inr
        (⟨(newQ, newZ), incidence⟩ :
          QZEdge (rxReplacementPresentation P S))) = true) :
    rxXQIncidence P S xCoordinate newQ = true := by
  classical
  simp only [xStarEdgeMember, decide_eq_true_eq] at member
  obtain ⟨face, hx, huse⟩ := member
  change decide
        ((⟨(newQ, newZ), incidence⟩ :
              QZEdge (rxReplacementPresentation P S)) =
            faceQZEdge (rxReplacementPresentation P S) face 0 ∨
          (⟨(newQ, newZ), incidence⟩ :
              QZEdge (rxReplacementPresentation P S)) =
            faceQZEdge (rxReplacementPresentation P S) face 1) = true at huse
  rw [decide_eq_true_eq] at huse
  have hfaceX : rxFaceX P S face = xCoordinate := by
    simp only [xStarFaceMember, decide_eq_true_eq] at hx
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
    exact hx
  rcases huse with hzero | hone
  · have hfaceQ : newQ = rxFaceQ P S face 0 := congrArg
      (fun selected : QZEdge (rxReplacementPresentation P S) =>
        selected.1.1) hzero
    exact (rxXQIncidence_eq_true_iff P S xCoordinate newQ).2
      ⟨face, 0, hfaceX, hfaceQ.symm⟩
  · have hfaceQ : newQ = rxFaceQ P S face 1 := congrArg
      (fun selected : QZEdge (rxReplacementPresentation P S) =>
        selected.1.1) hone
    exact (rxXQIncidence_eq_true_iff P S xCoordinate newQ).2
      ⟨face, 1, hfaceX, hfaceQ.symm⟩
theorem rxXBoundaryQEdgeGlue_localOwner
    (P : TannerSquarePresentation) (S : OddScale)
    (xCoordinate : RX0 P S) (oldX : P.X)
    (localEdge : DoubleCylinderEdge P oldX S)
    (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S)
    (incidence : rxQZIncidence P S (Sum.inl ⟨oldX, localEdge⟩)
      (Sum.inl (Sum.inr qEdge)) = true)
    (member : xStarEdgeMember (rxReplacementPresentation P S) xCoordinate
      (Sum.inr
        (⟨(Sum.inl ⟨oldX, localEdge⟩, Sum.inl (Sum.inr qEdge)), incidence⟩ :
          QZEdge (rxReplacementPresentation P S))) = true) :
    oldX = xCoordinate.1 := by
  classical
  simp only [xStarEdgeMember, decide_eq_true_eq] at member
  obtain ⟨face, hx, huse⟩ := member
  change decide
        ((⟨(Sum.inl ⟨oldX, localEdge⟩, Sum.inl (Sum.inr qEdge)), incidence⟩ :
              QZEdge (rxReplacementPresentation P S)) =
            faceQZEdge (rxReplacementPresentation P S) face 0 ∨
          (⟨(Sum.inl ⟨oldX, localEdge⟩, Sum.inl (Sum.inr qEdge)), incidence⟩ :
              QZEdge (rxReplacementPresentation P S)) =
            faceQZEdge (rxReplacementPresentation P S) face 1) = true at huse
  rw [decide_eq_true_eq] at huse
  have hfaceX : rxFaceX P S face = xCoordinate := by
    simp only [xStarFaceMember, decide_eq_true_eq] at hx
    rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
    exact hx
  have route : ∀ corner : Two,
      (⟨(Sum.inl ⟨oldX, localEdge⟩, Sum.inl (Sum.inr qEdge)), incidence⟩ :
          QZEdge (rxReplacementPresentation P S)) =
        faceQZEdge (rxReplacementPresentation P S) face corner →
      oldX = xCoordinate.1 := by
    intro corner hedge
    have hraw := congrArg Subtype.val hedge
    have hq := congrArg Prod.fst hraw
    have hz := congrArg Prod.snd hraw
    rcases face with localFace | glue | oldFace
    · change Sum.inl (Sum.inr qEdge) = localFaceZ P S localFace at hz
      simp [localFaceZ] at hz
    · rcases glue with ⟨a, edge, endpoint⟩
      fin_cases corner
      · have hlocal := Sum.inl.inj hq
        exact (congrArg Sigma.fst hlocal).trans
          (congrArg Sigma.fst hfaceX)
      · change Sum.inl ⟨oldX, localEdge⟩ =
          glueFaceQ1 P S ⟨a, edge, endpoint⟩ at hq
        simp [glueFaceQ1] at hq
    · change Sum.inl (Sum.inr qEdge) = oldZFaceZ P S oldFace at hz
      simp [oldZFaceZ] at hz
  exact huse.elim (route 0) (route 1)
noncomputable def rxQEdgeXBoundaryFaceOwnerLocalEdgeAtEndpoint
    (P : TannerSquarePresentation) (S : OddScale)
    (xCoordinate : RX0 P S)
    (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S)
    (localEdge : DoubleCylinderEdge P xCoordinate.1 S)
    (incidence : rxQZIncidence P S
      (Sum.inl ⟨xCoordinate.1, localEdge⟩)
      (Sum.inl (Sum.inr qEdge)) = true)
    (member : xStarEdgeMember (rxReplacementPresentation P S) xCoordinate
      (Sum.inr
        (⟨(Sum.inl ⟨xCoordinate.1, localEdge⟩,
            Sum.inl (Sum.inr qEdge)), incidence⟩ :
          QZEdge (rxReplacementPresentation P S))) = true)
    (hxq : P.xq xCoordinate.1 qEdge.1 = true) (endpoint : Two)
    (hfaceX : glueFaceX P S
      ⟨(⟨(xCoordinate.1, qEdge.1), hxq⟩ : XQEdge P),
        qEdge.2, endpoint⟩ = xCoordinate)
    (hedge : localEdge = qToXDoubleCylinderEdgeRaw
      P qEdge.1 xCoordinate.1 hxq S qEdge.2) :
    {owner : XStarFace (rxReplacementPresentation P S) xCoordinate × Two //
      xStarFaceQZEdge (rxReplacementPresentation P S) xCoordinate
          owner.1 owner.2 =
        ⟨Sum.inr
          (⟨(Sum.inl ⟨xCoordinate.1, localEdge⟩,
              Sum.inl (Sum.inr qEdge)), incidence⟩ :
            QZEdge (rxReplacementPresentation P S)), member⟩} := by
  let glue : RXXQGlueFace P S :=
    ⟨(⟨(xCoordinate.1, qEdge.1), hxq⟩ : XQEdge P), qEdge.2, endpoint⟩
  let rawFace : RXFace P S := Sum.inr (Sum.inl glue)
  have hfaceQ : rxFaceQ P S rawFace 0 =
      Sum.inl ⟨xCoordinate.1, localEdge⟩ := by
    apply congrArg Sum.inl
    exact Sigma.ext rfl (by simpa only [heq_eq_eq] using hedge.symm)
  have hfaceZ : rxFaceZ P S rawFace =
      Sum.inl (Sum.inr qEdge) := rfl
  let face : XStarFace (rxReplacementPresentation P S) xCoordinate :=
    ⟨rawFace, by
      simp only [xStarFaceMember, decide_eq_true_eq]
      rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
      exact hfaceX⟩
  refine ⟨(face, 0), ?_⟩
  apply Subtype.ext
  apply congrArg Sum.inr
  apply Subtype.ext
  exact Prod.ext hfaceQ hfaceZ
noncomputable def rxQEdgeXBoundaryFaceOwnerLocalEdge
    (P : TannerSquarePresentation) (S : OddScale)
    (xCoordinate : RX0 P S)
    (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S)
    (localEdge : Σ x : P.X, DoubleCylinderEdge P x S)
    (incidence : rxQZIncidence P S (Sum.inl localEdge)
      (Sum.inl (Sum.inr qEdge)) = true)
    (member : xStarEdgeMember (rxReplacementPresentation P S) xCoordinate
      (Sum.inr
        (⟨(Sum.inl localEdge, Sum.inl (Sum.inr qEdge)), incidence⟩ :
          QZEdge (rxReplacementPresentation P S))) = true) :
    {owner : XStarFace (rxReplacementPresentation P S) xCoordinate × Two //
      xStarFaceQZEdge (rxReplacementPresentation P S) xCoordinate
          owner.1 owner.2 =
        ⟨Sum.inr
          (⟨(Sum.inl localEdge, Sum.inl (Sum.inr qEdge)), incidence⟩ :
            QZEdge (rxReplacementPresentation P S)), member⟩} := by
  rcases localEdge with ⟨oldX, localEdge⟩
  have howner := rxXBoundaryQEdgeGlue_localOwner
    P S xCoordinate oldX localEdge qEdge incidence member
  subst oldX
  let xMember := rxXBoundaryQZ_to_zBoundaryX P S xCoordinate
    (Sum.inl ⟨xCoordinate.1, localEdge⟩)
      (Sum.inl (Sum.inr qEdge)) incidence member
  let qMember := rxXBoundaryQZ_to_zBoundaryQ P S xCoordinate
    (Sum.inl ⟨xCoordinate.1, localEdge⟩)
      (Sum.inl (Sum.inr qEdge)) incidence member
  let hxq := rxQEdgeBoundaryX_incidence P S qEdge xCoordinate xMember
  have hedge : localEdge = qToXDoubleCylinderEdgeRaw
      P qEdge.1 xCoordinate.1 hxq S qEdge.2 := by
    simpa using rxQEdgeBoundaryLocalQ_edge P S qEdge
      ⟨xCoordinate.1, localEdge⟩ qMember
  by_cases hzero : xCoordinate = glueFaceX P S
      ⟨(⟨(xCoordinate.1, qEdge.1), hxq⟩ : XQEdge P), qEdge.2, 0⟩
  · exact rxQEdgeXBoundaryFaceOwnerLocalEdgeAtEndpoint
      P S xCoordinate qEdge localEdge
        incidence member hxq 0 hzero.symm hedge
  · have hone := (rxQEdgeBoundaryX_endpoints
      P S qEdge xCoordinate xMember).resolve_left hzero
    exact rxQEdgeXBoundaryFaceOwnerLocalEdgeAtEndpoint
      P S xCoordinate qEdge localEdge
        incidence member hxq 1 hone.symm hedge
noncomputable def rxQEdgeXBoundaryFaceOwnerQVertexAtEndpoint
    (P : TannerSquarePresentation) (S : OddScale)
    (xCoordinate : RX0 P S)
    (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S)
    (endpoint : Two)
    (incidence : rxQZIncidence P S
      (Sum.inr ⟨qEdge.1, edgeEndpoint
        (qDoubleCylinderEdgeStart P qEdge.1 S)
        (qDoubleCylinderEdgeEnd P qEdge.1 S) qEdge.2 endpoint⟩)
      (Sum.inl (Sum.inr qEdge)) = true)
    (member : xStarEdgeMember (rxReplacementPresentation P S) xCoordinate
      (Sum.inr
        (⟨(Sum.inr ⟨qEdge.1, edgeEndpoint
              (qDoubleCylinderEdgeStart P qEdge.1 S)
              (qDoubleCylinderEdgeEnd P qEdge.1 S) qEdge.2 endpoint⟩,
            Sum.inl (Sum.inr qEdge)), incidence⟩ :
          QZEdge (rxReplacementPresentation P S))) = true) :
    {owner : XStarFace (rxReplacementPresentation P S) xCoordinate × Two //
      xStarFaceQZEdge (rxReplacementPresentation P S) xCoordinate
          owner.1 owner.2 =
        ⟨Sum.inr
          (⟨(Sum.inr ⟨qEdge.1, edgeEndpoint
                (qDoubleCylinderEdgeStart P qEdge.1 S)
                (qDoubleCylinderEdgeEnd P qEdge.1 S) qEdge.2 endpoint⟩,
              Sum.inl (Sum.inr qEdge)), incidence⟩ :
            QZEdge (rxReplacementPresentation P S)), member⟩} := by
  let successorXQ := rxXBoundaryQZ_xqIncidence P S xCoordinate
    (Sum.inr ⟨qEdge.1, edgeEndpoint
      (qDoubleCylinderEdgeStart P qEdge.1 S)
      (qDoubleCylinderEdgeEnd P qEdge.1 S) qEdge.2 endpoint⟩)
    (Sum.inl (Sum.inr qEdge)) incidence member
  let hxq := rxQVertexXRadial_oldXQ P S xCoordinate qEdge.1
    (edgeEndpoint (qDoubleCylinderEdgeStart P qEdge.1 S)
      (qDoubleCylinderEdgeEnd P qEdge.1 S) qEdge.2 endpoint) successorXQ
  let glue : RXXQGlueFace P S :=
    ⟨(⟨(xCoordinate.1, qEdge.1), hxq⟩ : XQEdge P), qEdge.2, endpoint⟩
  have hfaceX : glueFaceX P S glue = xCoordinate :=
    rxQVertexGlueFaceX_eq P S xCoordinate qEdge.1
      (edgeEndpoint (qDoubleCylinderEdgeStart P qEdge.1 S)
        (qDoubleCylinderEdgeEnd P qEdge.1 S) qEdge.2 endpoint)
      successorXQ hxq qEdge.2 endpoint rfl
  have hfaceQ : rxFaceQ P S (Sum.inr (Sum.inl glue)) 1 =
      Sum.inr ⟨qEdge.1, edgeEndpoint
        (qDoubleCylinderEdgeStart P qEdge.1 S)
        (qDoubleCylinderEdgeEnd P qEdge.1 S) qEdge.2 endpoint⟩ := rfl
  have hfaceZ : rxFaceZ P S (Sum.inr (Sum.inl glue)) =
      Sum.inl (Sum.inr qEdge) := rfl
  let face : XStarFace (rxReplacementPresentation P S) xCoordinate :=
    ⟨Sum.inr (Sum.inl glue), by
      simp only [xStarFaceMember, decide_eq_true_eq]
      rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
      exact hfaceX⟩
  refine ⟨(face, 1), ?_⟩
  apply Subtype.ext
  apply congrArg Sum.inr
  apply Subtype.ext
  exact Prod.ext hfaceQ hfaceZ
noncomputable def rxQEdgeXBoundaryFaceOwnerQVertex
    (P : TannerSquarePresentation) (S : OddScale)
    (xCoordinate : RX0 P S)
    (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S)
    (qVertex : Σ q : P.Q, QDoubleCylinderVertex P q S)
    (incidence : rxQZIncidence P S (Sum.inr qVertex)
      (Sum.inl (Sum.inr qEdge)) = true)
    (member : xStarEdgeMember (rxReplacementPresentation P S) xCoordinate
      (Sum.inr
        (⟨(Sum.inr qVertex, Sum.inl (Sum.inr qEdge)), incidence⟩ :
          QZEdge (rxReplacementPresentation P S))) = true) :
    {owner : XStarFace (rxReplacementPresentation P S) xCoordinate × Two //
      xStarFaceQZEdge (rxReplacementPresentation P S) xCoordinate
          owner.1 owner.2 =
        ⟨Sum.inr
          (⟨(Sum.inr qVertex, Sum.inl (Sum.inr qEdge)), incidence⟩ :
            QZEdge (rxReplacementPresentation P S)), member⟩} := by
  let qMember := rxXBoundaryQZ_to_zBoundaryQ P S xCoordinate
    (Sum.inr qVertex) (Sum.inl (Sum.inr qEdge)) incidence member
  by_cases hstart : qVertex = ⟨qEdge.1,
      qDoubleCylinderEdgeStart P qEdge.1 S qEdge.2⟩
  · cases hstart
    exact rxQEdgeXBoundaryFaceOwnerQVertexAtEndpoint
      P S xCoordinate qEdge 0 incidence member
  · have hend := (rxQEdgeBoundaryQVertex_endpoints
      P S qEdge qVertex qMember).resolve_left hstart
    cases hend
    exact rxQEdgeXBoundaryFaceOwnerQVertexAtEndpoint
      P S xCoordinate qEdge 1 incidence member
theorem rxOldZXBoundary_oldEdgeMember
    (P : TannerSquarePresentation) (S : OddScale)
    (xCoordinate : RX0 P S) (oldZ : P.Z) (copy newCopy : Two)
    (q : P.Q) (endpoint : QStarEdge P q)
    (incidence : rxQZIncidence P S
      (Sum.inr ⟨q, (newCopy, Sum.inl (Sum.inr endpoint))⟩)
      (Sum.inr (oldZ, copy)) = true)
    (member : xStarEdgeMember (rxReplacementPresentation P S) xCoordinate
      (Sum.inr
        (⟨(Sum.inr ⟨q, (newCopy, Sum.inl (Sum.inr endpoint))⟩,
            Sum.inr (oldZ, copy)), incidence⟩ :
          QZEdge (rxReplacementPresentation P S))) = true)
    (oldQMember : zStarBoundaryVertexMember P oldZ
      (Vertex.q q) = true) :
    xStarEdgeMember P xCoordinate.1
      (Sum.inr
        (⟨(q, oldZ), rxOldZBoundaryQZIncidence P q oldZ oldQMember⟩ :
          QZEdge P)) = true := by
  classical
  let oldEdge : QZEdge P :=
    ⟨(q, oldZ), rxOldZBoundaryQZIncidence P q oldZ oldQMember⟩
  simp only [xStarEdgeMember, decide_eq_true_eq] at member
  obtain ⟨face, hx, huse⟩ := member
  change decide
        ((⟨(Sum.inr ⟨q, (newCopy, Sum.inl (Sum.inr endpoint))⟩,
              Sum.inr (oldZ, copy)), incidence⟩ :
            QZEdge (rxReplacementPresentation P S)) =
            faceQZEdge (rxReplacementPresentation P S) face 0 ∨
          (⟨(Sum.inr ⟨q, (newCopy, Sum.inl (Sum.inr endpoint))⟩,
              Sum.inr (oldZ, copy)), incidence⟩ :
            QZEdge (rxReplacementPresentation P S)) =
            faceQZEdge (rxReplacementPresentation P S) face 1) = true at huse
  rw [decide_eq_true_eq] at huse
  simp only [xStarEdgeMember, decide_eq_true_eq]
  have route : ∀ corner : Two,
      (⟨(Sum.inr ⟨q, (newCopy, Sum.inl (Sum.inr endpoint))⟩,
          Sum.inr (oldZ, copy)), incidence⟩ :
        QZEdge (rxReplacementPresentation P S)) =
          faceQZEdge (rxReplacementPresentation P S) face corner →
      ∃ oldFace : P.Face,
        xStarFaceMember P xCoordinate.1 oldFace = true ∧
          decide (oldEdge = faceQZEdge P oldFace 0 ∨
            oldEdge = faceQZEdge P oldFace 1) = true := by
    intro corner hedge
    have hraw := congrArg Subtype.val hedge
    have hq := congrArg Prod.fst hraw
    have hz := congrArg Prod.snd hraw
    rcases face with localFace | glue | oldFace
    · change Sum.inr (oldZ, copy) = localFaceZ P S localFace at hz
      simp [localFaceZ] at hz
    · change Sum.inr (oldZ, copy) = glueFaceZ P S glue at hz
      simp [glueFaceZ] at hz
    · rcases oldFace with ⟨oldFace, storedCopy⟩
      have hzpair : (P.faceZ oldFace, storedCopy) = (oldZ, copy) := by
        change Sum.inr (oldZ, copy) =
          Sum.inr (P.faceZ oldFace, storedCopy) at hz
        exact (Sum.inr.inj hz).symm
      have hfaceZ : P.faceZ oldFace = oldZ := congrArg Prod.fst hzpair
      have hfaceX : P.faceX oldFace = xCoordinate.1 := by
        have hsuccessorX : rxFaceX P S
            (Sum.inr (Sum.inr (oldFace, storedCopy))) = xCoordinate := by
          simp only [xStarFaceMember, decide_eq_true_eq] at hx
          rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
          exact hx
        exact congrArg Sigma.fst hsuccessorX
      have hfaceQ : P.faceQ oldFace corner = q := by
        have hsuccessorQ :
            Sum.inr ⟨q, (newCopy, Sum.inl (Sum.inr endpoint))⟩ =
              rxFaceQ P S (Sum.inr (Sum.inr (oldFace, storedCopy))) corner := hq
        exact (congrArg Sigma.fst (Sum.inr.inj hsuccessorQ)).symm
      refine ⟨oldFace, ?_, ?_⟩
      · simpa [xStarFaceMember] using hfaceX
      · rw [decide_eq_true_eq]
        apply rxTwoElim (motive := fun corner =>
          P.faceQ oldFace corner = q →
            oldEdge = faceQZEdge P oldFace 0 ∨
              oldEdge = faceQZEdge P oldFace 1)
        · intro hq0
          left
          apply Subtype.ext
          exact Prod.ext hq0.symm hfaceZ.symm
        · intro hq1
          right
          apply Subtype.ext
          exact Prod.ext hq1.symm hfaceZ.symm
        · exact hfaceQ
  obtain ⟨oldFace, hmember, hedge⟩ := huse.elim (route 0) (route 1)
  exact ⟨oldFace, hmember, hedge⟩
theorem rxOldZXBoundary_selectedFaceX
    (P : TannerSquarePresentation) (S : OddScale)
    (xCoordinate : RX0 P S) (oldZ : P.Z) (copy newCopy : Two)
    (q : P.Q) (endpoint : QStarEdge P q)
    (incidence : rxQZIncidence P S
      (Sum.inr ⟨q, (newCopy, Sum.inl (Sum.inr endpoint))⟩)
      (Sum.inr (oldZ, copy)) = true)
    (member : xStarEdgeMember (rxReplacementPresentation P S) xCoordinate
      (Sum.inr
        (⟨(Sum.inr ⟨q, (newCopy, Sum.inl (Sum.inr endpoint))⟩,
            Sum.inr (oldZ, copy)), incidence⟩ :
          QZEdge (rxReplacementPresentation P S))) = true)
    (selectedFace : P.Face)
    (hselectedX : P.faceX selectedFace = xCoordinate.1)
    (hselectedZ : P.faceZ selectedFace = oldZ) :
    oldZFaceX P S (selectedFace, copy) = xCoordinate := by
  classical
  simp only [xStarEdgeMember, decide_eq_true_eq] at member
  obtain ⟨face, hx, huse⟩ := member
  change decide
        ((⟨(Sum.inr ⟨q, (newCopy, Sum.inl (Sum.inr endpoint))⟩,
              Sum.inr (oldZ, copy)), incidence⟩ :
            QZEdge (rxReplacementPresentation P S)) =
            faceQZEdge (rxReplacementPresentation P S) face 0 ∨
          (⟨(Sum.inr ⟨q, (newCopy, Sum.inl (Sum.inr endpoint))⟩,
              Sum.inr (oldZ, copy)), incidence⟩ :
            QZEdge (rxReplacementPresentation P S)) =
            faceQZEdge (rxReplacementPresentation P S) face 1) = true at huse
  rw [decide_eq_true_eq] at huse
  have route : ∀ corner : Two,
      (⟨(Sum.inr ⟨q, (newCopy, Sum.inl (Sum.inr endpoint))⟩,
          Sum.inr (oldZ, copy)), incidence⟩ :
        QZEdge (rxReplacementPresentation P S)) =
          faceQZEdge (rxReplacementPresentation P S) face corner →
      oldZFaceX P S (selectedFace, copy) = xCoordinate := by
    intro corner hedge
    have hraw := congrArg Subtype.val hedge
    have hz := congrArg Prod.snd hraw
    rcases face with localFace | glue | oldFace
    · change Sum.inr (oldZ, copy) = localFaceZ P S localFace at hz
      simp [localFaceZ] at hz
    · change Sum.inr (oldZ, copy) = glueFaceZ P S glue at hz
      simp [glueFaceZ] at hz
    · rcases oldFace with ⟨sourceFace, storedCopy⟩
      have hzpair : (P.faceZ sourceFace, storedCopy) = (oldZ, copy) := by
        change Sum.inr (oldZ, copy) =
          Sum.inr (P.faceZ sourceFace, storedCopy) at hz
        exact (Sum.inr.inj hz).symm
      have hsourceZ : P.faceZ sourceFace = oldZ :=
        congrArg Prod.fst hzpair
      have hcopy : storedCopy = copy := congrArg Prod.snd hzpair
      have hsource : oldZFaceX P S (sourceFace, storedCopy) =
          xCoordinate := by
        have hrawX : rxFaceX P S
            (Sum.inr (Sum.inr (sourceFace, storedCopy))) = xCoordinate := by
          simp only [xStarFaceMember, decide_eq_true_eq] at hx
          rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl] at hx
          exact hx
        exact hrawX
      have hsourceX : P.faceX sourceFace = xCoordinate.1 :=
        congrArg Sigma.fst hsource
      subst storedCopy
      exact (oldZFaceX_congr P S selectedFace sourceFace copy
        (hselectedX.trans hsourceX.symm)
        (hselectedZ.trans hsourceZ.symm)).trans hsource
  exact huse.elim (route 0) (route 1)
noncomputable def rxOldZXBoundaryFaceOwnerTerminal
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (xCoordinate : RX0 P S)
    (oldZ : P.Z) (copy newCopy : Two) (q : P.Q)
    (endpoint : QStarEdge P q)
    (incidence : rxQZIncidence P S
      (Sum.inr ⟨q, (newCopy, Sum.inl (Sum.inr endpoint))⟩)
      (Sum.inr (oldZ, copy)) = true)
    (member : xStarEdgeMember (rxReplacementPresentation P S) xCoordinate
      (Sum.inr
        (⟨(Sum.inr ⟨q, (newCopy, Sum.inl (Sum.inr endpoint))⟩,
            Sum.inr (oldZ, copy)), incidence⟩ :
          QZEdge (rxReplacementPresentation P S))) = true) :
    {owner : XStarFace (rxReplacementPresentation P S) xCoordinate × Two //
      xStarFaceQZEdge (rxReplacementPresentation P S) xCoordinate
          owner.1 owner.2 =
        ⟨Sum.inr
          (⟨(Sum.inr ⟨q, (newCopy, Sum.inl (Sum.inr endpoint))⟩,
              Sum.inr (oldZ, copy)), incidence⟩ :
            QZEdge (rxReplacementPresentation P S)), member⟩} := by
  let newQ : RX1 P S :=
    Sum.inr ⟨q, (newCopy, Sum.inl (Sum.inr endpoint))⟩
  let qMember := rxXBoundaryQZ_to_zBoundaryQ P S xCoordinate newQ
    (Sum.inr (oldZ, copy)) incidence member
  let successorQ : ZStarBoundaryVertex
      (rxReplacementPresentation P S) (Sum.inr (oldZ, copy)) :=
    ⟨Vertex.q newQ, qMember⟩
  let oldQVertex := rxOldZBoundaryVertexProject
    P S oldZ copy successorQ
  have oldQMember : zStarBoundaryVertexMember P oldZ
      (Vertex.q q) = true := oldQVertex.2
  have mappedQ := rxOldZBoundaryVertexMap_project
    P S oldZ copy successorQ
  have hmappedQ : rxOldZCopyQCoordinate
      P S oldZ copy q oldQMember = newQ := by
    exact Vertex.q.inj (congrArg Subtype.val mappedQ)
  let oldIncidence := rxOldZBoundaryQZIncidence P q oldZ oldQMember
  let oldEdge : QZEdge P := ⟨(q, oldZ), oldIncidence⟩
  let oldMember := rxOldZXBoundary_oldEdgeMember
    P S xCoordinate oldZ copy newCopy q endpoint incidence member oldQMember
  let selected := A4.xBoundaryFaceOwner xCoordinate.1 oldEdge oldMember
  have hselected := congrArg Subtype.val selected.2
  have hedge : faceQZEdge P selected.1.1.1 selected.1.2 = oldEdge :=
    Sum.inr.inj hselected
  have hfaceX : P.faceX selected.1.1.1 = xCoordinate.1 := by
    simpa [xStarFaceMember] using selected.1.1.2
  have hfaceQ : P.faceQ selected.1.1.1 selected.1.2 = q :=
    (congrArg (fun chosen : QZEdge P => chosen.1.1) hedge).trans rfl
  have hfaceZ : P.faceZ selected.1.1.1 = oldZ :=
    (congrArg (fun chosen : QZEdge P => chosen.1.2) hedge).trans rfl
  let rawFace : RXFace P S :=
    Sum.inr (Sum.inr (selected.1.1.1, copy))
  have hsuccessorX : rxFaceX P S rawFace = xCoordinate := by
    exact rxOldZXBoundary_selectedFaceX
      P S xCoordinate oldZ copy newCopy q endpoint incidence member
        selected.1.1.1 hfaceX hfaceZ
  have hlift := congrArg (fun chosen : QZEdge P =>
      (Sum.inr ⟨chosen.1.1,
        (copy, Sum.inl (Sum.inr
          (⟨chosen.1.2, chosen.2⟩ : QStarEdge P chosen.1.1)))⟩ :
        RX1 P S)) hedge
  have hsuccessorQ : rxFaceQ P S rawFace selected.1.2 = newQ := by
    rw [show rxFaceQ P S rawFace selected.1.2 =
        rxOldZCopyQCoordinate P S oldZ copy q oldQMember by
      simpa [rawFace, rxFaceQ, oldZFaceQ, rxOldZCopyQCoordinate,
        oldEdge, oldIncidence, faceQZEdge] using hlift]
    exact hmappedQ
  have hsuccessorZ : rxFaceZ P S rawFace =
      Sum.inr (oldZ, copy) := by
    simp [rawFace, rxFaceZ, oldZFaceZ, hfaceZ]
  let face : XStarFace (rxReplacementPresentation P S) xCoordinate :=
    ⟨rawFace, by
      simp only [xStarFaceMember, decide_eq_true_eq]
      rw [show (rxReplacementPresentation P S).faceX = rxFaceX P S from rfl]
      exact hsuccessorX⟩
  refine ⟨(face, selected.1.2), ?_⟩
  apply Subtype.ext
  apply congrArg Sum.inr
  apply Subtype.ext
  exact Prod.ext hsuccessorQ hsuccessorZ
noncomputable def rxReplacementXBoundaryFaceOwner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (xCoordinate : (rxReplacementPresentation P S).X)
    (edge : QZEdge (rxReplacementPresentation P S))
    (member : xStarEdgeMember (rxReplacementPresentation P S) xCoordinate
      (Sum.inr edge) = true) :
    {owner : XStarFace (rxReplacementPresentation P S) xCoordinate × Two //
      xStarFaceQZEdge (rxReplacementPresentation P S) xCoordinate
          owner.1 owner.2 = ⟨Sum.inr edge, member⟩} := by
  rcases edge with ⟨⟨newQ, newZ⟩, incidence⟩
  rcases newZ with nonOldZ | oldZCopy
  · rcases nonOldZ with localCell | qEdge
    · rcases localCell with ⟨oldX, cell⟩
      exact rxLocalCellXBoundaryFaceOwner
        P S xCoordinate oldX cell newQ incidence member
    · rcases newQ with localEdge | qVertex
      · exact rxQEdgeXBoundaryFaceOwnerLocalEdge
          P S xCoordinate qEdge localEdge incidence member
      · exact rxQEdgeXBoundaryFaceOwnerQVertex
          P S xCoordinate qEdge qVertex incidence member
  · rcases oldZCopy with ⟨oldZ, copy⟩
    let qMember := rxXBoundaryQZ_to_zBoundaryQ P S xCoordinate newQ
      (Sum.inr (oldZ, copy)) incidence member
    have terminal := rxOldZBoundaryQ_terminal
      P S oldZ copy newQ qMember
    rcases newQ with localEdge | qVertex
    · exact terminal.elim
    · rcases qVertex with ⟨q, newCopy, vertex⟩
      rcases vertex with original | interior
      · rcases original with center | endpoint
        · exact terminal.elim
        · exact rxOldZXBoundaryFaceOwnerTerminal
            P A4 S xCoordinate oldZ copy newCopy q endpoint incidence member
      · exact terminal.elim
theorem rxZBoundaryLocalCellLocalEdge_pair_cases
    (P : TannerSquarePresentation) (S : OddScale) (oldX : P.X)
    (cell : DoubleCylinderFace P oldX S) (newX : RX0 P S)
    (localEdge : Σ x : P.X, DoubleCylinderEdge P x S)
    (incidence : rxXQIncidence P S newX (Sum.inl localEdge) = true)
    (member : zStarEdgeMember (rxReplacementPresentation P S)
      (Sum.inl (Sum.inl ⟨oldX, cell⟩))
      (Sum.inl
        (⟨(newX, Sum.inl localEdge), incidence⟩ :
          XQEdge (rxReplacementPresentation P S))) = true) :
    (newX = rxLocalCellXAt P S oldX cell (0, 0) ∧
        (Sum.inl localEdge : RX1 P S) =
          rxLocalCellQAt P S oldX cell (0, 0) 0) ∨
      (newX = rxLocalCellXAt P S oldX cell (0, 0) ∧
        (Sum.inl localEdge : RX1 P S) =
          rxLocalCellQAt P S oldX cell (0, 0) 1) ∨
      (newX = rxLocalCellXAt P S oldX cell (0, 1) ∧
        (Sum.inl localEdge : RX1 P S) =
          rxLocalCellQAt P S oldX cell (0, 1) 0) ∨
      (newX = rxLocalCellXAt P S oldX cell (0, 1) ∧
        (Sum.inl localEdge : RX1 P S) =
          rxLocalCellQAt P S oldX cell (0, 1) 1) ∨
      (newX = rxLocalCellXAt P S oldX cell (1, 0) ∧
        (Sum.inl localEdge : RX1 P S) =
          rxLocalCellQAt P S oldX cell (1, 0) 0) ∨
      (newX = rxLocalCellXAt P S oldX cell (1, 0) ∧
        (Sum.inl localEdge : RX1 P S) =
          rxLocalCellQAt P S oldX cell (1, 0) 1) ∨
      (newX = rxLocalCellXAt P S oldX cell (1, 1) ∧
        (Sum.inl localEdge : RX1 P S) =
          rxLocalCellQAt P S oldX cell (1, 1) 0) ∨
      (newX = rxLocalCellXAt P S oldX cell (1, 1) ∧
        (Sum.inl localEdge : RX1 P S) =
          rxLocalCellQAt P S oldX cell (1, 1) 1) := by
  classical
  let edge : XQEdge (rxReplacementPresentation P S) :=
    ⟨(newX, Sum.inl localEdge), incidence⟩
  simp only [zStarEdgeMember, decide_eq_true_eq] at member
  obtain ⟨face, hface, huse⟩ := member
  change decide (edge = faceXQEdge (rxReplacementPresentation P S) face 0 ∨
    edge = faceXQEdge (rxReplacementPresentation P S) face 1) = true at huse
  rw [decide_eq_true_eq] at huse
  have hfaceZ : rxFaceZ P S face =
      Sum.inl (Sum.inl ⟨oldX, cell⟩) := by
    simp only [zStarFaceMember, decide_eq_true_eq] at hface
    rw [show (rxReplacementPresentation P S).faceZ = rxFaceZ P S from rfl] at hface
    exact hface
  have route : ∀ (corner : Two × Two) (qCorner : Two),
      newX = rxLocalCellXAt P S oldX cell corner →
      (Sum.inl localEdge : RX1 P S) =
          rxLocalCellQAt P S oldX cell corner qCorner →
      (newX = rxLocalCellXAt P S oldX cell (0, 0) ∧
          (Sum.inl localEdge : RX1 P S) =
            rxLocalCellQAt P S oldX cell (0, 0) 0) ∨
        (newX = rxLocalCellXAt P S oldX cell (0, 0) ∧
          (Sum.inl localEdge : RX1 P S) =
            rxLocalCellQAt P S oldX cell (0, 0) 1) ∨
        (newX = rxLocalCellXAt P S oldX cell (0, 1) ∧
          (Sum.inl localEdge : RX1 P S) =
            rxLocalCellQAt P S oldX cell (0, 1) 0) ∨
        (newX = rxLocalCellXAt P S oldX cell (0, 1) ∧
          (Sum.inl localEdge : RX1 P S) =
            rxLocalCellQAt P S oldX cell (0, 1) 1) ∨
        (newX = rxLocalCellXAt P S oldX cell (1, 0) ∧
          (Sum.inl localEdge : RX1 P S) =
            rxLocalCellQAt P S oldX cell (1, 0) 0) ∨
        (newX = rxLocalCellXAt P S oldX cell (1, 0) ∧
          (Sum.inl localEdge : RX1 P S) =
            rxLocalCellQAt P S oldX cell (1, 0) 1) ∨
        (newX = rxLocalCellXAt P S oldX cell (1, 1) ∧
          (Sum.inl localEdge : RX1 P S) =
            rxLocalCellQAt P S oldX cell (1, 1) 0) ∨
        (newX = rxLocalCellXAt P S oldX cell (1, 1) ∧
          (Sum.inl localEdge : RX1 P S) =
            rxLocalCellQAt P S oldX cell (1, 1) 1) := by
    rintro ⟨first, second⟩ qCorner hx hq
    fin_cases first <;> fin_cases second <;> fin_cases qCorner
    · exact Or.inl ⟨hx, hq⟩
    · exact Or.inr (Or.inl ⟨hx, hq⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hx, hq⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hx, hq⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hx, hq⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hx, hq⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl ⟨hx, hq⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr ⟨hx, hq⟩))))))
  have routeFace : ∀ qCorner : Two,
      edge = faceXQEdge (rxReplacementPresentation P S) face qCorner →
      (newX = rxLocalCellXAt P S oldX cell (0, 0) ∧
          (Sum.inl localEdge : RX1 P S) =
            rxLocalCellQAt P S oldX cell (0, 0) 0) ∨
        (newX = rxLocalCellXAt P S oldX cell (0, 0) ∧
          (Sum.inl localEdge : RX1 P S) =
            rxLocalCellQAt P S oldX cell (0, 0) 1) ∨
        (newX = rxLocalCellXAt P S oldX cell (0, 1) ∧
          (Sum.inl localEdge : RX1 P S) =
            rxLocalCellQAt P S oldX cell (0, 1) 0) ∨
        (newX = rxLocalCellXAt P S oldX cell (0, 1) ∧
          (Sum.inl localEdge : RX1 P S) =
            rxLocalCellQAt P S oldX cell (0, 1) 1) ∨
        (newX = rxLocalCellXAt P S oldX cell (1, 0) ∧
          (Sum.inl localEdge : RX1 P S) =
            rxLocalCellQAt P S oldX cell (1, 0) 0) ∨
        (newX = rxLocalCellXAt P S oldX cell (1, 0) ∧
          (Sum.inl localEdge : RX1 P S) =
            rxLocalCellQAt P S oldX cell (1, 0) 1) ∨
        (newX = rxLocalCellXAt P S oldX cell (1, 1) ∧
          (Sum.inl localEdge : RX1 P S) =
            rxLocalCellQAt P S oldX cell (1, 1) 0) ∨
        (newX = rxLocalCellXAt P S oldX cell (1, 1) ∧
          (Sum.inl localEdge : RX1 P S) =
            rxLocalCellQAt P S oldX cell (1, 1) 1) := by
    intro qCorner hedge
    have hraw := congrArg Subtype.val hedge
    have hx : newX = rxFaceX P S face := congrArg Prod.fst hraw
    have hq : (Sum.inl localEdge : RX1 P S) =
        rxFaceQ P S face qCorner := congrArg Prod.snd hraw
    rcases face with localFaceData | glue | old
    · rcases localFaceData with ⟨ownerX, ownerCell, corner⟩
      change (Sum.inl (Sum.inl ⟨ownerX, ownerCell⟩) : RX2 P S) =
          Sum.inl (Sum.inl ⟨oldX, cell⟩) at hfaceZ
      have howner : (⟨ownerX, ownerCell⟩ :
          Σ x : P.X, DoubleCylinderFace P x S) = ⟨oldX, cell⟩ :=
        Sum.inl.inj (Sum.inl.inj hfaceZ)
      cases howner
      have hx' : newX = rxLocalCellXAt P S oldX cell corner := by
        simpa [rxLocalCellXAt, rxFaceX] using hx
      have hq' : (Sum.inl localEdge : RX1 P S) =
          rxLocalCellQAt P S oldX cell corner qCorner := by
        simpa [rxLocalCellQAt, rxFaceQ, localFaceQAt] using hq
      exact route corner qCorner hx' hq'
    · rcases glue with ⟨a, qEdge, endpoint⟩
      simp [rxFaceZ, glueFaceZ] at hfaceZ
    · rcases old with ⟨oldFace, copy⟩
      simp [rxFaceZ, oldZFaceZ] at hfaceZ
  exact huse.elim (routeFace 0) (routeFace 1)
noncomputable def rxLocalCellZBoundaryFaceOwnerLocalEdgeAtCorner
    (P : TannerSquarePresentation) (S : OddScale) (oldX : P.X)
    (cell : DoubleCylinderFace P oldX S) (newX : RX0 P S)
    (localEdge : Σ x : P.X, DoubleCylinderEdge P x S)
    (incidence : rxXQIncidence P S newX (Sum.inl localEdge) = true)
    (member : zStarEdgeMember (rxReplacementPresentation P S)
      (Sum.inl (Sum.inl ⟨oldX, cell⟩))
      (Sum.inl
        (⟨(newX, Sum.inl localEdge), incidence⟩ :
          XQEdge (rxReplacementPresentation P S))) = true)
    (corner : Two × Two) (qCorner : Two)
    (hx : newX = rxLocalCellXAt P S oldX cell corner)
    (hq : (Sum.inl localEdge : RX1 P S) =
      rxLocalCellQAt P S oldX cell corner qCorner) :
    {owner : ZStarFace (rxReplacementPresentation P S)
        (Sum.inl (Sum.inl ⟨oldX, cell⟩)) × Two //
      zStarFaceXQEdge (rxReplacementPresentation P S)
          (Sum.inl (Sum.inl ⟨oldX, cell⟩)) owner.1 owner.2 =
        ⟨Sum.inl
          (⟨(newX, Sum.inl localEdge), incidence⟩ :
            XQEdge (rxReplacementPresentation P S)), member⟩} := by
  let rawFace : RXFace P S := Sum.inl ⟨oldX, cell, corner⟩
  have hfaceX : rxFaceX P S rawFace = newX := by
    change localFaceX P S ⟨oldX, cell, corner⟩ = newX
    exact hx.symm
  have hfaceQ : rxFaceQ P S rawFace qCorner =
      (Sum.inl localEdge : RX1 P S) := by
    change localFaceQAt P S ⟨oldX, cell, corner⟩ qCorner = Sum.inl localEdge
    exact hq.symm
  let face := rxLocalCellZStarFace P S oldX cell corner
  refine ⟨(face, qCorner), ?_⟩
  apply Subtype.ext
  apply congrArg Sum.inl
  apply Subtype.ext
  exact Prod.ext hfaceX hfaceQ
noncomputable def rxLocalCellZBoundaryFaceOwnerLocalEdge
    (P : TannerSquarePresentation) (S : OddScale) (oldX : P.X)
    (cell : DoubleCylinderFace P oldX S) (newX : RX0 P S)
    (localEdge : Σ x : P.X, DoubleCylinderEdge P x S)
    (incidence : rxXQIncidence P S newX (Sum.inl localEdge) = true)
    (member : zStarEdgeMember (rxReplacementPresentation P S)
      (Sum.inl (Sum.inl ⟨oldX, cell⟩))
      (Sum.inl
        (⟨(newX, Sum.inl localEdge), incidence⟩ :
          XQEdge (rxReplacementPresentation P S))) = true) :
    {owner : ZStarFace (rxReplacementPresentation P S)
        (Sum.inl (Sum.inl ⟨oldX, cell⟩)) × Two //
      zStarFaceXQEdge (rxReplacementPresentation P S)
          (Sum.inl (Sum.inl ⟨oldX, cell⟩)) owner.1 owner.2 =
        ⟨Sum.inl
          (⟨(newX, Sum.inl localEdge), incidence⟩ :
            XQEdge (rxReplacementPresentation P S)), member⟩} := by
  classical
  have cases := rxZBoundaryLocalCellLocalEdge_pair_cases
    P S oldX cell newX localEdge incidence member
  by_cases h000 : newX = rxLocalCellXAt P S oldX cell (0, 0) ∧
      (Sum.inl localEdge : RX1 P S) =
        rxLocalCellQAt P S oldX cell (0, 0) 0
  · exact rxLocalCellZBoundaryFaceOwnerLocalEdgeAtCorner
      P S oldX cell newX localEdge incidence member (0, 0) 0 h000.1 h000.2
  · by_cases h001 : newX = rxLocalCellXAt P S oldX cell (0, 0) ∧
        (Sum.inl localEdge : RX1 P S) =
          rxLocalCellQAt P S oldX cell (0, 0) 1
    · exact rxLocalCellZBoundaryFaceOwnerLocalEdgeAtCorner
        P S oldX cell newX localEdge incidence member (0, 0) 1 h001.1 h001.2
    · by_cases h010 : newX = rxLocalCellXAt P S oldX cell (0, 1) ∧
          (Sum.inl localEdge : RX1 P S) =
            rxLocalCellQAt P S oldX cell (0, 1) 0
      · exact rxLocalCellZBoundaryFaceOwnerLocalEdgeAtCorner
          P S oldX cell newX localEdge incidence member (0, 1) 0 h010.1 h010.2
      · by_cases h011 :
            newX = rxLocalCellXAt P S oldX cell (0, 1) ∧
              (Sum.inl localEdge : RX1 P S) =
                rxLocalCellQAt P S oldX cell (0, 1) 1
        · exact rxLocalCellZBoundaryFaceOwnerLocalEdgeAtCorner
            P S oldX cell newX localEdge incidence member
              (0, 1) 1 h011.1 h011.2
        · by_cases h100 :
              newX = rxLocalCellXAt P S oldX cell (1, 0) ∧
                (Sum.inl localEdge : RX1 P S) =
                  rxLocalCellQAt P S oldX cell (1, 0) 0
          · exact rxLocalCellZBoundaryFaceOwnerLocalEdgeAtCorner
              P S oldX cell newX localEdge incidence member
                (1, 0) 0 h100.1 h100.2
          · by_cases h101 :
                newX = rxLocalCellXAt P S oldX cell (1, 0) ∧
                  (Sum.inl localEdge : RX1 P S) =
                    rxLocalCellQAt P S oldX cell (1, 0) 1
            · exact rxLocalCellZBoundaryFaceOwnerLocalEdgeAtCorner
                P S oldX cell newX localEdge incidence member
                  (1, 0) 1 h101.1 h101.2
            · by_cases h110 :
                  newX = rxLocalCellXAt P S oldX cell (1, 1) ∧
                    (Sum.inl localEdge : RX1 P S) =
                      rxLocalCellQAt P S oldX cell (1, 1) 0
              · exact rxLocalCellZBoundaryFaceOwnerLocalEdgeAtCorner
                  P S oldX cell newX localEdge incidence member
                    (1, 1) 0 h110.1 h110.2
              · have remaining001 := cases.resolve_left h000
                have remaining010 := remaining001.resolve_left h001
                have remaining011 := remaining010.resolve_left h010
                have remaining100 := remaining011.resolve_left h011
                have remaining101 := remaining100.resolve_left h100
                have remaining110 := remaining101.resolve_left h101
                have h111 := remaining110.resolve_left h110
                exact rxLocalCellZBoundaryFaceOwnerLocalEdgeAtCorner
                  P S oldX cell newX localEdge incidence member
                    (1, 1) 1 h111.1 h111.2
theorem rxZBoundaryXQ_to_zBoundaryX
    (P : TannerSquarePresentation) (S : OddScale)
    (zCoordinate : RX2 P S) (newX : RX0 P S) (newQ : RX1 P S)
    (incidence : rxXQIncidence P S newX newQ = true)
    (member : zStarEdgeMember (rxReplacementPresentation P S) zCoordinate
      (Sum.inl
        (⟨(newX, newQ), incidence⟩ :
          XQEdge (rxReplacementPresentation P S))) = true) :
    zStarBoundaryVertexMember (rxReplacementPresentation P S) zCoordinate
      (Vertex.x newX) = true := by
  classical
  simp only [zStarEdgeMember, decide_eq_true_eq] at member
  obtain ⟨face, hz, huse⟩ := member
  change decide
        ((⟨(newX, newQ), incidence⟩ :
              XQEdge (rxReplacementPresentation P S)) =
            faceXQEdge (rxReplacementPresentation P S) face 0 ∨
          (⟨(newX, newQ), incidence⟩ :
              XQEdge (rxReplacementPresentation P S)) =
            faceXQEdge (rxReplacementPresentation P S) face 1) = true at huse
  rw [decide_eq_true_eq] at huse
  simp only [zStarBoundaryVertexMember]
  rw [decide_eq_true_eq]
  refine ⟨face, hz, ?_⟩
  rcases huse with hzero | hone
  · exact congrArg
      (fun selected : XQEdge (rxReplacementPresentation P S) =>
        selected.1.1) hzero
  · exact congrArg
      (fun selected : XQEdge (rxReplacementPresentation P S) =>
        selected.1.1) hone
theorem rxZBoundaryXQ_to_zBoundaryQ
    (P : TannerSquarePresentation) (S : OddScale)
    (zCoordinate : RX2 P S) (newX : RX0 P S) (newQ : RX1 P S)
    (incidence : rxXQIncidence P S newX newQ = true)
    (member : zStarEdgeMember (rxReplacementPresentation P S) zCoordinate
      (Sum.inl
        (⟨(newX, newQ), incidence⟩ :
          XQEdge (rxReplacementPresentation P S))) = true) :
    zStarBoundaryVertexMember (rxReplacementPresentation P S) zCoordinate
      (Vertex.q newQ) = true := by
  classical
  simp only [zStarEdgeMember, decide_eq_true_eq] at member
  obtain ⟨face, hz, huse⟩ := member
  change decide
        ((⟨(newX, newQ), incidence⟩ :
              XQEdge (rxReplacementPresentation P S)) =
            faceXQEdge (rxReplacementPresentation P S) face 0 ∨
          (⟨(newX, newQ), incidence⟩ :
              XQEdge (rxReplacementPresentation P S)) =
            faceXQEdge (rxReplacementPresentation P S) face 1) = true at huse
  rw [decide_eq_true_eq] at huse
  simp only [zStarBoundaryVertexMember, decide_eq_true_eq]
  change (exists face : RXFace P S,
    zStarFaceMember (rxReplacementPresentation P S) zCoordinate face = true ∧
      (newQ = rxFaceQ P S face 0 ∨ newQ = rxFaceQ P S face 1))
  refine ⟨face, hz, ?_⟩
  rcases huse with hzero | hone
  · exact Or.inl (congrArg
      (fun selected : XQEdge (rxReplacementPresentation P S) =>
        selected.1.2) hzero)
  · exact Or.inr (congrArg
      (fun selected : XQEdge (rxReplacementPresentation P S) =>
        selected.1.2) hone)
noncomputable def rxQEdgeZBoundaryFaceOwnerLocalEdgeAtEndpoint
    (P : TannerSquarePresentation) (S : OddScale)
    (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S)
    (newX : RX0 P S) (localEdge : DoubleCylinderEdge P newX.1 S)
    (incidence : rxXQIncidence P S newX
      (Sum.inl ⟨newX.1, localEdge⟩) = true)
    (member : zStarEdgeMember (rxReplacementPresentation P S)
      (Sum.inl (Sum.inr qEdge))
      (Sum.inl
        (⟨(newX, Sum.inl ⟨newX.1, localEdge⟩), incidence⟩ :
          XQEdge (rxReplacementPresentation P S))) = true)
    (hxq : P.xq newX.1 qEdge.1 = true) (endpoint : Two)
    (hfaceX : glueFaceX P S
      ⟨(⟨(newX.1, qEdge.1), hxq⟩ : XQEdge P), qEdge.2, endpoint⟩ =
        newX)
    (hedge : localEdge = qToXDoubleCylinderEdgeRaw
      P qEdge.1 newX.1 hxq S qEdge.2) :
    {owner : ZStarFace (rxReplacementPresentation P S)
        (Sum.inl (Sum.inr qEdge)) × Two //
      zStarFaceXQEdge (rxReplacementPresentation P S)
          (Sum.inl (Sum.inr qEdge)) owner.1 owner.2 =
        ⟨Sum.inl
          (⟨(newX, Sum.inl ⟨newX.1, localEdge⟩), incidence⟩ :
            XQEdge (rxReplacementPresentation P S)), member⟩} := by
  let face := rxQEdgeGlueZStarFace P S qEdge newX.1 hxq endpoint
  have hfaceQ : rxFaceQ P S face.1 0 =
      Sum.inl ⟨newX.1, localEdge⟩ := by
    apply congrArg Sum.inl
    exact Sigma.ext rfl (by simpa only [heq_eq_eq] using hedge.symm)
  refine ⟨(face, 0), ?_⟩
  apply Subtype.ext
  apply congrArg Sum.inl
  apply Subtype.ext
  exact Prod.ext hfaceX hfaceQ
noncomputable def rxQEdgeZBoundaryFaceOwnerLocalEdge
    (P : TannerSquarePresentation) (S : OddScale)
    (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S)
    (newX : RX0 P S)
    (localEdge : Σ x : P.X, DoubleCylinderEdge P x S)
    (incidence : rxXQIncidence P S newX (Sum.inl localEdge) = true)
    (member : zStarEdgeMember (rxReplacementPresentation P S)
      (Sum.inl (Sum.inr qEdge))
      (Sum.inl
        (⟨(newX, Sum.inl localEdge), incidence⟩ :
          XQEdge (rxReplacementPresentation P S))) = true) :
    {owner : ZStarFace (rxReplacementPresentation P S)
        (Sum.inl (Sum.inr qEdge)) × Two //
      zStarFaceXQEdge (rxReplacementPresentation P S)
          (Sum.inl (Sum.inr qEdge)) owner.1 owner.2 =
        ⟨Sum.inl
          (⟨(newX, Sum.inl localEdge), incidence⟩ :
            XQEdge (rxReplacementPresentation P S)), member⟩} := by
  rcases localEdge with ⟨ownerX, localEdge⟩
  have endpointCases := rxLocalEdgeXCoordinate_endpoint_cases
    P S newX ownerX localEdge incidence
  have howner : newX.1 = ownerX := endpointCases.elim
    (fun h => congrArg Sigma.fst h)
    (fun h => congrArg Sigma.fst h)
  subst ownerX
  let xMember := rxZBoundaryXQ_to_zBoundaryX P S
    (Sum.inl (Sum.inr qEdge)) newX
      (Sum.inl ⟨newX.1, localEdge⟩) incidence member
  let qMember := rxZBoundaryXQ_to_zBoundaryQ P S
    (Sum.inl (Sum.inr qEdge)) newX
      (Sum.inl ⟨newX.1, localEdge⟩) incidence member
  let hxq := rxQEdgeBoundaryX_incidence P S qEdge newX xMember
  have hedge : localEdge = qToXDoubleCylinderEdgeRaw
      P qEdge.1 newX.1 hxq S qEdge.2 := by
    simpa using rxQEdgeBoundaryLocalQ_edge P S qEdge
      ⟨newX.1, localEdge⟩ qMember
  by_cases hzero : newX = glueFaceX P S
      ⟨(⟨(newX.1, qEdge.1), hxq⟩ : XQEdge P), qEdge.2, 0⟩
  · exact rxQEdgeZBoundaryFaceOwnerLocalEdgeAtEndpoint
      P S qEdge newX localEdge incidence member hxq 0 hzero.symm hedge
  · have hone := (rxQEdgeBoundaryX_endpoints
      P S qEdge newX xMember).resolve_left hzero
    exact rxQEdgeZBoundaryFaceOwnerLocalEdgeAtEndpoint
      P S qEdge newX localEdge incidence member hxq 1 hone.symm hedge
noncomputable def rxQEdgeZBoundaryFaceOwnerQVertexAtEndpoint
    (P : TannerSquarePresentation) (S : OddScale)
    (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S)
    (newX : RX0 P S) (endpoint : Two)
    (incidence : rxXQIncidence P S newX
      (Sum.inr ⟨qEdge.1, edgeEndpoint
        (qDoubleCylinderEdgeStart P qEdge.1 S)
        (qDoubleCylinderEdgeEnd P qEdge.1 S) qEdge.2 endpoint⟩) = true)
    (member : zStarEdgeMember (rxReplacementPresentation P S)
      (Sum.inl (Sum.inr qEdge))
      (Sum.inl
        (⟨(newX, Sum.inr ⟨qEdge.1, edgeEndpoint
              (qDoubleCylinderEdgeStart P qEdge.1 S)
              (qDoubleCylinderEdgeEnd P qEdge.1 S) qEdge.2 endpoint⟩),
            incidence⟩ : XQEdge (rxReplacementPresentation P S))) = true) :
    {owner : ZStarFace (rxReplacementPresentation P S)
        (Sum.inl (Sum.inr qEdge)) × Two //
      zStarFaceXQEdge (rxReplacementPresentation P S)
          (Sum.inl (Sum.inr qEdge)) owner.1 owner.2 =
        ⟨Sum.inl
          (⟨(newX, Sum.inr ⟨qEdge.1, edgeEndpoint
                (qDoubleCylinderEdgeStart P qEdge.1 S)
                (qDoubleCylinderEdgeEnd P qEdge.1 S) qEdge.2 endpoint⟩),
              incidence⟩ : XQEdge (rxReplacementPresentation P S)), member⟩} := by
  let vertex := edgeEndpoint
    (qDoubleCylinderEdgeStart P qEdge.1 S)
    (qDoubleCylinderEdgeEnd P qEdge.1 S) qEdge.2 endpoint
  let hxq := rxQVertexXRadial_oldXQ
    P S newX qEdge.1 vertex incidence
  let face := rxQEdgeGlueZStarFace P S qEdge newX.1 hxq endpoint
  have hfaceX : rxFaceX P S face.1 = newX := by
    exact rxQVertexGlueFaceX_eq P S newX qEdge.1 vertex incidence hxq
      qEdge.2 endpoint rfl
  have hfaceQ : rxFaceQ P S face.1 1 =
      Sum.inr ⟨qEdge.1, vertex⟩ := rfl
  refine ⟨(face, 1), ?_⟩
  apply Subtype.ext
  apply congrArg Sum.inl
  apply Subtype.ext
  exact Prod.ext hfaceX hfaceQ
noncomputable def rxQEdgeZBoundaryFaceOwnerQVertex
    (P : TannerSquarePresentation) (S : OddScale)
    (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S)
    (newX : RX0 P S)
    (qVertex : Σ q : P.Q, QDoubleCylinderVertex P q S)
    (incidence : rxXQIncidence P S newX (Sum.inr qVertex) = true)
    (member : zStarEdgeMember (rxReplacementPresentation P S)
      (Sum.inl (Sum.inr qEdge))
      (Sum.inl
        (⟨(newX, Sum.inr qVertex), incidence⟩ :
          XQEdge (rxReplacementPresentation P S))) = true) :
    {owner : ZStarFace (rxReplacementPresentation P S)
        (Sum.inl (Sum.inr qEdge)) × Two //
      zStarFaceXQEdge (rxReplacementPresentation P S)
          (Sum.inl (Sum.inr qEdge)) owner.1 owner.2 =
        ⟨Sum.inl
          (⟨(newX, Sum.inr qVertex), incidence⟩ :
            XQEdge (rxReplacementPresentation P S)), member⟩} := by
  let qMember := rxZBoundaryXQ_to_zBoundaryQ P S
    (Sum.inl (Sum.inr qEdge)) newX (Sum.inr qVertex) incidence member
  by_cases hstart : qVertex = ⟨qEdge.1,
      qDoubleCylinderEdgeStart P qEdge.1 S qEdge.2⟩
  · cases hstart
    exact rxQEdgeZBoundaryFaceOwnerQVertexAtEndpoint
      P S qEdge newX 0 incidence member
  · have hend := (rxQEdgeBoundaryQVertex_endpoints
      P S qEdge qVertex qMember).resolve_left hstart
    cases hend
    exact rxQEdgeZBoundaryFaceOwnerQVertexAtEndpoint
      P S qEdge newX 1 incidence member
theorem rxOldZBoundaryXQ_oldIncidence
    (P : TannerSquarePresentation) (S : OddScale)
    (oldZ : P.Z) (copy : Two) (newX : RX0 P S)
    (qVertex : Σ q : P.Q, QDoubleCylinderVertex P q S)
    (incidence : rxXQIncidence P S newX (Sum.inr qVertex) = true)
    (member : zStarEdgeMember (rxReplacementPresentation P S)
      (Sum.inr (oldZ, copy))
      (Sum.inl
        (⟨(newX, Sum.inr qVertex), incidence⟩ :
          XQEdge (rxReplacementPresentation P S))) = true) :
    P.xq newX.1 qVertex.1 = true := by
  classical
  let edge : XQEdge (rxReplacementPresentation P S) :=
    ⟨(newX, Sum.inr qVertex), incidence⟩
  simp only [zStarEdgeMember, decide_eq_true_eq] at member
  obtain ⟨face, hz, huse⟩ := member
  change decide (edge = faceXQEdge (rxReplacementPresentation P S) face 0 ∨
    edge = faceXQEdge (rxReplacementPresentation P S) face 1) = true at huse
  rw [decide_eq_true_eq] at huse
  have route : ∀ corner : Two,
      edge = faceXQEdge (rxReplacementPresentation P S) face corner →
        P.xq newX.1 qVertex.1 = true := by
    intro corner hedge
    have hraw := congrArg Subtype.val hedge
    have hx := congrArg Prod.fst hraw
    have hq := congrArg Prod.snd hraw
    rcases face with localFace | glue | oldFace
    · simp only [zStarFaceMember, decide_eq_true_eq] at hz
      cases hz
    · simp only [zStarFaceMember, decide_eq_true_eq] at hz
      cases hz
    · rcases oldFace with ⟨oldFace, storedCopy⟩
      have hfaceX : P.faceX oldFace = newX.1 :=
        (congrArg Sigma.fst hx).symm
      have hfaceQ : P.faceQ oldFace corner = qVertex.1 :=
        (congrArg Sigma.fst (Sum.inr.inj hq)).symm
      simpa [hfaceX, hfaceQ] using P.data.faceQ_xq oldFace corner
  exact huse.elim (route 0) (route 1)
theorem rxOldZBoundaryXQ_oldMember
    (P : TannerSquarePresentation) (S : OddScale)
    (oldZ : P.Z) (copy : Two) (newX : RX0 P S)
    (qVertex : Σ q : P.Q, QDoubleCylinderVertex P q S)
    (incidence : rxXQIncidence P S newX (Sum.inr qVertex) = true)
    (member : zStarEdgeMember (rxReplacementPresentation P S)
      (Sum.inr (oldZ, copy))
      (Sum.inl
        (⟨(newX, Sum.inr qVertex), incidence⟩ :
          XQEdge (rxReplacementPresentation P S))) = true)
    (oldIncidence : P.xq newX.1 qVertex.1 = true) :
    zStarEdgeMember P oldZ
      (Sum.inl (⟨(newX.1, qVertex.1), oldIncidence⟩ : XQEdge P)) = true := by
  classical
  let successorEdge : XQEdge (rxReplacementPresentation P S) :=
    ⟨(newX, Sum.inr qVertex), incidence⟩
  let oldEdge : XQEdge P := ⟨(newX.1, qVertex.1), oldIncidence⟩
  simp only [zStarEdgeMember, decide_eq_true_eq] at member
  obtain ⟨face, hz, huse⟩ := member
  change decide (successorEdge = faceXQEdge (rxReplacementPresentation P S) face 0 ∨
    successorEdge = faceXQEdge (rxReplacementPresentation P S) face 1) = true at huse
  rw [decide_eq_true_eq] at huse
  simp only [zStarEdgeMember, decide_eq_true_eq]
  have route : ∀ corner : Two,
      successorEdge =
          faceXQEdge (rxReplacementPresentation P S) face corner →
      ∃ oldFace : P.Face,
        zStarFaceMember P oldZ oldFace = true ∧
          decide (oldEdge = faceXQEdge P oldFace 0 ∨
            oldEdge = faceXQEdge P oldFace 1) = true := by
    intro corner hedge
    have hraw := congrArg Subtype.val hedge
    have hx := congrArg Prod.fst hraw
    have hq := congrArg Prod.snd hraw
    rcases face with localFace | glue | oldFace
    · simp only [zStarFaceMember, decide_eq_true_eq] at hz
      cases hz
    · simp only [zStarFaceMember, decide_eq_true_eq] at hz
      cases hz
    · rcases oldFace with ⟨oldFace, storedCopy⟩
      simp only [zStarFaceMember, decide_eq_true_eq] at hz
      have hzpair : (P.faceZ oldFace, storedCopy) = (oldZ, copy) :=
        Sum.inr.inj hz
      have hfaceZ : P.faceZ oldFace = oldZ := congrArg Prod.fst hzpair
      have hfaceX : P.faceX oldFace = newX.1 :=
        (congrArg Sigma.fst hx).symm
      have hfaceQ : P.faceQ oldFace corner = qVertex.1 :=
        (congrArg Sigma.fst (Sum.inr.inj hq)).symm
      refine ⟨oldFace, by simpa [zStarFaceMember] using hfaceZ, ?_⟩
      rw [decide_eq_true_eq]
      apply rxTwoElim (motive := fun corner =>
        P.faceX oldFace = newX.1 →
        P.faceQ oldFace corner = qVertex.1 →
          oldEdge = faceXQEdge P oldFace 0 ∨
            oldEdge = faceXQEdge P oldFace 1)
      · intro hx0 hq0
        left
        apply Subtype.ext
        exact Prod.ext hx0.symm hq0.symm
      · intro hx1 hq1
        right
        apply Subtype.ext
        exact Prod.ext hx1.symm hq1.symm
      · exact hfaceX
      · exact hfaceQ
  obtain ⟨oldFace, hmember, hedge⟩ := huse.elim (route 0) (route 1)
  exact ⟨oldFace, hmember, hedge⟩
noncomputable def rxOldZBoundaryEdgeProject
    (P : TannerSquarePresentation) (S : OddScale)
    (oldZ : P.Z) (copy : Two) :
    ZStarBoundaryEdge (rxReplacementPresentation P S)
        (Sum.inr (oldZ, copy)) → ZStarBoundaryEdge P oldZ :=
  fun successorEdge => by
    rcases successorEdge with ⟨raw, member⟩
    rcases raw with newXQ | impossible
    · rcases newXQ with ⟨⟨newX, newQ⟩, incidence⟩
      let successorEdge : ZStarBoundaryEdge
          (rxReplacementPresentation P S) (Sum.inr (oldZ, copy)) :=
        ⟨Sum.inl (⟨(newX, newQ), incidence⟩ :
          XQEdge (rxReplacementPresentation P S)), member⟩
      let qMember := (zBoundaryEdgeEnd (rxReplacementPresentation P S)
        (Sum.inr (oldZ, copy)) successorEdge).2
      have terminal := rxOldZBoundaryQ_terminal
        P S oldZ copy newQ qMember
      rcases newQ with localEdge | qVertex
      · exact terminal.elim
      · rcases qVertex with ⟨q, newCopy, vertex⟩
        rcases vertex with original | interior
        · rcases original with center | endpoint
          · exact terminal.elim
          · let qVertex : Σ q : P.Q, QDoubleCylinderVertex P q S :=
              ⟨q, (newCopy, Sum.inl (Sum.inr endpoint))⟩
            let oldIncidence := rxOldZBoundaryXQ_oldIncidence
              P S oldZ copy newX qVertex incidence member
            exact ⟨Sum.inl
              (⟨(newX.1, q), oldIncidence⟩ : XQEdge P),
              rxOldZBoundaryXQ_oldMember
                P S oldZ copy newX qVertex incidence member oldIncidence⟩
        · exact terminal.elim
    · simp [zStarBoundaryEdgeMember] at member
theorem rxOldZBoundaryEdgeMap_project
    (P : TannerSquarePresentation) (S : OddScale)
    (oldZ : P.Z) (copy : Two)
    (edge : ZStarBoundaryEdge (rxReplacementPresentation P S)
      (Sum.inr (oldZ, copy))) :
    rxOldZBoundaryEdgeMap P S oldZ copy
        (rxOldZBoundaryEdgeProject P S oldZ copy edge) = edge := by
  have hstart := rxOldZBoundaryVertexMap_project P S oldZ copy
    (zBoundaryEdgeStart (rxReplacementPresentation P S)
      (Sum.inr (oldZ, copy)) edge)
  have hend := rxOldZBoundaryVertexMap_project P S oldZ copy
    (zBoundaryEdgeEnd (rxReplacementPresentation P S)
      (Sum.inr (oldZ, copy)) edge)
  rcases edge with ⟨raw, member⟩
  rcases raw with newXQ | impossible
  · rcases newXQ with ⟨⟨newX, newQ⟩, incidence⟩
    let successorEdge : ZStarBoundaryEdge
        (rxReplacementPresentation P S) (Sum.inr (oldZ, copy)) :=
      ⟨Sum.inl (⟨(newX, newQ), incidence⟩ :
        XQEdge (rxReplacementPresentation P S)), member⟩
    let qMember := (zBoundaryEdgeEnd (rxReplacementPresentation P S)
      (Sum.inr (oldZ, copy)) successorEdge).2
    have terminal := rxOldZBoundaryQ_terminal P S oldZ copy newQ qMember
    rcases newQ with localEdge | qVertex
    · exact terminal.elim
    · rcases qVertex with ⟨q, newCopy, vertex⟩
      rcases vertex with original | interior
      · rcases original with center | endpoint
        · exact terminal.elim
        · apply Subtype.ext
          apply congrArg Sum.inl
          apply Subtype.ext
          exact Prod.ext
            (Vertex.x.inj (congrArg Subtype.val hstart))
            (Vertex.q.inj (congrArg Subtype.val hend))
      · exact terminal.elim
  · simp [zStarBoundaryEdgeMember] at member
noncomputable def rxOldZZBoundaryFaceOwnerTerminal
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (oldZ : P.Z) (copy : Two)
    (newX : RX0 P S) (newCopy : Two) (q : P.Q)
    (endpoint : QStarEdge P q)
    (incidence : rxXQIncidence P S newX
      (Sum.inr ⟨q, (newCopy, Sum.inl (Sum.inr endpoint))⟩) = true)
    (member : zStarEdgeMember (rxReplacementPresentation P S)
      (Sum.inr (oldZ, copy))
      (Sum.inl
        (⟨(newX,
            Sum.inr ⟨q, (newCopy, Sum.inl (Sum.inr endpoint))⟩),
          incidence⟩ : XQEdge (rxReplacementPresentation P S))) = true) :
    {owner : ZStarFace (rxReplacementPresentation P S)
        (Sum.inr (oldZ, copy)) × Two //
      zStarFaceXQEdge (rxReplacementPresentation P S)
          (Sum.inr (oldZ, copy)) owner.1 owner.2 =
        ⟨Sum.inl
          (⟨(newX,
              Sum.inr ⟨q, (newCopy, Sum.inl (Sum.inr endpoint))⟩),
            incidence⟩ : XQEdge (rxReplacementPresentation P S)), member⟩} := by
  let newQ : RX1 P S :=
    Sum.inr ⟨q, (newCopy, Sum.inl (Sum.inr endpoint))⟩
  let successorEdge : ZStarBoundaryEdge
      (rxReplacementPresentation P S) (Sum.inr (oldZ, copy)) :=
    ⟨Sum.inl (⟨(newX, newQ), incidence⟩ :
      XQEdge (rxReplacementPresentation P S)), member⟩
  let oldBoundary := rxOldZBoundaryEdgeProject
    P S oldZ copy successorEdge
  have hmapped : rxOldZBoundaryEdgeMap P S oldZ copy oldBoundary =
      successorEdge := rxOldZBoundaryEdgeMap_project
        P S oldZ copy successorEdge
  rcases oldBoundary with ⟨rawOld, oldMember⟩
  rcases rawOld with oldXQ | impossible
  · let selected := A4.zBoundaryFaceOwner oldZ oldXQ oldMember
    have hfaceZ : P.faceZ selected.1.1.1 = oldZ := by
      simpa [zStarFaceMember] using selected.1.1.2
    let face : ZStarFace (rxReplacementPresentation P S)
        (Sum.inr (oldZ, copy)) :=
      ⟨Sum.inr (Sum.inr (selected.1.1.1, copy)), by
        simp only [zStarFaceMember, decide_eq_true_eq]
        change rxFaceZ P S
          (Sum.inr (Sum.inr (selected.1.1.1, copy))) =
            Sum.inr (oldZ, copy)
        simp [rxFaceZ, oldZFaceZ, hfaceZ]⟩
    let selectedBoundary : ZStarBoundaryEdge P oldZ :=
      ⟨Sum.inl (faceXQEdge P selected.1.1.1 selected.1.2), by
        change decide (exists oldFace : P.Face,
          zStarFaceMember P oldZ oldFace = true ∧
            decide
              (faceXQEdge P selected.1.1.1 selected.1.2 =
                  faceXQEdge P oldFace 0 ∨
                faceXQEdge P selected.1.1.1 selected.1.2 =
                  faceXQEdge P oldFace 1) = true) = true
        rw [decide_eq_true_eq]
        refine ⟨selected.1.1.1, selected.1.1.2, ?_⟩
        rw [decide_eq_true_eq]
        exact rxTwoElim (motive := fun corner =>
          faceXQEdge P selected.1.1.1 corner =
              faceXQEdge P selected.1.1.1 0 ∨
            faceXQEdge P selected.1.1.1 corner =
              faceXQEdge P selected.1.1.1 1)
          (Or.inl rfl) (Or.inr rfl) selected.1.2⟩
    have hselectedBoundary : selectedBoundary =
        (⟨Sum.inl oldXQ, oldMember⟩ : ZStarBoundaryEdge P oldZ) := by
      apply Subtype.ext
      simpa [selectedBoundary, zStarFaceXQEdge] using
        congrArg Subtype.val selected.2
    have hlift := congrArg
      (rxOldZBoundaryEdgeMap P S oldZ copy) hselectedBoundary
    have hlifted : rxOldZBoundaryEdgeMap P S oldZ copy selectedBoundary =
        successorEdge := hlift.trans hmapped
    have hstartLifted := congrArg
      (zBoundaryEdgeStart (rxReplacementPresentation P S)
        (Sum.inr (oldZ, copy))) hlifted
    have hendLifted := congrArg
      (zBoundaryEdgeEnd (rxReplacementPresentation P S)
        (Sum.inr (oldZ, copy))) hlifted
    have hstart : rxOldZBoundaryVertexMap P S oldZ copy
          (zBoundaryEdgeStart P oldZ selectedBoundary) =
        zBoundaryEdgeStart (rxReplacementPresentation P S)
          (Sum.inr (oldZ, copy)) successorEdge :=
      (rxOldZBoundaryEdgeMap_start P S oldZ copy selectedBoundary).symm.trans
        hstartLifted
    have hend : rxOldZBoundaryVertexMap P S oldZ copy
          (zBoundaryEdgeEnd P oldZ selectedBoundary) =
        zBoundaryEdgeEnd (rxReplacementPresentation P S)
          (Sum.inr (oldZ, copy)) successorEdge :=
      (rxOldZBoundaryEdgeMap_end P S oldZ copy selectedBoundary).symm.trans
        hendLifted
    refine ⟨(face, selected.1.2), ?_⟩
    apply Subtype.ext
    apply congrArg Sum.inl
    apply Subtype.ext
    exact Prod.ext
      (by
        change rxFaceX P S face.1 = newX
        have hstartX := Vertex.x.inj (congrArg Subtype.val hstart)
        simp [faceXQEdge, face, selectedBoundary, rxFaceX, oldZFaceX,
          xStarFaceZVertex, oldFaceInXStar, hfaceZ,
          zBoundaryEdgeStart, rxOldZBoundaryVertexMap,
          rxOldZCopyXCoordinate, successorEdge, newQ] at hstartX ⊢
        exact hstartX)
      (by
        change rxFaceQ P S face.1 selected.1.2 = newQ
        simpa [faceXQEdge, face, selectedBoundary, rxFaceQ, oldZFaceQ,
          hfaceZ, Sigma.ext_iff,
          zBoundaryEdgeEnd, rxOldZBoundaryVertexMap,
          rxOldZCopyQCoordinate, successorEdge, newQ] using
        Sum.inr.inj (Vertex.q.inj (congrArg Subtype.val hend)))
  · simp [zStarBoundaryEdgeMember] at oldMember
theorem rxLocalCellBoundaryQ_localTag
    (P : TannerSquarePresentation) (S : OddScale) (oldX : P.X)
    (cell : DoubleCylinderFace P oldX S) (newQ : RX1 P S)
    (member : zStarBoundaryVertexMember (rxReplacementPresentation P S)
      (Sum.inl (Sum.inl ⟨oldX, cell⟩)) (Vertex.q newQ) = true) :
    match newQ with
    | Sum.inl _ => True
    | Sum.inr _ => False := by
  have cases := rxLocalCellBoundaryQ_cases P S oldX cell newQ member
  rcases cases with h | h | h | h | h | h | h | h <;>
    cases h <;> trivial
noncomputable def rxReplacementZBoundaryFaceOwner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (zCoordinate : (rxReplacementPresentation P S).Z)
    (edge : XQEdge (rxReplacementPresentation P S))
    (member : zStarEdgeMember (rxReplacementPresentation P S) zCoordinate
      (Sum.inl edge) = true) :
    {owner : ZStarFace (rxReplacementPresentation P S) zCoordinate × Two //
      zStarFaceXQEdge (rxReplacementPresentation P S) zCoordinate
          owner.1 owner.2 = ⟨Sum.inl edge, member⟩} := by
  rcases edge with ⟨⟨newX, newQ⟩, incidence⟩
  rcases zCoordinate with nonOldZ | oldZCopy
  · rcases nonOldZ with localCell | qEdge
    · rcases localCell with ⟨oldX, cell⟩
      rcases newQ with localEdge | qVertex
      · exact rxLocalCellZBoundaryFaceOwnerLocalEdge
          P S oldX cell newX localEdge incidence member
      · have qMember := rxZBoundaryXQ_to_zBoundaryQ P S
          (Sum.inl (Sum.inl ⟨oldX, cell⟩)) newX
            (Sum.inr qVertex) incidence member
        exact (rxLocalCellBoundaryQ_localTag
          P S oldX cell (Sum.inr qVertex) qMember).elim
    · rcases newQ with localEdge | qVertex
      · exact rxQEdgeZBoundaryFaceOwnerLocalEdge
          P S qEdge newX localEdge incidence member
      · exact rxQEdgeZBoundaryFaceOwnerQVertex
          P S qEdge newX qVertex incidence member
  · rcases oldZCopy with ⟨oldZ, copy⟩
    let qMember := rxZBoundaryXQ_to_zBoundaryQ P S
      (Sum.inr (oldZ, copy)) newX newQ incidence member
    have terminal := rxOldZBoundaryQ_terminal
      P S oldZ copy newQ qMember
    rcases newQ with localEdge | qVertex
    · exact terminal.elim
    · rcases qVertex with ⟨q, newCopy, vertex⟩
      rcases vertex with original | interior
      · rcases original with center | endpoint
        · exact terminal.elim
        · exact rxOldZZBoundaryFaceOwnerTerminal
            P A4 S oldZ copy newX newCopy q endpoint incidence member
      · exact terminal.elim
noncomputable def rxReplacementAdmissibleV3
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) :
    TannerSquareAdmissibleV3 (rxReplacementPresentation P S) where
  toTannerSquareAdmissibleV2 := rxReplacementAdmissibleV2 P A4 R S
  xRadialFaceOwner :=
    rxReplacementXRadialFaceOwner P A4.toTannerSquareAdmissibleV3 S
  zRadialFaceOwner := rxReplacementZRadialFaceOwner P A4 S
noncomputable def rxReplacementAdmissibleV4
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) :
    TannerSquareAdmissibleV4 (rxReplacementPresentation P S) where
  toTannerSquareAdmissibleV3 := rxReplacementAdmissibleV3 P A4 R S
  xBoundaryFaceOwner := rxReplacementXBoundaryFaceOwner P A4 S
  zBoundaryFaceOwner := rxReplacementZBoundaryFaceOwner P A4 S
theorem rxLocalFaceXZ_injective
    (P : TannerSquarePresentation) (S : OddScale) :
    Function.Injective (fun face : RXLocalFace P S =>
      (localFaceX P S face, localFaceZ P S face)) := by
  rintro ⟨firstX, firstCell, firstCorner⟩
    ⟨secondX, secondCell, secondCorner⟩ hpair
  have hx := congrArg Prod.fst hpair
  have hz := congrArg Prod.snd hpair
  change (Sum.inl (Sum.inl (⟨firstX, firstCell⟩ :
      Σ x : P.X, DoubleCylinderFace P x S)) : RX2 P S) =
    Sum.inl (Sum.inl (⟨secondX, secondCell⟩ :
      Σ x : P.X, DoubleCylinderFace P x S)) at hz
  have hcell : (⟨firstX, firstCell⟩ :
      Σ x : P.X, DoubleCylinderFace P x S) =
    ⟨secondX, secondCell⟩ := Sum.inl.inj (Sum.inl.inj hz)
  cases hcell
  have hcorner : firstCorner = secondCorner :=
    localFaceX_fixedCell_injective P firstX S firstCell hx
  cases hcorner
  rfl
theorem rxGlueFaceXZ_injective
    (P : TannerSquarePresentation) (S : OddScale) :
    Function.Injective (fun face : RXXQGlueFace P S =>
      (glueFaceX P S face, glueFaceZ P S face)) := by
  rintro ⟨firstA, firstEdge, firstEndpoint⟩
    ⟨secondA, secondEdge, secondEndpoint⟩ hpair
  have hx := congrArg Prod.fst hpair
  have hz := congrArg Prod.snd hpair
  change (Sum.inl (Sum.inr (⟨firstA.1.2, firstEdge⟩ :
      Σ q : P.Q, QDoubleCylinderEdge P q S)) : RX2 P S) =
    Sum.inl (Sum.inr (⟨secondA.1.2, secondEdge⟩ :
      Σ q : P.Q, QDoubleCylinderEdge P q S)) at hz
  have hqedge : (⟨firstA.1.2, firstEdge⟩ :
      Σ q : P.Q, QDoubleCylinderEdge P q S) =
    ⟨secondA.1.2, secondEdge⟩ := Sum.inr.inj (Sum.inl.inj hz)
  have hqbase : firstA.1.2 = secondA.1.2 := congrArg Sigma.fst hqedge
  have hxbase : firstA.1.1 = secondA.1.1 := congrArg Sigma.fst hx
  have ha : firstA = secondA := by
    apply Subtype.ext
    exact Prod.ext hxbase hqbase
  subst secondA
  have hedge : firstEdge = secondEdge :=
    eq_of_heq (Sigma.mk.inj_iff.mp hqedge).2
  subst secondEdge
  change (⟨firstA.1.1,
      edgeEndpoint (tannerDoubleCylinderEdgeStart P firstA.1.1 S)
        (tannerDoubleCylinderEdgeEnd P firstA.1.1 S)
        (qToXDoubleCylinderEdgeRaw P firstA.1.2 firstA.1.1 firstA.2 S
          firstEdge) firstEndpoint⟩ : RX0 P S) =
    ⟨firstA.1.1,
      edgeEndpoint (tannerDoubleCylinderEdgeStart P firstA.1.1 S)
        (tannerDoubleCylinderEdgeEnd P firstA.1.1 S)
        (qToXDoubleCylinderEdgeRaw P firstA.1.2 firstA.1.1 firstA.2 S
          firstEdge) secondEndpoint⟩ at hx
  injection hx with _ hvertex
  have hendpoint : firstEndpoint = secondEndpoint := by
    apply twoSelect_injective
      (tannerDoubleCylinderEdgeStart_ne_end P firstA.1.1 S
        (qToXDoubleCylinderEdgeRaw P firstA.1.2 firstA.1.1 firstA.2 S
          firstEdge))
    exact hvertex
  subst secondEndpoint
  rfl
theorem rxOldZFaceXZ_injective
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (S : OddScale) :
    Function.Injective (fun face : RXOldZFace P =>
      (oldZFaceX P S face, oldZFaceZ P S face)) := by
  rintro ⟨firstFace, firstCopy⟩ ⟨secondFace, secondCopy⟩ hpair
  have hx := congrArg Prod.fst hpair
  have hz := congrArg Prod.snd hpair
  change Sum.inr (P.faceZ firstFace, firstCopy) =
    Sum.inr (P.faceZ secondFace, secondCopy) at hz
  have hzpair : (P.faceZ firstFace, firstCopy) =
      (P.faceZ secondFace, secondCopy) := Sum.inr.inj hz
  have hcopy : firstCopy = secondCopy := congrArg Prod.snd hzpair
  have hxold : P.faceX firstFace = P.faceX secondFace :=
    congrArg Sigma.fst hx
  have hzold : P.faceZ firstFace = P.faceZ secondFace :=
    congrArg Prod.fst hzpair
  have hface : firstFace = secondFace :=
    R.faceXZ_injective (Prod.ext hxold hzold)
  subst secondFace
  subst secondCopy
  rfl
theorem rxFaceXZ_injective
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (S : OddScale) :
    Function.Injective (fun face : RXFace P S =>
      (rxFaceX P S face, rxFaceZ P S face)) := by
  intro first second hpair
  rcases first with firstLocal | firstGlue | firstOld <;>
    rcases second with secondLocal | secondGlue | secondOld
  · exact congrArg Sum.inl
      (rxLocalFaceXZ_injective P S (by
        simpa [rxFaceX, rxFaceZ] using hpair))
  · have hz := congrArg Prod.snd hpair
    simp [rxFaceZ, localFaceZ, glueFaceZ] at hz
  · have hz := congrArg Prod.snd hpair
    simp [rxFaceZ, localFaceZ, oldZFaceZ] at hz
  · have hz := congrArg Prod.snd hpair
    simp [rxFaceZ, glueFaceZ, localFaceZ] at hz
  · exact congrArg (fun face => Sum.inr (Sum.inl face))
      (rxGlueFaceXZ_injective P S (by
        simpa [rxFaceX, rxFaceZ] using hpair))
  · have hz := congrArg Prod.snd hpair
    simp [rxFaceZ, glueFaceZ, oldZFaceZ] at hz
  · have hz := congrArg Prod.snd hpair
    simp [rxFaceZ, oldZFaceZ, localFaceZ] at hz
  · have hz := congrArg Prod.snd hpair
    simp [rxFaceZ, oldZFaceZ, glueFaceZ] at hz
  · exact congrArg (fun face => Sum.inr (Sum.inr face))
      (rxOldZFaceXZ_injective P R S (by
        simpa [rxFaceX, rxFaceZ] using hpair))
noncomputable def rxReplacementCellularRegular
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (S : OddScale) :
    TannerSquareCellularRegular (rxReplacementPresentation P S) where
  faceXZ_injective := rxFaceXZ_injective P R S
@[simp] theorem subdivisionEdgeVertexMatrix_start_eq_one
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : SubdivisionEdge P x S) :
    subdivisionEdgeVertexMatrix P x S
        (subdivisionEdgeStart P x S edge) edge = 1 := by
  classical
  simp [subdivisionEdgeVertexMatrix, subdivisionEdgeStart_ne_end P x S edge]
@[simp] theorem subdivisionEdgeVertexMatrix_end_eq_one
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : SubdivisionEdge P x S) :
    subdivisionEdgeVertexMatrix P x S
        (subdivisionEdgeEnd P x S edge) edge = 1 := by
  classical
  simp [subdivisionEdgeVertexMatrix,
    Ne.symm (subdivisionEdgeStart_ne_end P x S edge)]
set_option maxHeartbeats 800000 in
theorem rxBoundaryMatrices_mul_xFace
    (P : TannerSquarePresentation) (S : OddScale)
    (xCoordinate : RX0 P S)
    (xFace : Σ x : P.X, DoubleCylinderFace P x S) :
    rxBoundaryProductMatrix P S xCoordinate
        (Sum.inl (Sum.inl xFace)) = 0 := by
  classical
  rcases xCoordinate with ⟨x, vertex⟩
  rcases xFace with ⟨x', face⟩
  by_cases hxx : x = x'
  · subst x'
    rw [rxBoundaryProductMatrix]
    simp only [Fintype.sum_sum_type]
    rw [Fintype.sum_sigma]
    rw [Finset.sum_eq_single x]
    · simp only [rxBoundary1Matrix, rxBoundary2Matrix, dite_true, mul_zero,
        Finset.sum_const_zero, add_zero]
      change (∑ edge : DoubleCylinderEdge P x S,
        doubleCylinderEdgeVertexMatrix P x S vertex edge *
          doubleCylinderFaceEdgeMatrix P x S edge face) = 0
      rw [← Matrix.mul_apply]
      rw [doubleCylinderEdgeVertexMatrix_mul_faceEdgeMatrix]
      rfl
    · intro y _hy hyx
      simp [rxBoundary1Matrix, rxBoundary2Matrix, hyx, Ne.symm hyx]
    · simp
  · rw [rxBoundaryProductMatrix]
    simp only [Fintype.sum_sum_type]
    rw [Fintype.sum_sigma]
    simp [rxBoundary1Matrix, rxBoundary2Matrix, hxx]
noncomputable def rxVertexIndicator {Vertex : Type}
    (first second : Vertex) : Field := by
  classical
  exact if first = second then 1 else 0
theorem rxSumMulIndicator {Index : Type}
    [Fintype Index] [DecidableEq Index]
    (value : Index → Field) (target : Index) :
    (∑ index : Index, value index *
      (if index = target then (1 : Field) else 0)) = value target := by
  classical
  simp
def rxFinTwoElim {motive : Fin 2 → Sort _}
    (zero : motive 0) (one : motive 1) (endpoint : Fin 2) : motive endpoint := by
  rcases endpoint with ⟨endpoint, hendpoint⟩
  rcases endpoint with _ | endpoint
  · exact zero
  · rcases endpoint with _ | endpoint
    · exact one
    · omega
theorem qDoubleCylinderVertexXIncidence_atRoot
    (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (q : P.Q) (hxq : P.xq x q = true)
    (root : QStarEdge P q) (qVertex : QDoubleCylinderVertex P q S)
    (xVertex : DoubleCylinderVertex P x S) :
    qDoubleCylinderVertexXIncidence P q x S xVertex qVertex =
      rxVertexIndicator xVertex
        (qToXDoubleCylinderVertexAtRoot P q x hxq S root qVertex) := by
  classical
  rcases xVertex with ⟨xCopy, xVertex⟩
  rcases qVertex with ⟨qCopy, qVertex⟩
  fin_cases xCopy <;> fin_cases qCopy
  all_goals
    rcases xVertex with oldVertex | edgeInterior | faceInterior
  all_goals
    rcases qVertex with oldVertex' | edgeInterior'
  all_goals
    first
    | (rcases oldVertex' with cone | endpoint <;>
        simp [qDoubleCylinderVertexXIncidence, qSubdivisionVertexXIncidence,
          qToXDoubleCylinderVertexAtRoot, qToXSubdivisionVertexAtRoot,
          qToXBoundaryVertexAtRoot, xStarBoundaryVertexToStar,
          xBoundaryEdgeStart, xBoundaryEdgeEnd, qToXBoundaryEdge,
          rxVertexIndicator, Subtype.ext_iff, Prod.ext_iff, hxq])
    | simp [qDoubleCylinderVertexXIncidence, qSubdivisionVertexXIncidence,
        qToXDoubleCylinderVertexAtRoot, qToXSubdivisionVertexAtRoot,
        qToXBoundaryVertexAtRoot, xStarBoundaryVertexToStar,
        xBoundaryEdgeStart, xBoundaryEdgeEnd, qToXBoundaryEdge,
        rxVertexIndicator, Subtype.ext_iff, Prod.ext_iff, hxq]
  all_goals
    rcases edgeInterior with ⟨⟨edge, hmem⟩, index⟩
    rcases edge with xqEdge | qzEdge
    · simp [xStarBoundaryEdgeToStar, rxVertexIndicator,
        Subtype.ext_iff] at hmem ⊢
    · simp [xStarBoundaryEdgeToStar, qToXBoundaryEdge,
        rxVertexIndicator, Subtype.ext_iff, Prod.ext_iff, and_assoc]
theorem qDoubleCylinderVertexXIncidence_endpoint
    (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (q : P.Q) (hxq : P.xq x q = true)
    (qEdge : QDoubleCylinderEdge P q S) (endpoint : Two)
    (xVertex : DoubleCylinderVertex P x S) :
    qDoubleCylinderVertexXIncidence P q x S xVertex
        (edgeEndpoint (qDoubleCylinderEdgeStart P q S)
          (qDoubleCylinderEdgeEnd P q S) qEdge endpoint) =
      rxVertexIndicator xVertex
        (edgeEndpoint (tannerDoubleCylinderEdgeStart P x S)
          (tannerDoubleCylinderEdgeEnd P x S)
          (qToXDoubleCylinderEdgeRaw P q x hxq S qEdge) endpoint) := by
  let root := qDoubleCylinderUnderlyingStarEdge P q S qEdge
  refine rxFinTwoElim (motive := fun endpoint =>
    qDoubleCylinderVertexXIncidence P q x S xVertex
        (edgeEndpoint (qDoubleCylinderEdgeStart P q S)
          (qDoubleCylinderEdgeEnd P q S) qEdge endpoint) =
      rxVertexIndicator xVertex
        (edgeEndpoint (tannerDoubleCylinderEdgeStart P x S)
          (tannerDoubleCylinderEdgeEnd P x S)
          (qToXDoubleCylinderEdgeRaw P q x hxq S qEdge) endpoint)) ?_ ?_ endpoint
  · simp only [edgeEndpoint, twoSelect_zero]
    rw [qDoubleCylinderVertexXIncidence_atRoot P S x q hxq root]
    rw [qToXDoubleCylinderEdgeRaw_start P q x hxq S root qEdge]
  · simp only [edgeEndpoint, twoSelect_one]
    rw [qDoubleCylinderVertexXIncidence_atRoot P S x q hxq root]
    rw [qToXDoubleCylinderEdgeRaw_end P q x hxq S root qEdge]
theorem doubleCylinderEdgeVertexMatrix_eq_endpointIndicators
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (vertex : DoubleCylinderVertex P x S)
    (edge : DoubleCylinderEdge P x S) :
    doubleCylinderEdgeVertexMatrix P x S vertex edge =
      rxVertexIndicator vertex (tannerDoubleCylinderEdgeStart P x S edge) +
        rxVertexIndicator vertex (tannerDoubleCylinderEdgeEnd P x S edge) := by
  classical
  rcases edge with ⟨copy, subdivisionEdge⟩ | boundaryVertex
  · rcases vertex with ⟨vertexCopy, vertexValue⟩
    fin_cases vertexCopy <;> fin_cases copy <;>
      simp [doubleCylinderEdgeVertexMatrix, subdivisionEdgeVertexMatrix,
        tannerDoubleCylinderEdgeStart, tannerDoubleCylinderEdgeEnd,
        rxVertexIndicator]
  · rcases vertex with ⟨vertexCopy, vertexValue⟩
    fin_cases vertexCopy <;>
      simp [doubleCylinderEdgeVertexMatrix, tannerDoubleCylinderEdgeStart,
        tannerDoubleCylinderEdgeEnd, rxVertexIndicator]
theorem qDoubleCylinderVertexZIncidence_eq_indicator
    (P : TannerSquarePresentation) (S : OddScale)
    (q : P.Q) (z : P.Z) (zCopy : Two) (hqz : P.qz q z = true)
    (vertex : QDoubleCylinderVertex P q S) :
    qDoubleCylinderVertexZIncidence P q S vertex (z, zCopy) =
      rxVertexIndicator vertex
        (zCopy, Sum.inl (Sum.inr (⟨z, hqz⟩ : QStarEdge P q))) := by
  classical
  rcases vertex with ⟨copy, vertex⟩
  fin_cases copy <;> fin_cases zCopy
  all_goals rcases vertex with (cone | endpoint) | interior
  all_goals
    simp [qDoubleCylinderVertexZIncidence, rxVertexIndicator, hqz,
      Subtype.ext_iff]
set_option maxHeartbeats 800000 in
theorem rxBoundaryMatrices_mul_qEdge
    (P : TannerSquarePresentation) (S : OddScale)
    (xCoordinate : RX0 P S)
    (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S) :
    rxBoundaryProductMatrix P S xCoordinate
        (Sum.inl (Sum.inr qEdge)) = 0 := by
  classical
  rcases xCoordinate with ⟨x, xVertex⟩
  rcases qEdge with ⟨q, qEdge⟩
  rw [rxBoundaryProductMatrix]
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_sigma, Fintype.sum_sigma]
  simp only [rxBoundary1Matrix, rxBoundary2Matrix]
  simp
  by_cases hxq : P.xq x q = true
  · let mapped := qToXDoubleCylinderEdgeRaw P q x hxq S qEdge
    have hX :
        (∑ edge : DoubleCylinderEdge P x S,
          doubleCylinderEdgeVertexMatrix P x S xVertex edge *
            qDoubleCylinderEdgeXIncidence P q x S edge qEdge) =
          doubleCylinderEdgeVertexMatrix P x S xVertex mapped := by
      rw [Finset.sum_eq_single mapped]
      · simp [qDoubleCylinderEdgeXIncidence, hxq, mapped]
      · intro other _ hother
        rw [qDoubleCylinderEdgeXIncidence]
        rw [dif_pos hxq]
        rw [if_neg]
        simp
        intro heq
        apply hother
        simpa [mapped] using heq
      · simp
    have hQ :
        (∑ vertex : QDoubleCylinderVertex P q S,
          qDoubleCylinderVertexXIncidence P q x S xVertex vertex *
            qDoubleCylinderEdgeVertexIncidence P q S vertex qEdge) =
          qDoubleCylinderVertexXIncidence P q x S xVertex
              (qDoubleCylinderEdgeStart P q S qEdge) +
            qDoubleCylinderVertexXIncidence P q x S xVertex
              (qDoubleCylinderEdgeEnd P q S qEdge) := by
      simp only [qDoubleCylinderEdgeVertexIncidence, mul_add,
        Finset.sum_add_distrib, rxSumMulIndicator]
    have hXsplit :
        (∑ edge : Two × SubdivisionEdge P x S,
            doubleCylinderEdgeVertexMatrix P x S xVertex (Sum.inl edge) *
              qDoubleCylinderEdgeXIncidence P q x S (Sum.inl edge) qEdge) +
          ∑ vertex : SubdivisionBoundaryVertex P x S,
            doubleCylinderEdgeVertexMatrix P x S xVertex (Sum.inr vertex) *
              qDoubleCylinderEdgeXIncidence P q x S (Sum.inr vertex) qEdge =
          doubleCylinderEdgeVertexMatrix P x S xVertex mapped := by
      simpa only [Fintype.sum_sum_type] using hX
    have hstart :
        qDoubleCylinderVertexXIncidence P q x S xVertex
            (qDoubleCylinderEdgeStart P q S qEdge) =
          rxVertexIndicator xVertex
            (tannerDoubleCylinderEdgeStart P x S mapped) := by
      simpa only [edgeEndpoint, twoSelect_zero, mapped] using
        qDoubleCylinderVertexXIncidence_endpoint P S x q hxq qEdge 0 xVertex
    have hend :
        qDoubleCylinderVertexXIncidence P q x S xVertex
            (qDoubleCylinderEdgeEnd P q S qEdge) =
          rxVertexIndicator xVertex
            (tannerDoubleCylinderEdgeEnd P x S mapped) := by
      simpa only [edgeEndpoint, twoSelect_one, mapped] using
        qDoubleCylinderVertexXIncidence_endpoint P S x q hxq qEdge 1 xVertex
    rw [hXsplit, hQ]
    rw [hstart, hend]
    rw [doubleCylinderEdgeVertexMatrix_eq_endpointIndicators]
    exact ZModModule.add_self _
  · simp [qDoubleCylinderEdgeXIncidence,
      qDoubleCylinderVertexXIncidence, qSubdivisionVertexXIncidence, hxq]
set_option maxHeartbeats 800000 in
theorem rxBoundaryMatrices_mul_zPoint
    (P : TannerSquarePresentation) (S : OddScale)
    (xCoordinate : RX0 P S) (zPoint : P.Z × Two) :
    rxBoundaryProductMatrix P S xCoordinate (Sum.inr zPoint) = 0 := by
  classical
  rcases xCoordinate with ⟨x, xVertex⟩
  rcases zPoint with ⟨z, zCopy⟩
  rw [rxBoundaryProductMatrix]
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_sigma, Fintype.sum_sigma]
  simp only [rxBoundary1Matrix, rxBoundary2Matrix, mul_zero,
    Finset.sum_const_zero, zero_add]
  have hreduce :
      (∑ q : P.Q, ∑ vertex : QDoubleCylinderVertex P q S,
        qDoubleCylinderVertexXIncidence P q x S xVertex vertex *
          qDoubleCylinderVertexZIncidence P q S vertex (z, zCopy)) =
        ∑ q : P.Q, if hqz : P.qz q z = true then
          qDoubleCylinderVertexXIncidence P q x S xVertex
            (zCopy, Sum.inl (Sum.inr (⟨z, hqz⟩ : QStarEdge P q)))
        else 0 := by
    apply Finset.sum_congr rfl
    intro q _
    by_cases hqz : P.qz q z = true
    · rw [dif_pos hqz]
      simp_rw [qDoubleCylinderVertexZIncidence_eq_indicator P S q z zCopy hqz]
      simp [rxVertexIndicator]
    · rw [dif_neg hqz]
      simp [qDoubleCylinderVertexZIncidence, hqz]
  rw [hreduce]
  rcases xVertex with ⟨xCopy, xVertex⟩
  fin_cases xCopy <;> fin_cases zCopy
  all_goals rcases xVertex with oldVertex | edgeInterior | faceInterior
  all_goals
    first
    | (rcases oldVertex with ⟨oldVertex, hmem⟩;
       rcases oldVertex with oldX | oldQ | oldZ)
    | skip
  all_goals
    try simp [qDoubleCylinderVertexXIncidence, qSubdivisionVertexXIncidence]
  all_goals
    by_cases hzz : oldZ = z
    · subst oldZ
      calc
        _ = ∑ q : P.Q,
            if P.xq x q && P.qz q z then (1 : Field) else 0 := by
          apply Finset.sum_congr rfl
          intro q _
          by_cases hxq : P.xq x q = true <;>
            by_cases hqz : P.qz q z = true <;>
              simp [hxq, hqz, Subtype.ext_iff]
        _ = 0 := sharedQ_indicator_sum_zero P x z
    · simp [hzz]
theorem rxBoundaryMatrices_mul
    (P : TannerSquarePresentation) (S : OddScale) :
    rxBoundaryProductMatrix P S = 0 := by
  classical
  ext xCoordinate zCoordinate
  rcases zCoordinate with (xFace | qEdge) | zPoint
  · exact rxBoundaryMatrices_mul_xFace P S xCoordinate xFace
  · exact rxBoundaryMatrices_mul_qEdge P S xCoordinate qEdge
  · exact rxBoundaryMatrices_mul_zPoint P S xCoordinate zPoint
noncomputable def rxBoundary1
    (P : TannerSquarePresentation) (S : OddScale) :
    Word Field (RX1 P S) →ₗ[Field] Word Field (RX0 P S) := by
  classical
  exact Matrix.toLin' (rxBoundary1Matrix P S)
noncomputable def rxBoundary2
    (P : TannerSquarePresentation) (S : OddScale) :
    Word Field (RX2 P S) →ₗ[Field] Word Field (RX1 P S) := by
  classical
  exact Matrix.toLin' (rxBoundary2Matrix P S)
theorem rxBoundary_squared
    (P : TannerSquarePresentation) (S : OddScale) :
    (rxBoundary1 P S).comp (rxBoundary2 P S) = 0 := by
  classical
  change (Matrix.toLin' (rxBoundary1Matrix P S)).comp
    (Matrix.toLin' (rxBoundary2Matrix P S)) = 0
  rw [← Matrix.toLin'_mul (rxBoundary1Matrix P S) (rxBoundary2Matrix P S)]
  change Matrix.toLin' (rxBoundaryProductMatrix P S) = 0
  rw [rxBoundaryMatrices_mul]
  simp
noncomputable def rxCx (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :
    ChainComplexData Field
      (Word Field (DoubleCylinderVertex P x S))
      (Word Field (DoubleCylinderEdge P x S))
      (Word Field (DoubleCylinderFace P x S)) :=
  doubleCylinderChainComplex P x S
noncomputable def rxCq (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) :
    ChainComplexData Field
      (Word Field (Fin 0))
      (Word Field (QDoubleCylinderVertex P q S))
      (Word Field (QDoubleCylinderEdge P q S)) where
  boundary1 := 0
  boundary2 := qDoubleCylinderBoundary1 P q S
  boundary_squared := by simp
noncomputable def rxCz (_P : TannerSquarePresentation) (_z : _P.Z) :
    ChainComplexData Field
      (Word Field (Fin 0)) (Word Field (Fin 0)) (Word Field Two) where
  boundary1 := 0
  boundary2 := 0
  boundary_squared := by simp
noncomputable def rxTotalChainComplex
    (P : TannerSquarePresentation) (S : OddScale) :
    ChainComplexData Field
      (Word Field (RX0 P S))
      (Word Field (RX1 P S))
      (Word Field (RX2 P S)) where
  boundary1 := rxBoundary1 P S
  boundary2 := rxBoundary2 P S
  boundary_squared := rxBoundary_squared P S
def wordPullback {Source Target : Type}
    (map : Source → Target) : Word Field Target →ₗ[Field] Word Field Source where
  toFun := fun word source => word (map source)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
@[simp] theorem wordPullback_apply {Source Target : Type}
    (map : Source → Target) (word : Word Field Target) (source : Source) :
    wordPullback map word source = word (map source) := rfl
theorem wordLinearMapTranspose_graphBoundary_apply
    {Vertex Edge : Type} [Fintype Vertex] [Fintype Edge]
    [DecidableEq Vertex] [DecidableEq Edge]
    (edgeStart edgeEnd : Edge → Vertex) (word : Word Field Vertex)
    (edge : Edge) :
    wordLinearMapTranspose (graphBoundary edgeStart edgeEnd) word edge =
      word (edgeStart edge) + word (edgeEnd edge) := by
  have hpair := wordPairing_wordLinearMapTranspose
    (graphBoundary edgeStart edgeEnd) word
    (Pi.single edge (1 : Field))
  simpa only [wordPairing_apply, dotProduct_single_one,
    graphBoundary_single, graphEdgeBoundary, dotProduct_add] using hpair
theorem wordPullback_graphCoboundary
    {SourceVertex SourceEdge TargetVertex TargetEdge : Type}
    [Fintype SourceVertex] [Fintype SourceEdge]
    [Fintype TargetVertex] [Fintype TargetEdge]
    [DecidableEq SourceVertex] [DecidableEq SourceEdge]
    [DecidableEq TargetVertex] [DecidableEq TargetEdge]
    (sourceStart sourceEnd : SourceEdge → SourceVertex)
    (targetStart targetEnd : TargetEdge → TargetVertex)
    (vertexMap : SourceVertex → TargetVertex)
    (edgeMap : SourceEdge → TargetEdge)
    (start_commutes : ∀ edge, targetStart (edgeMap edge) =
      vertexMap (sourceStart edge))
    (end_commutes : ∀ edge, targetEnd (edgeMap edge) =
      vertexMap (sourceEnd edge)) :
    (wordLinearMapTranspose (graphBoundary sourceStart sourceEnd)).comp
        (wordPullback vertexMap) =
      (wordPullback edgeMap).comp
        (wordLinearMapTranspose (graphBoundary targetStart targetEnd)) := by
  classical
  apply LinearMap.ext
  intro word
  ext edge
  simp only [LinearMap.comp_apply, wordPullback_apply,
    wordLinearMapTranspose_graphBoundary_apply]
  rw [start_commutes edge, end_commutes edge]
def rxSubdivisionSegmentVertex
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : XStarEdge P x) (step : Nat) (hstep : step ≤ S.half) :
    SubdivisionVertex P x S :=
  if hzero : step = 0 then
    Sum.inl (xStarEdgeStart P x edge)
  else if hlast : step = S.half then
    Sum.inl (xStarEdgeEnd P x edge)
  else
    Sum.inr (Sum.inl (edge, ⟨step - 1, by omega⟩))
noncomputable def rxSubdivisionSegmentPath
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : XStarEdge P x) :
    (step : Nat) → (hstep : step ≤ S.half) →
      UndirectedPath (subdivisionEdgeStart P x S)
        (subdivisionEdgeEnd P x S) (Sum.inl (xStarEdgeStart P x edge))
        (rxSubdivisionSegmentVertex P x S edge step hstep)
  | 0, _ => .nil
  | step + 1, hstep => by
      have hindex : step < S.half := by omega
      let index : Fin S.half := ⟨step, hindex⟩
      apply UndirectedPath.step
        (rxSubdivisionSegmentPath P x S edge step (by omega))
        (Sum.inl (edge, index))
      exact Or.inl ⟨by
        have hnotlast : step ≠ S.half := by omega
        simp [rxSubdivisionSegmentVertex, subdivisionEdgeStart, index,
          subdivisionSegmentStart, hnotlast], by
        simp [rxSubdivisionSegmentVertex, subdivisionEdgeEnd, index,
          subdivisionSegmentEnd]⟩
noncomputable def doubleCylinderGraphBoundary
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Word Field (DoubleCylinderEdge P x S) →ₗ[Field]
      Word Field (DoubleCylinderVertex P x S) := by
  classical
  exact graphBoundary (tannerDoubleCylinderEdgeStart P x S)
    (tannerDoubleCylinderEdgeEnd P x S)
theorem doubleCylinderGraphBoundary_eq_boundary1
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    doubleCylinderGraphBoundary P x S = doubleCylinderBoundary1 P x S := by
  classical
  apply LinearMap.ext
  intro word
  rw [← word_eq_sum_single (F := Field) word]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro edge _
  have hsingle : Pi.single edge (word edge) =
      word edge • Pi.single edge (1 : Field) := by
    ext other
    change (Pi.single edge (word edge) :
        Word Field (DoubleCylinderEdge P x S)) other =
      word edge *
        (Pi.single edge (1 : Field) :
          Word Field (DoubleCylinderEdge P x S)) other
    rw [Pi.single_apply, Pi.single_apply]
    by_cases h : other = edge <;> simp [h]
  rw [hsingle]
  simp only [map_smul]
  apply congrArg (fun value => word edge • value)
  rw [doubleCylinderGraphBoundary, graphBoundary_single]
  ext vertex
  simp only [doubleCylinderBoundary1, Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct]
  rw [Fintype.sum_eq_single edge]
  · rcases edge with ⟨copy, subdivisionEdge⟩ | boundaryVertex
    · rcases vertex with ⟨vertexCopy, vertexValue⟩
      fin_cases vertexCopy <;> fin_cases copy <;>
        simp [doubleCylinderEdgeVertexMatrix, subdivisionEdgeVertexMatrix,
          graphEdgeBoundary, tannerDoubleCylinderEdgeStart,
          tannerDoubleCylinderEdgeEnd, Pi.single_apply]
    · rcases vertex with ⟨vertexCopy, vertexValue⟩
      fin_cases vertexCopy <;>
        simp [doubleCylinderEdgeVertexMatrix, graphEdgeBoundary,
          tannerDoubleCylinderEdgeStart, tannerDoubleCylinderEdgeEnd,
          Pi.single_apply]
  · intro other hne
    simp [hne]
noncomputable abbrev RXH0 (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :=
  LinearMap.ker (wordLinearMapTranspose (rxCx P x S).boundary1)
def rxCxH0Coordinate (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (x : P.X) (S : OddScale) :
    RXH0 P x S →ₗ[Field] Field where
  toFun := fun word => word.1
    (0, (subdivisionOriginalBoundaryVertex P x S (A.xBoundaryRoot x)).1)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
noncomputable abbrev RXH1 (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :=
  (rxCx P x S).middleCohomology
noncomputable def rxCxH1Coordinate (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) :
    RXH1 P x S →ₗ[Field] Word Field (Fin 0) := 0
def rxCxH1_segmentPrefix
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S)) (copy : Two)
    (edge : XStarEdge P x) :
    (step : Nat) → step ≤ S.half → Field
  | 0, _ => 0
  | step + 1, hstep =>
      rxCxH1_segmentPrefix P x S word copy edge step (by omega) +
        word (Sum.inl (copy, Sum.inl (edge, ⟨step, by omega⟩)))
def rxCxH1_horizontalPrefix
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S)) (copy : Two)
    (face : XStarFace P x) :
    (step : Nat) → step ≤ S.half → Field
  | 0, _ => 0
  | step + 1, hstep =>
      rxCxH1_horizontalPrefix P x S word copy face step (by omega) +
        word (Sum.inl (copy, subdivisionHorizontalEdge P x S face
          ⟨step, by omega⟩ 0))
def rxCxH1_verticalPrefix
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S)) (copy : Two)
    (face : XStarFace P x) (horizontal : Fin (S.half + 1)) :
    (step : Nat) → step ≤ S.half → Field
  | 0, _ => 0
  | step + 1, hstep =>
      rxCxH1_verticalPrefix P x S word copy face horizontal step (by omega) +
        word (Sum.inl (copy, subdivisionVerticalEdge P x S face horizontal
          ⟨step, by omega⟩))
theorem rxCxH1_qIncidence
    (P : TannerSquarePresentation) (x : P.X) (q : P.Q)
    (member : xStarVertexMember P x (Vertex.q q) = true) :
    P.xq x q = true := by
  change decide (∃ face : P.Face,
    xStarFaceMember P x face = true ∧
      (q = P.faceQ face 0 ∨ q = P.faceQ face 1)) = true at member
  obtain ⟨face, hface, hcorner⟩ := of_decide_eq_true member
  have hx : P.faceX face = x := by
    simpa [xStarFaceMember] using hface
  rcases hcorner with hcorner | hcorner
  · simpa [hx, hcorner] using P.data.faceQ_xq face 0
  · simpa [hx, hcorner] using P.data.faceQ_xq face 1
theorem rxCxH1_qRadialMember
    (P : TannerSquarePresentation) (x : P.X) (q : P.Q)
    (member : xStarVertexMember P x (Vertex.q q) = true) :
    xStarEdgeMember P x
      (Sum.inl (⟨(x, q), rxCxH1_qIncidence P x q member⟩ : XQEdge P)) =
        true := by
  change decide (∃ rawFace : P.Face,
    xStarFaceMember P x rawFace = true ∧
      (q = P.faceQ rawFace 0 ∨ q = P.faceQ rawFace 1)) = true at member
  obtain ⟨rawFace, hface, hcorner⟩ := of_decide_eq_true member
  let face : XStarFace P x := ⟨rawFace, hface⟩
  have hx : P.faceX rawFace = x := by
    simpa [xStarFaceMember] using hface
  rcases hcorner with hcorner | hcorner
  · have hedge :
        (⟨(x, q), rxCxH1_qIncidence P x q member⟩ : XQEdge P) =
          faceXQEdge P rawFace 0 := by
      apply Subtype.ext
      change (x, q) = (P.faceX rawFace, P.faceQ rawFace 0)
      simp [hx, hcorner]
    rw [hedge]
    exact (xStarFaceXQEdge P x face 0).2
  · have hedge :
        (⟨(x, q), rxCxH1_qIncidence P x q member⟩ : XQEdge P) =
          faceXQEdge P rawFace 1 := by
      apply Subtype.ext
      change (x, q) = (P.faceX rawFace, P.faceQ rawFace 1)
      simp [hx, hcorner]
    rw [hedge]
    exact (xStarFaceXQEdge P x face 1).2
def rxCxH1_qRadialEdge
    (P : TannerSquarePresentation) (x : P.X) (q : P.Q)
    (member : xStarVertexMember P x (Vertex.q q) = true) :
    XStarEdge P x :=
  ⟨Sum.inl
      (⟨(x, q), rxCxH1_qIncidence P x q member⟩ : XQEdge P),
    rxCxH1_qRadialMember P x q member⟩
theorem rxCxH1_qMember_of_qzMember
    (P : TannerSquarePresentation) (x : P.X) (edge : QZEdge P)
    (member : xStarEdgeMember P x (Sum.inr edge) = true) :
    xStarVertexMember P x (Vertex.q edge.1.1) = true := by
  let starEdge : XStarEdge P x := ⟨Sum.inr edge, member⟩
  have startMember := (xStarEdgeStart P x starEdge).2
  change xStarVertexMember P x (Vertex.q edge.1.1) = true at startMember
  exact startMember
def rxCxH1_qPotential
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S)) (copy : Two)
    (q : P.Q) (member : xStarVertexMember P x (Vertex.q q) = true) : Field :=
  rxCxH1_segmentPrefix P x S word copy
    (rxCxH1_qRadialEdge P x q member) S.half (le_refl S.half)
def rxCxH1_oldZOwnerPotential
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S)) (copy : Two)
    (ownerEdge : XStarBoundaryEdge P x) : Field := by
  rcases ownerEdge with ⟨rawEdge, edgeMember⟩
  rcases rawEdge with impossible | qzEdge
  · simp [xStarBoundaryEdgeMember] at edgeMember
  · have starMember : xStarEdgeMember P x (Sum.inr qzEdge) = true :=
      edgeMember
    have qMember : xStarVertexMember P x (Vertex.q qzEdge.1.1) = true :=
      rxCxH1_qMember_of_qzMember P x qzEdge starMember
    let starEdge : XStarEdge P x :=
      ⟨Sum.inr qzEdge, starMember⟩
    exact rxCxH1_qPotential P x S word copy qzEdge.1.1 qMember +
      rxCxH1_segmentPrefix P x S word copy starEdge S.half
        (le_refl S.half)
noncomputable def rxCxH1_oldVertexPotential
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S)) (copy : Two)
    (vertex : XStarVertex P x) : Field := by
  rcases vertex with ⟨rawVertex, member⟩
  rcases rawVertex with oldX | oldQ | oldZ
  · exact 0
  · exact rxCxH1_qPotential P x S word copy oldQ member
  · let boundaryVertex : XStarBoundaryVertex P x :=
      ⟨Vertex.z oldZ, member⟩
    let owner := A3.toTannerSquareAdmissibleV2.xBoundaryIncidentEdge
      x boundaryVertex
    exact rxCxH1_oldZOwnerPotential P x S word copy owner.1.1
noncomputable def rxCxH1_subdivisionPotential
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S)) (copy : Two)
    (vertex : SubdivisionVertex P x S) : Field := by
  rcases vertex with oldVertex | edgeInterior | faceInterior
  · exact rxCxH1_oldVertexPotential P A3 x S word copy oldVertex
  · rcases edgeInterior with ⟨edge, index⟩
    exact rxCxH1_oldVertexPotential P A3 x S word copy
        (xStarEdgeStart P x edge) +
      rxCxH1_segmentPrefix P x S word copy edge (index.1 + 1) (by
        have := index.2
        omega)
  · rcases faceInterior with ⟨face, i, j⟩
    let horizontal : Fin (S.half + 1) := ⟨i.1 + 1, by
      have := i.2
      have := S.half_pos
      omega⟩
    exact rxCxH1_horizontalPrefix P x S word copy face (i.1 + 1) (by
        have := i.2
        omega) +
      rxCxH1_verticalPrefix P x S word copy face horizontal (j.1 + 1) (by
        have := j.2
        omega)
noncomputable def rxCxH1_glueDiscrepancy
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S))
    (vertex : SubdivisionBoundaryVertex P x S) : Field :=
  rxCxH1_subdivisionPotential P A3 x S word 0 vertex.1 +
    rxCxH1_subdivisionPotential P A3 x S word 1 vertex.1 +
      word (Sum.inr vertex)
noncomputable def rxCxH1_glueOffset
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S)) : Field :=
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  rxCxH1_glueDiscrepancy P A3 x S word
    (subdivisionOriginalBoundaryVertex P x S (A.xBoundaryRoot x))
noncomputable def rxCxH1_doubleCylinderPotential
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S)) :
    Word Field (DoubleCylinderVertex P x S) := fun vertex =>
  rxCxH1_subdivisionPotential P A3 x S word vertex.1 vertex.2 +
    rxTwoElim (motive := fun _ => Field) 0
      (rxCxH1_glueOffset P A3 x S word) vertex.1
noncomputable def rxCxH1_oldBoundaryDiscrepancy
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S)) :
    Word Field (XStarBoundaryVertex P x) := fun vertex =>
  rxCxH1_glueDiscrepancy P A3 x S word
    (subdivisionOriginalBoundaryVertex P x S vertex)
def rxXQDegreeZero (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (x : P.X)
    (hxq : P.xq x q = true) (S : OddScale) :
    Word Field (DoubleCylinderVertex P x S) →ₗ[Field]
      Word Field (QDoubleCylinderVertex P q S) :=
  wordPullback (qToXDoubleCylinderVertex P A q x hxq S)
def rxXQDegreeOne (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (x : P.X)
    (hxq : P.xq x q = true) (S : OddScale) :
    Word Field (DoubleCylinderEdge P x S) →ₗ[Field]
      Word Field (QDoubleCylinderEdge P q S) :=
  wordPullback (qToXDoubleCylinderEdge P A q x hxq S)
theorem rxXQ_commutes (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (x : P.X)
    (hxq : P.xq x q = true) (S : OddScale) :
    (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)).comp
        (rxXQDegreeZero P A q x hxq S) =
      (rxXQDegreeOne P A q x hxq S).comp
        (wordLinearMapTranspose (doubleCylinderBoundary1 P x S)) := by
  classical
  rw [← doubleCylinderGraphBoundary_eq_boundary1]
  simpa [doubleCylinderGraphBoundary, qDoubleCylinderBoundary1,
    rxXQDegreeZero, rxXQDegreeOne] using
    (wordPullback_graphCoboundary
      (qDoubleCylinderEdgeStart P q S)
      (qDoubleCylinderEdgeEnd P q S)
      (tannerDoubleCylinderEdgeStart P x S)
      (tannerDoubleCylinderEdgeEnd P x S)
      (qToXDoubleCylinderVertex P A q x hxq S)
      (qToXDoubleCylinderEdge P A q x hxq S)
      (fun edge => (qToXDoubleCylinderEdge_start P A q x hxq S edge).symm)
      (fun edge => (qToXDoubleCylinderEdge_end P A q x hxq S edge).symm))
noncomputable abbrev RXQH0 (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) :=
  Word Field (Fin 0) ⧸
    LinearMap.range (rxCq P q S).boundary1
noncomputable def rxCqH0Coordinate (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) : RXQH0 P q S →ₗ[Field] Word Field (Fin 0) := 0
noncomputable abbrev RXQH1 (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) := (rxCq P q S).middleCohomology
noncomputable def rxXQH0ToH1 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (x : P.X)
    (hxq : P.xq x q = true) (S : OddScale) :
    RXH0 P x S →ₗ[Field] RXQH1 P q S := by
  classical
  let cocycleMap : RXH0 P x S →ₗ[Field]
      (rxCq P q S).middleCocycleCode.carrier := {
    toFun := fun word => ⟨rxXQDegreeZero P A q x hxq S word.1, by
      rw [(rxCq P q S).mem_middleCocycleCode_iff]
      change wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
          (rxXQDegreeZero P A q x hxq S word.1) = 0
      have hcommutes := LinearMap.congr_fun
        (rxXQ_commutes P A q x hxq S) word.1
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at hcommutes
      rw [hcommutes]
      have hxzero :
          wordLinearMapTranspose (doubleCylinderBoundary1 P x S) word.1 = 0 := by
        exact word.2
      rw [hxzero]
      exact map_zero (rxXQDegreeOne P A q x hxq S)⟩
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  exact (rxCq P q S).middleCoboundaryInCocycles.mkQ.comp cocycleMap
def rxCqRootEvaluation (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) :
    (rxCq P q S).middleCocycleCode.carrier →ₗ[Field] Field where
  toFun := fun word => word.1 (0, Sum.inl (Sum.inl ()))
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
noncomputable def rxCqH1Coordinate (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) : RXQH1 P q S →ₗ[Field] Field :=
  (rxCq P q S).middleCoboundaryInCocycles.liftQ
    (rxCqRootEvaluation P q S)
    (by
      intro boundary hboundary
      change boundary.1 ∈
        (rxCq P q S).firstCoboundaryCheckCode.carrier at hboundary
      rcases ((rxCq P q S).mem_firstCoboundaryCheckCode_iff boundary.1).1
          hboundary with ⟨source, hsource⟩
      have hzero : wordLinearMapTranspose (rxCq P q S).boundary1 source = 0 := by
        simp [rxCq, wordLinearMapTranspose_zero]
      have hword : boundary.1 = 0 := by simpa [hzero] using hsource.symm
      change boundary ∈ LinearMap.ker (rxCqRootEvaluation P q S)
      rw [LinearMap.mem_ker]
      change boundary.1 (0, Sum.inl (Sum.inl ())) = 0
      simp [hword])
@[simp] theorem rxCqH1Coordinate_mk (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (word : (rxCq P q S).middleCocycleCode.carrier) :
    rxCqH1Coordinate P q S
        (Submodule.Quotient.mk word) =
      word.1 (0, Sum.inl (Sum.inl ())) := rfl
noncomputable abbrev RXZH0 (P : TannerSquarePresentation) (z : P.Z) :=
  Word Field (Fin 0) ⧸
    LinearMap.range (rxCz P z).boundary1
noncomputable def rxCzH0Coordinate (P : TannerSquarePresentation) (z : P.Z) :
    RXZH0 P z →ₗ[Field] Word Field (Fin 0) := 0
noncomputable abbrev RXZH1 (P : TannerSquarePresentation) (z : P.Z) :=
  (rxCz P z).middleCohomology
noncomputable def rxCzH1Coordinate (P : TannerSquarePresentation) (z : P.Z) :
    RXZH1 P z →ₗ[Field] Word Field (Fin 0) := 0
def rxQZDegreeOne (P : TannerSquarePresentation) (q : P.Q) (z : P.Z)
    (hqz : P.qz q z = true) (S : OddScale) :
    Word Field (QDoubleCylinderVertex P q S) →ₗ[Field] Word Field Two :=
  wordPullback (fun copy : Two =>
    (copy, Sum.inl (Sum.inr (⟨z, hqz⟩ : QStarEdge P q))))
noncomputable abbrev RXZH2 (P : TannerSquarePresentation) (z : P.Z) :=
  Word Field Two ⧸
    LinearMap.range (wordLinearMapTranspose (rxCz P z).boundary2)
def rxCzWordCoordinates : Word Field Two →ₗ[Field] Field × Field where
  toFun := fun word => (word 0, word 1)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
noncomputable def rxCzH2Coordinates (P : TannerSquarePresentation) (z : P.Z) :
    RXZH2 P z →ₗ[Field] Field × Field :=
  (LinearMap.range (wordLinearMapTranspose (rxCz P z).boundary2)).liftQ
    rxCzWordCoordinates
    (by
      intro boundary hboundary
      rcases hboundary with ⟨source, hsource⟩
      have hzero : wordLinearMapTranspose (rxCz P z).boundary2 source = 0 := by
        simp [rxCz, wordLinearMapTranspose_zero]
      change boundary ∈ LinearMap.ker rxCzWordCoordinates
      rw [LinearMap.mem_ker]
      have : boundary = 0 := by simpa [hzero] using hsource.symm
      simp [this, rxCzWordCoordinates])
@[simp] theorem rxCzH2Coordinates_mk (P : TannerSquarePresentation) (z : P.Z)
    (word : Word Field Two) :
    rxCzH2Coordinates P z
        ((LinearMap.range
          (wordLinearMapTranspose (rxCz P z).boundary2)).mkQ word) =
      (word 0, word 1) := rfl
noncomputable def rxQZH1ToH2 (P : TannerSquarePresentation)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    RXQH1 P q S →ₗ[Field] RXZH2 P z := by
  classical
  let targetQ := LinearMap.range
    (wordLinearMapTranspose (rxCz P z).boundary2)
  exact (rxCq P q S).middleCoboundaryInCocycles.liftQ
    (targetQ.mkQ.comp
      ((rxQZDegreeOne P q z hqz S).comp
        (rxCq P q S).middleCocycleCode.carrier.subtype)) (by
      intro boundary hboundary
      change boundary.1 ∈
        (rxCq P q S).firstCoboundaryCheckCode.carrier at hboundary
      rcases ((rxCq P q S).mem_firstCoboundaryCheckCode_iff boundary.1).1
          hboundary with ⟨source, hsource⟩
      have hzero :
          wordLinearMapTranspose (rxCq P q S).boundary1 source = 0 := by
        simp [rxCq, wordLinearMapTranspose_zero]
      have hword : boundary.1 = 0 := by
        simpa [hzero] using hsource.symm
      rw [LinearMap.mem_ker]
      simp [hword])
@[simp] theorem rxQZH1ToH2_mk (P : TannerSquarePresentation)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale)
    (word : (rxCq P q S).middleCocycleCode.carrier) :
    rxQZH1ToH2 P q z hqz S
        ((rxCq P q S).middleCoboundaryInCocycles.mkQ word) =
      (LinearMap.range
        (wordLinearMapTranspose (rxCz P z).boundary2)).mkQ
        (rxQZDegreeOne P q z hqz S word.1) := rfl
def rxAggregateDegreeZero (P : TannerSquarePresentation) (S : OddScale) :
    Word Field P.X →ₗ[Field] Word Field (RX0 P S) :=
  wordPullback Sigma.fst
def rxAggregateDegreeTwo (P : TannerSquarePresentation) (S : OddScale) :
    Word Field P.Z →ₗ[Field] Word Field (RX2 P S) where
  toFun := fun word coordinate => match coordinate with
    | Sum.inl _ => 0
    | Sum.inr zPoint => word zPoint.1
  map_add' := by intros; funext coordinate; rcases coordinate with _ | _ <;> rfl
  map_smul' := by intros; funext coordinate; rcases coordinate with _ | _ <;> rfl
@[simp] theorem rxAggregateDegreeTwo_xFace
    (P : TannerSquarePresentation) (S : OddScale) (word : Word Field P.Z)
    (xFace : Σ x : P.X, DoubleCylinderFace P x S) :
    rxAggregateDegreeTwo P S word (Sum.inl (Sum.inl xFace)) = 0 := rfl
@[simp] theorem rxAggregateDegreeTwo_qEdge
    (P : TannerSquarePresentation) (S : OddScale) (word : Word Field P.Z)
    (qEdge : Σ q : P.Q, QDoubleCylinderEdge P q S) :
    rxAggregateDegreeTwo P S word (Sum.inl (Sum.inr qEdge)) = 0 := rfl
@[simp] theorem rxAggregateDegreeTwo_zPoint
    (P : TannerSquarePresentation) (S : OddScale) (word : Word Field P.Z)
    (z : P.Z) (copy : Two) :
    rxAggregateDegreeTwo P S word (Sum.inr (z, copy)) = word z := rfl
noncomputable def rxAggregateXH0 (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) : Word Field P.X →ₗ[Field] RXH0 P x S := by
  classical
  exact {
    toFun := fun word => ⟨fun _ => word x, by
      change wordLinearMapTranspose (doubleCylinderBoundary1 P x S)
          (fun _ => word x) = 0
      rw [← doubleCylinderGraphBoundary_eq_boundary1]
      change wordLinearMapTranspose
        (graphBoundary (tannerDoubleCylinderEdgeStart P x S)
          (tannerDoubleCylinderEdgeEnd P x S)) (fun _ => word x) = 0
      ext edge
      rw [wordLinearMapTranspose_graphBoundary_apply]
      exact ZModModule.add_self (word x)⟩
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
@[simp] theorem rxCxH0Coordinate_rxAggregateXH0
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (word : Word Field P.X) :
    rxCxH0Coordinate P A x S (rxAggregateXH0 P x S word) = word x := rfl
noncomputable def rxXQAdjacency (P : TannerSquarePresentation) :
    Word Field P.X →ₗ[Field] Word Field P.Q :=
  wordLinearMapTranspose (Matrix.toLin' (xqIncidenceMatrix P))
noncomputable def rxAggregateQH1 (P : TannerSquarePresentation)
    (q : P.Q) (S : OddScale) : Word Field P.Q →ₗ[Field] RXQH1 P q S := by
  classical
  let cocycleMap : Word Field P.Q →ₗ[Field]
      (rxCq P q S).middleCocycleCode.carrier := {
    toFun := fun word => ⟨fun _ => word q, by
      rw [(rxCq P q S).mem_middleCocycleCode_iff]
      change wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
          (fun _ => word q) = 0
      unfold qDoubleCylinderBoundary1
      ext edge
      rw [wordLinearMapTranspose_graphBoundary_apply]
      exact ZModModule.add_self (word q)⟩
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  exact (rxCq P q S).middleCoboundaryInCocycles.mkQ.comp cocycleMap
@[simp] theorem rxCqH1Coordinate_rxAggregateQH1
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (word : Word Field P.Q) :
    rxCqH1Coordinate P q S (rxAggregateQH1 P q S word) = word q := rfl
noncomputable def rxQZAdjacency (P : TannerSquarePresentation) :
    Word Field P.Q →ₗ[Field] Word Field P.Z :=
  wordLinearMapTranspose (Matrix.toLin' (qzIncidenceMatrix P))
@[simp] theorem baseScaleFiveRX0_card :
    Fintype.card (RX0 baseTannerSquarePresentation scaleFive) = 60 := by
  decide +kernel
@[simp] theorem baseScaleFiveRX1_card :
    Fintype.card (RX1 baseTannerSquarePresentation scaleFive) = 140 := by
  decide +kernel
@[simp] theorem baseScaleFiveRX2_card :
    Fintype.card (RX2 baseTannerSquarePresentation scaleFive) = 82 := by
  decide +kernel
set_option maxRecDepth 10000 in
@[simp] theorem baseScaleFiveRXFace_card :
    Fintype.card (RXFace baseTannerSquarePresentation scaleFive) = 280 := by
  decide +kernel
open BDL26BoundedValence
noncomputable def rxOriginalBoundaryQNeighbour
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    (QStarEdge P q ⊕ Fin 3) → RX1 P S
  | Sum.inl e => Sum.inl ⟨x, qToXDoubleCylinderEdgeRaw P q x
      (rxOriginalXBoundaryQ_incidence P x q oldMember) S
      (Sum.inl (copy, e, rxRadialGridZero S))⟩
  | Sum.inr i => ![
      localFaceQAt P S (rxOriginalBoundaryQOwnerLocalFace P A4 S x copy q oldMember)
        (rxOriginalBoundaryQRootCorner P A4 x q oldMember),
      localFaceQAt P S (rxOriginalBoundaryQRootLocalFace P A4 S x copy q oldMember) 1,
      glueFaceQ1 P S (rxOriginalBoundaryQGlueFaceAt P S x copy q oldMember
        (rxOriginalBoundaryQRootQStarEdge P A4 x q oldMember))] i
noncomputable def rxOriginalBoundaryZNeighbour
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.z z) = true) :
    ((SharedQ P.data x z × Two) ⊕ Unit) → RX1 P S
  | Sum.inl (q, bit) =>
      let hxq : P.xq x q.1 = true := (show P.xq x q.1 = true ∧ P.qz q.1 z = true from by simpa using q.2).1
      let hqz : P.qz q.1 z = true := (show P.xq x q.1 = true ∧ P.qz q.1 z = true from by simpa using q.2).2
      let edge : QZEdge P := ⟨(q.1, z), hqz⟩
      let hm := rxOriginalBoundaryZGlueEdge_member P x q.1 hxq
        (⟨z, hqz⟩ : QStarEdge P q.1)
      if bit = 0 then localFaceQAt P S
        (rxOriginalBoundaryZRectangleLocalFaceAt P S x copy edge hm) 0
      else glueFaceQ1 P S
        (rxOriginalBoundaryZGlueFaceAt P A4 S x copy edge hm)
  | Sum.inr _ => localFaceQAt P S
      (rxOriginalBoundaryZRectangleLocalFaceAt P S x copy
        (rxOriginalBoundaryZRootOwner P A4 x z oldMember).1.edge
        (rxOriginalBoundaryZRootOwner P A4 x z oldMember).1.member) 1
abbrev RXRadialFaceCorner (P : TannerSquarePresentation) (x : P.X)
    (radial : XQEdge P) (member : xStarEdgeMember P x (Sum.inl radial) = true) :=
  {fc : XStarFace P x × Two //
    xStarFaceXQEdge P x fc.1 fc.2 = ⟨Sum.inl radial, member⟩}
noncomputable def rxRadialInteriorNeighbour
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (radial : XQEdge P) (member : xStarEdgeMember P x (Sum.inl radial) = true)
    (index : Fin (S.half - 1)) : (RXRadialFaceCorner P x radial member ⊕ Two) → RX1 P S
  | Sum.inl fc => localFaceQAt P S
      (rxStarEdgeInteriorBeforeLocalFaceAt P S x copy ⟨Sum.inl radial, member⟩
        index fc.1.1 fc.1.2)
      (rxStarEdgeInteriorAcrossCornerAt ⟨Sum.inl radial, member⟩ fc.1.2)
  | Sum.inr bit => Sum.inl ⟨x, Sum.inl (copy, Sum.inl
      (⟨Sum.inl radial, member⟩, if bit = 0 then rxStarEdgeInteriorPreviousIndex S index
        else rxStarEdgeInteriorNextIndex S index))⟩
noncomputable def rxLocalCellBoundaryEdge (P : TannerSquarePresentation)
    (S : OddScale) (x : P.X) (cell : DoubleCylinderFace P x S)
    (slot : Fin 2 × Fin 2) : RX1 P S :=
  Sum.inl ⟨x, match cell with
    | Sum.inl cf => Sum.inl (cf.1, subdivisionFaceBoundaryEdge P x S cf.2 slot)
    | Sum.inr rectangle => doubleCylinderRectangleBoundaryEdge P x S rectangle slot⟩
noncomputable def rxQEdgeNeighbour (P : TannerSquarePresentation) (S : OddScale)
    (q : P.Q) (edge : QDoubleCylinderEdge P q S) :
    ({x : P.X // P.xq x q = true} ⊕ Fin 2) → RX1 P S
  | Sum.inl x => Sum.inl ⟨x.1, qToXDoubleCylinderEdgeRaw P q x.1 x.2 S edge⟩
  | Sum.inr endpoint => Sum.inr ⟨q, BDL26RXLocalReplacement.edgeEndpoint
      (qDoubleCylinderEdgeStart P q S) (qDoubleCylinderEdgeEnd P q S) edge endpoint⟩
abbrev RXBoundaryFaceCorner (P : TannerSquarePresentation) (x : P.X)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true) :=
  {fc : XStarFace P x × Fin 2 //
    xStarFaceQZEdge P x fc.1 fc.2 = ⟨Sum.inr edge, member⟩}
noncomputable def rxBoundaryInteriorNeighbour
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Fin 2) (edge : QZEdge P)
    (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) : (RXBoundaryFaceCorner P x edge member ⊕ Fin 4) → RX1 P S
  | Sum.inl fc => localFaceQAt P S
      (rxStarEdgeInteriorBeforeLocalFaceAt P S x copy ⟨Sum.inr edge, member⟩
        index fc.1.1 fc.1.2)
      (rxStarEdgeInteriorAcrossCornerAt ⟨Sum.inr edge, member⟩ fc.1.2)
  | Sum.inr tag => if tag = 0 then
      Sum.inl ⟨x, Sum.inl (copy, Sum.inl
        (⟨Sum.inr edge, member⟩, rxStarEdgeInteriorPreviousIndex S index))⟩
    else if tag = 1 then
      Sum.inl ⟨x, Sum.inl (copy, Sum.inl
        (⟨Sum.inr edge, member⟩, rxStarEdgeInteriorNextIndex S index))⟩
    else if tag = 2 then localFaceQAt P S
      (rxStarEdgeInteriorRectangleBeforeLocalFace P S x copy edge member index) 1
    else glueFaceQ1 P S
      (rxStarEdgeInteriorGlueBefore P A4 S x copy edge member index)
noncomputable def rxVerticalOldZZNeighbour
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (z : P.Z) :
    (SharedQ P.data x z × Two) → RX2 P S := fun ⟨q, bit⟩ =>
  let h : P.xq x q.1 = true ∧ P.qz q.1 z = true := by simpa using q.2
  let e : QStarEdge P q.1 := ⟨z, h.2⟩
  if bit = 0 then
    Sum.inl (Sum.inl ⟨x, Sum.inr
      (qToXSubdivisionBoundaryEdge P q.1 x h.1 S
        (e, ⟨S.half - 1, by have := S.half_pos; omega⟩))⟩)
  else Sum.inl (Sum.inr ⟨q.1, Sum.inr e⟩)
def rxRadialCellAt (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (f : XStarFace P x) (corner : Two) (k : Fin S.half) :
    SubdivisionFace P x S :=
  if corner = 0 then (f, k, ⟨0, S.half_pos⟩) else (f, ⟨0, S.half_pos⟩, k)
def rxBoundaryCellAt (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (f : XStarFace P x) (corner : Two) (k : Fin S.half) :
    SubdivisionFace P x S :=
  if corner = 0 then (f, rxStarEdgeInteriorLastIndex S, k)
  else (f, k, rxStarEdgeInteriorLastIndex S)
end BDL26RXLocalReplacement
end Coding
end QEC


