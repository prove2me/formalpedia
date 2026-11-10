-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
-- name    : QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T00:19:08.937975+00:00
-- url     : https://prove2.me/theorems/504db70a-8c78-4ada-8135-b0e2a8751ac9
-- title:
--   XLocal Weight
-- statement:
--   Definitions and structural lemmas for XLocal Weight, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalGridParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_TannerSquarePresentation_faceQ_injective
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
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
attribute [local simp] QEC.Coding.BDL26XLocalConnectingWeight.copiedQ_image_copy
attribute [local simp] QEC.Coding.BDL26XLocalConnectingWeight.copiedQ_image_vertical
attribute [local simp] QEC.Coding.BDL26XLocalConnectingWeight.verticalZ_image_copy
attribute [local simp] QEC.Coding.BDL26XLocalConnectingWeight.verticalZ_image_vertical
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
namespace QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26XLocalGridParity BDL26XLocalWeightParity
open BDL26XLocalConnectingWeight
open scoped BigOperators Classical
theorem xLocal_boundary_side_injective
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P) (x : P.X) :
    Function.Injective (fun p : XStarFace P x × Two =>
      xStarFaceBoundaryEdge P x p.1 p.2) := by
  rintro ⟨f, s⟩ ⟨g, t⟩ h
  have he : faceQZEdge P f.val s = faceQZEdge P g.val t := by
    exact Sum.inr.inj (congrArg Subtype.val h)
  have hq := congrArg (fun e : QZEdge P => e.val.1) he
  have hz := congrArg (fun e : QZEdge P => e.val.2) he
  have hfx : P.faceX f.val = x := by simpa [xStarFaceMember] using f.property
  have hgx : P.faceX g.val = x := by simpa [xStarFaceMember] using g.property
  have hfg : f = g := Subtype.ext (R.faceXZ_injective (Prod.ext (hfx.trans hgx.symm) hz))
  subst g
  have hst : s = t := P.faceQ_injective f.val hq
  subst t
  rfl
theorem xLocal_boundary_side_surjective
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P) (x : P.X) :
    Function.Surjective (fun p : XStarFace P x × Two =>
      xStarFaceBoundaryEdge P x p.1 p.2) := by
  rintro ⟨edge, hedge⟩
  rcases edge with radial | boundary
  · simp [xStarBoundaryEdgeMember] at hedge
  · let member := xStarBoundaryEdgeMember_to_star P x (Sum.inr boundary) hedge
    let owner := A4.xBoundaryFaceOwner x boundary member
    refine ⟨owner.val, ?_⟩
    apply Subtype.ext
    exact congrArg (fun e : XStarEdge P x => e.val) owner.property
noncomputable def xLocalBoundarySideEquiv
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (x : P.X) :
    (XStarFace P x × Two) ≃ XStarBoundaryEdge P x :=
  Equiv.ofBijective (fun p => xStarFaceBoundaryEdge P x p.1 p.2)
    ⟨xLocal_boundary_side_injective P R x, xLocal_boundary_side_surjective P A4 x⟩
theorem xLocal_boundary_segment_bijective
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Function.Bijective (fun p : XStarBoundaryEdge P x × Fin S.half =>
      subdivisionOriginalBoundaryEdge P x S p.1 p.2) := by
  constructor
  · rintro ⟨e, i⟩ ⟨f, j⟩ h
    have hp : (xStarBoundaryEdgeToStar P x e, i) =
        (xStarBoundaryEdgeToStar P x f, j) :=
      Sum.inl.inj (congrArg Subtype.val h)
    have hij := congrArg Prod.snd hp
    have hef : e = f := Subtype.ext
      (congrArg (fun e : XStarEdge P x => e.val) (congrArg Prod.fst hp))
    exact Prod.ext hef hij
  · rintro ⟨edge, hedge⟩
    rcases edge with original | interior
    · rcases original with ⟨edge, i⟩
      exact ⟨(⟨edge.val, hedge⟩, i), rfl⟩
    · simp [subdivisionBoundaryEdgeMember] at hedge
noncomputable def xLocalBoundarySegmentEquiv
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    (XStarBoundaryEdge P x × Fin S.half) ≃ SubdivisionBoundaryEdge P x S :=
  Equiv.ofBijective (fun p => subdivisionOriginalBoundaryEdge P x S p.1 p.2)
    (xLocal_boundary_segment_bijective P x S)
abbrev XLocalPieceCell (S : OddScale) :=
  (Two × GridVertex S.half) ⊕ (Two × StripVertex S.half)
def xLocalPieceCellMap (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    XStarFace P x × XLocalPieceCell S → DoubleCylinderFace P x S
  | (face, Sum.inl (copy, i, j)) => Sum.inl (copy, face, i, j)
  | (face, Sum.inr (side, i)) => Sum.inr
      (subdivisionOriginalBoundaryEdge P x S
        (xStarFaceBoundaryEdge P x face side) i)
theorem xLocalPieceCellMap_injective
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (x : P.X) (S : OddScale) : Function.Injective (xLocalPieceCellMap P x S) := by
  rintro ⟨f, a | a⟩ ⟨g, b | b⟩ h
  · rcases a with ⟨c, i, j⟩
    rcases b with ⟨d, k, l⟩
    have hc := Sum.inl.inj h
    cases hc
    rfl
  · cases h
  · cases h
  · rcases a with ⟨s, i⟩
    rcases b with ⟨t, j⟩
    change Sum.inr (subdivisionOriginalBoundaryEdge P x S (xStarFaceBoundaryEdge P x f s) i) =
      Sum.inr (subdivisionOriginalBoundaryEdge P x S (xStarFaceBoundaryEdge P x g t) j) at h
    have he : subdivisionOriginalBoundaryEdge P x S (xStarFaceBoundaryEdge P x f s) i =
        subdivisionOriginalBoundaryEdge P x S (xStarFaceBoundaryEdge P x g t) j := Sum.inr.inj h
    have hp : (xStarFaceBoundaryEdge P x f s, i) =
        (xStarFaceBoundaryEdge P x g t, j) :=
      (xLocal_boundary_segment_bijective P x S).1 he
    have hij := congrArg Prod.snd hp
    have hfs : (f, s) = (g, t) :=
      xLocal_boundary_side_injective P R x (congrArg Prod.fst hp)
    cases hfs
    cases hij
    rfl
theorem xLocalPieceCellMap_surjective
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (x : P.X) (S : OddScale) : Function.Surjective (xLocalPieceCellMap P x S) := by
  rintro (⟨copy, face, i, j⟩ | edge)
  · exact ⟨(face, Sum.inl (copy, i, j)), rfl⟩
  · obtain ⟨⟨boundary, i⟩, hi⟩ := (xLocal_boundary_segment_bijective P x S).2 edge
    obtain ⟨⟨face, side⟩, hside⟩ := xLocal_boundary_side_surjective P A4 x boundary
    subst boundary
    exact ⟨(face, Sum.inr (side, i)), congrArg Sum.inr hi⟩
noncomputable def xLocalPieceCellEquiv
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale) :
    (XStarFace P x × XLocalPieceCell S) ≃ DoubleCylinderFace P x S :=
  Equiv.ofBijective (xLocalPieceCellMap P x S)
    ⟨xLocalPieceCellMap_injective P R x S, xLocalPieceCellMap_surjective P A4 x S⟩
@[simp] theorem xLocalPieceCellEquiv_apply
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (p : XStarFace P x × XLocalPieceCell S) :
    xLocalPieceCellEquiv P A4 R x S p = xLocalPieceCellMap P x S p := rfl
def xLocalLayerWord (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (syndrome : Word Field (DoubleCylinderFace P x S))
    (face : XStarFace P x) (copy : Two) : Word Field (GridVertex S.half) :=
  fun ij => syndrome (Sum.inl (copy, face, ij))
def xLocalStripWord (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (syndrome : Word Field (DoubleCylinderFace P x S))
    (face : XStarFace P x) (side : Two) : Word Field (StripVertex S.half) :=
  fun i => syndrome (Sum.inr (subdivisionOriginalBoundaryEdge P x S
    (xStarFaceBoundaryEdge P x face side) i))
def xLocalRegionParity (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (syndrome : Word Field (DoubleCylinderFace P x S))
    (face : XStarFace P x) : Two ⊕ Two → Field
  | Sum.inl copy => totalParity (xLocalLayerWord P x S syndrome face copy)
  | Sum.inr side => totalParity (xLocalStripWord P x S syndrome face side)
def xLocalGridDualEdge (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (copy : Two) : GridEdge S.half → DoubleCylinderEdge P x S
  | Sum.inl (i, j) => Sum.inl (copy, Sum.inr (Sum.inr (face, i, j)))
  | Sum.inr (i, j) => Sum.inl (copy, Sum.inr (Sum.inl (face, i, j)))
def xLocalStripDualEdge (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (side : Two) (i : StripEdge S.half) :
    DoubleCylinderEdge P x S :=
  Sum.inr ⟨Sum.inr (Sum.inl
    (xStarBoundaryEdgeToStar P x (xStarFaceBoundaryEdge P x face side), i)), by
      change xStarBoundaryEdgeMember P x (xStarFaceBoundaryEdge P x face side).val = true
      exact (xStarFaceBoundaryEdge P x face side).property⟩
noncomputable def xLocalWordPush
    {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (embed : I → J) : Word Field I →ₗ[Field] Word Field J where
  toFun := fun f => ∑ i, Pi.single (embed i) (f i)
  map_add' := by
    intro f g
    simp [Pi.add_apply, Pi.single_add, Finset.sum_add_distrib]
  map_smul' := by
    intro a f
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply funext
    intro j
    by_cases hj : j = embed i <;> simp [Pi.single_apply, hj, smul_eq_mul]
def xLocalBoundaryInteriorVertex (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (e : XStarBoundaryEdge P x) (i : Fin (S.half - 1)) :
    SubdivisionBoundaryVertex P x S :=
  ⟨Sum.inr (Sum.inl (xStarBoundaryEdgeToStar P x e, i)), e.property⟩
def xLocalLast (S : OddScale) : Fin S.half := ⟨S.half - 1, by have := S.half_pos; omega⟩
def xLocalGridRoot (S : OddScale) : GridVertex S.half := (xLocalLast S, xLocalLast S)
def xLocalRegionRoot (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) : Two ⊕ Two → DoubleCylinderFace P x S
  | Sum.inl copy => Sum.inl (copy, face, xLocalGridRoot S)
  | Sum.inr side => Sum.inr (subdivisionOriginalBoundaryEdge P x S
      (xStarFaceBoundaryEdge P x face side) (xLocalLast S))
def xLocalLayerStripConnector (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (copy side : Two) : DoubleCylinderEdge P x S :=
  Sum.inl (copy, (subdivisionOriginalBoundaryEdge P x S
    (xStarFaceBoundaryEdge P x face side) (xLocalLast S)).val)
def xLocalStripStripConnector (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) : DoubleCylinderEdge P x S :=
  Sum.inr (subdivisionOriginalBoundaryVertex P x S
    (xBoundaryEdgeEnd P x (xStarFaceBoundaryEdge P x face 0)))
noncomputable def xLocalRootCorrection
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (a b l r : Field) : Word Field (DoubleCylinderEdge P x S) :=
  let c := pieceCrossingCoefficients a b l r
  Pi.single (xLocalLayerStripConnector P x S face 0 0) (c 0) +
    Pi.single (xLocalLayerStripConnector P x S face 0 1) (c 1) +
    Pi.single (xLocalLayerStripConnector P x S face 1 0) (c 2) +
    Pi.single (xLocalLayerStripConnector P x S face 1 1) (c 3) +
    Pi.single (xLocalStripStripConnector P x S face) (c 4)
def xLocalPieceWord (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (syndrome : Word Field (DoubleCylinderFace P x S)) :
    Word Field (XLocalPieceCell S) := fun cell => syndrome (xLocalPieceCellMap P x S (face, cell))
end QEC.Coding.BDL26RXLocalReplacement


