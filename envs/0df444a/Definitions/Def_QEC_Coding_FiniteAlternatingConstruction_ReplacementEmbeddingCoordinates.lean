-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
-- name    : QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T01:48:28.823769+00:00
-- url     : https://prove2.me/theorems/c78019b0-7697-4985-ab99-73b518b9bae7
-- title:
--   Replacement Embedding Coordinates
-- statement:
--   Definitions and structural lemmas for Replacement Embedding Coordinates, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_correctionRegion_mem
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_syndromeRegion_mem
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_OddScale_two_half_add_one
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_faceCornerBoundaryEdge_surjective
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_faceCornerWedge_bijective
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzFace_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzQ_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzX_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzZ_card
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
attribute [local simp] QEC.Coding.BDL26DecodingGraph.correctionRegion_mem
attribute [local simp] QEC.Coding.BDL26DecodingGraph.syndromeRegion_mem
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
namespace QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
theorem faceCornerBoundaryEdge_injective (P : TannerSquarePresentation) :
    Function.Injective (faceCornerBoundaryEdge P) := by
  intro a b h
  apply (faceCornerWedge_bijective P).1
  apply Subtype.ext
  have hx : P.faceX a.1 = P.faceX b.1 := congrArg Sigma.fst h
  have he : faceQZEdge P a.1 a.2 = faceQZEdge P b.1 b.2 := by
    have hv := congrArg
      (fun e : Σ x : P.X, XStarBoundaryEdge P x => e.2.1) h
    exact Sum.inr.inj hv
  exact Prod.ext hx (congrArg Subtype.val he)
noncomputable def faceCornerBoundaryEquiv (P : TannerSquarePresentation) :
    P.Face × BDL26FiniteTannerSquare.Two ≃ Σ x : P.X, XStarBoundaryEdge P x :=
  Equiv.ofBijective (faceCornerBoundaryEdge P)
    ⟨faceCornerBoundaryEdge_injective P, faceCornerBoundaryEdge_surjective P⟩
abbrev PatchCorner := BDL26FiniteTannerSquare.Two × BDL26FiniteTannerSquare.Two
abbrev PlaneSlot (S : OddScale) :=
  (BDL26FiniteTannerSquare.Two × (Fin S.half × Fin S.half)) × PatchCorner
abbrev BoundarySlot (S : OddScale) :=
  BDL26FiniteTannerSquare.Two × (Fin S.half × PatchCorner)
abbrev QEdgeSlot (S : OddScale) :=
  (BDL26FiniteTannerSquare.Two × Fin S.half) ⊕ Fin 1
abbrev GlueSlot (S : OddScale) :=
  BDL26FiniteTannerSquare.Two × (QEdgeSlot S × BDL26FiniteTannerSquare.Two)
abbrev PatchSlot (S : OddScale) :=
  (PlaneSlot S ⊕ BoundarySlot S) ⊕ (GlueSlot S ⊕ BDL26FiniteTannerSquare.Two)
def planarLocalCoordinates (P : TannerSquarePresentation) (S : OddScale) :
    (Σ x : P.X,
      (BDL26FiniteTannerSquare.Two × SubdivisionFace P x S) × PatchCorner) ≃
      P.Face × PlaneSlot S where
  toFun c := (c.2.1.2.1.1, ((c.2.1.1, c.2.1.2.2), c.2.2))
  invFun c := ⟨P.faceX c.1,
    (c.2.1.1, (oldFaceInXStar P c.1, c.2.1.2)), c.2.2⟩
  left_inv := by
    rintro ⟨x, ⟨copy, ⟨⟨f, hf⟩, i, j⟩⟩, corner⟩
    have hx : P.faceX f = x := by simpa [xStarFaceMember] using hf
    subst x
    rfl
  right_inv := fun _ => rfl
noncomputable def boundarySegmentCoordinates (P : TannerSquarePresentation) (S : OddScale) :
    (Σ x : P.X, SubdivisionBoundaryEdge P x S) ≃
      (P.Face × BDL26FiniteTannerSquare.Two) × Fin S.half :=
  (Equiv.sigmaCongrRight fun x => subdivisionBoundaryEdgeEquiv P x S).trans
    ((Equiv.sigmaProdDistrib (fun x => XStarBoundaryEdge P x) (Fin S.half)).symm.trans
      (Equiv.prodCongr (faceCornerBoundaryEquiv P).symm (Equiv.refl _)))
def boundarySlotReassociate (P : TannerSquarePresentation) (S : OddScale) :
    ((P.Face × BDL26FiniteTannerSquare.Two) × Fin S.half) × PatchCorner ≃
      P.Face × BoundarySlot S where
  toFun c := (c.1.1.1, c.1.1.2, c.1.2, c.2)
  invFun c := (((c.1, c.2.1), c.2.2.1), c.2.2.2)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
noncomputable def rectangleLocalCoordinates
    (P : TannerSquarePresentation) (S : OddScale) :
    (Σ x : P.X, SubdivisionBoundaryEdge P x S × PatchCorner) ≃
      P.Face × BoundarySlot S :=
  (Equiv.sigmaProdDistrib (fun x => SubdivisionBoundaryEdge P x S) PatchCorner).symm.trans
    ((Equiv.prodCongr (boundarySegmentCoordinates P S) (Equiv.refl _)).trans
      (boundarySlotReassociate P S))
noncomputable def rxLocalFaceCoordinates (P : TannerSquarePresentation) (S : OddScale) :
    RXLocalFace P S ≃ P.Face × (PlaneSlot S ⊕ BoundarySlot S) :=
  (Equiv.sigmaCongrRight fun x =>
    Equiv.sumProdDistrib (BDL26FiniteTannerSquare.Two × SubdivisionFace P x S)
      (SubdivisionBoundaryEdge P x S) PatchCorner).trans
    ((Equiv.sigmaSumDistrib
      (fun x => (BDL26FiniteTannerSquare.Two × SubdivisionFace P x S) × PatchCorner)
      (fun x => SubdivisionBoundaryEdge P x S × PatchCorner)).trans
      ((Equiv.sumCongr (planarLocalCoordinates P S) (rectangleLocalCoordinates P S)).trans
        (Equiv.prodSumDistrib P.Face (PlaneSlot S) (BoundarySlot S)).symm))
def qDoubleCylinderEdgeCoordinates (P : TannerSquarePresentation) (q : P.Q) (S : OddScale) :
    QDoubleCylinderEdge P q S ≃ QStarEdge P q × QEdgeSlot S where
  toFun
    | .inl (copy, edge, i) => (edge, .inl (copy, i))
    | .inr edge => (edge, .inr 0)
  invFun
    | (edge, .inl (copy, i)) => .inl (copy, edge, i)
    | (edge, .inr _) => .inr edge
  left_inv := by rintro (⟨copy, edge, i⟩ | edge) <;> rfl
  right_inv := by
    rintro ⟨edge, c | c⟩
    · rfl
    · have hc : c = 0 := Subsingleton.elim _ _
      subst c
      rfl
def qGlueFiberReassociate (P : TannerSquarePresentation) (a : XQEdge P) (S : OddScale) :
    QDoubleCylinderEdge P a.1.2 S × BDL26FiniteTannerSquare.Two ≃
      QStarEdge P a.1.2 × (QEdgeSlot S × BDL26FiniteTannerSquare.Two) :=
  (Equiv.prodCongr (qDoubleCylinderEdgeCoordinates P a.1.2 S) (Equiv.refl _)).trans
    (Equiv.prodAssoc _ _ _)
noncomputable def rxGlueFaceCoordinates (P : TannerSquarePresentation) (S : OddScale) :
    RXXQGlueFace P S ≃ P.Face × GlueSlot S :=
  (Equiv.sigmaCongrRight fun a => qGlueFiberReassociate P a S).trans
    ((Equiv.sigmaProdDistrib (fun a : XQEdge P => QStarEdge P a.1.2)
      (QEdgeSlot S × BDL26FiniteTannerSquare.Two)).symm.trans
      ((Equiv.prodCongr
        ((xqQStarEdgeEquiv P).trans
          (Equiv.ofBijective (faceCornerWedge P) (faceCornerWedge_bijective P)).symm)
        (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _)))
noncomputable def rxFaceSlotEquiv (P : TannerSquarePresentation) (S : OddScale) :
    RXFace P S ≃ P.Face × PatchSlot S :=
  (Equiv.sumCongr (rxLocalFaceCoordinates P S)
    ((Equiv.sumCongr (rxGlueFaceCoordinates P S) (Equiv.refl _)).trans
      (Equiv.prodSumDistrib P.Face (GlueSlot S) BDL26FiniteTannerSquare.Two).symm)).trans
    (Equiv.prodSumDistrib P.Face (PlaneSlot S ⊕ BoundarySlot S)
      (GlueSlot S ⊕ BDL26FiniteTannerSquare.Two)).symm
abbrev FineCoordinate (S : OddScale) :=
  (Fin S.half × BDL26FiniteTannerSquare.Two) ⊕ Fin 1
def castFinEquiv {n m : Nat} (h : n = m) : Fin n ≃ Fin m where
  toFun := Fin.cast h
  invFun := Fin.cast h.symm
  left_inv := by intro i; apply Fin.ext; rfl
  right_inv := by intro i; apply Fin.ext; rfl
def fineCoordinateEquiv (S : OddScale) : FineCoordinate S ≃ Fin S.ell :=
  (Equiv.sumCongr (finProdFinEquiv :
    Fin S.half × BDL26FiniteTannerSquare.Two ≃ Fin (S.half * 2))
    (Equiv.refl (Fin 1))).trans
    (finSumFinEquiv.trans (castFinEquiv (by have := S.two_half_add_one; omega)))
@[simp] theorem fineCoordinate_interior_val (S : OddScale)
    (i : Fin S.half) (bit : BDL26FiniteTannerSquare.Two) :
    (fineCoordinateEquiv S (.inl (i, bit))).val = 2 * i.val + bit.val := by
  simp [fineCoordinateEquiv, castFinEquiv, finProdFinEquiv, finSumFinEquiv, Nat.add_comm]
@[simp] theorem fineCoordinate_last (S : OddScale) (i : Fin 1) :
    fineCoordinateEquiv S (.inr i) = lastStrip S := by
  apply Fin.ext
  have hi : i.val = 0 := by omega
  have hodd := S.two_half_add_one
  simp [fineCoordinateEquiv, castFinEquiv, finSumFinEquiv, lastStrip, hi]
  omega
abbrev RawPositiveCell (S : OddScale) :=
  BDL26FiniteTannerSquare.Two × (FineCoordinate S × FineCoordinate S)
abbrev RawSeamCell (S : OddScale) := BDL26FiniteTannerSquare.Two × FineCoordinate S
abbrev RawFlatCell (S : OddScale) :=
  RawPositiveCell S ⊕ (RawSeamCell S ⊕ RawSeamCell S)
def patchSlotToRawFlat (S : OddScale) : PatchSlot S → RawFlatCell S
  | .inl (.inl ((copy, i, j), a, b)) => .inl (copy, .inl (i, a), .inl (j, b))
  | .inl (.inr (side, i, copy, endpoint)) =>
      if side = 0 then .inr (.inr (copy, .inl (i, endpoint)))
      else .inr (.inl (copy, .inl (i, endpoint)))
  | .inr (.inl (side, .inl (copy, i), endpoint)) =>
      if side = 0 then .inl (copy, .inr 0, .inl (i, endpoint))
      else .inl (copy, .inl (i, endpoint), .inr 0)
  | .inr (.inl (side, .inr _, copy)) =>
      if side = 0 then .inr (.inl (copy, .inr 0))
      else .inr (.inr (copy, .inr 0))
  | .inr (.inr copy) => .inl (copy, .inr 0, .inr 0)
def rawFlatToPatchSlot (S : OddScale) : RawFlatCell S → PatchSlot S
  | .inl (copy, .inl (i, a), .inl (j, b)) => .inl (.inl ((copy, i, j), a, b))
  | .inl (copy, .inr _, .inl (i, endpoint)) =>
      .inr (.inl (0, .inl (copy, i), endpoint))
  | .inl (copy, .inl (i, endpoint), .inr _) =>
      .inr (.inl (1, .inl (copy, i), endpoint))
  | .inl (copy, .inr _, .inr _) => .inr (.inr copy)
  | .inr (.inl (copy, .inl (i, endpoint))) => .inl (.inr (1, i, copy, endpoint))
  | .inr (.inr (copy, .inl (i, endpoint))) => .inl (.inr (0, i, copy, endpoint))
  | .inr (.inl (copy, .inr _)) => .inr (.inl (0, .inr 0, copy))
  | .inr (.inr (copy, .inr _)) => .inr (.inl (1, .inr 0, copy))
def patchSlotRawFlatEquiv (S : OddScale) : PatchSlot S ≃ RawFlatCell S where
  toFun := patchSlotToRawFlat S
  invFun := rawFlatToPatchSlot S
  left_inv := by
    intro c
    rcases c with c | c
    · rcases c with c | ⟨side, i, copy, endpoint⟩
      · rcases c with ⟨⟨copy, i, j⟩, a, b⟩
        rfl
      · fin_cases side <;> simp [patchSlotToRawFlat, rawFlatToPatchSlot]
    · rcases c with ⟨side, edge, endpoint⟩ | copy
      · rcases edge with ⟨copy, i⟩ | last
        · fin_cases side <;> simp [patchSlotToRawFlat, rawFlatToPatchSlot]
        · have hlast : last = 0 := Subsingleton.elim _ _
          subst last
          fin_cases side <;> simp [patchSlotToRawFlat, rawFlatToPatchSlot]
      · rfl
  right_inv := by
    intro c
    rcases c with ⟨copy, i, j⟩ | c
    · rcases i with ⟨i, a⟩ | i <;> rcases j with ⟨j, b⟩ | j
      · rfl
      · have h : j = 0 := Subsingleton.elim _ _
        subst j
        rfl
      · have h : i = 0 := Subsingleton.elim _ _
        subst i
        rfl
      · have hi : i = 0 := Subsingleton.elim _ _
        have hj : j = 0 := Subsingleton.elim _ _
        subst i
        subst j
        rfl
    · rcases c with ⟨copy, c⟩ | ⟨copy, c⟩ <;> rcases c with ⟨i, endpoint⟩ | last
      · rfl
      · have h : last = 0 := Subsingleton.elim _ _
        subst last
        rfl
      · rfl
      · have h : last = 0 := Subsingleton.elim _ _
        subst last
        rfl
def rawFlatCellEquiv (S : OddScale) : RawFlatCell S ≃ FlatCell S :=
  Equiv.sumCongr
    (Equiv.prodCongr (Equiv.refl _)
      (Equiv.prodCongr (fineCoordinateEquiv S) (fineCoordinateEquiv S)))
    (Equiv.sumCongr
      (Equiv.prodCongr (Equiv.refl _) (fineCoordinateEquiv S))
      (Equiv.prodCongr (Equiv.refl _) (fineCoordinateEquiv S)))
noncomputable def rxFaceFlatEquiv (P : TannerSquarePresentation) (S : OddScale) :
    RXFace P S ≃ P.Face × FlatCell S :=
  (rxFaceSlotEquiv P S).trans
    (Equiv.prodCongr (Equiv.refl _)
      ((patchSlotRawFlatEquiv S).trans (rawFlatCellEquiv S)))
noncomputable def rzFaceFlatEquiv (P : TannerSquarePresentation) (S : OddScale) :
    BDL26RZLocalReplacement.RZFace P S ≃ P.Face × FlatCell S :=
  (rzFaceEquiv P S).trans (rxFaceFlatEquiv (transposePresentation P) S)
noncomputable section PointMaps
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
def foldedSquare (x q₀ q₁ z : E) (u v : ℝ) : E :=
  if v ≤ u then (1 - u) • x + (u - v) • q₀ + v • z
  else (1 - v) • x + (v - u) • q₁ + u • z
def facePoint (P : TannerSquarePresentation) (J : Vertex P → E)
    (f : P.Face) (u v : ℝ) : E :=
  foldedSquare (J (.x (P.faceX f))) (J (.q (P.faceQ f 0)))
    (J (.q (P.faceQ f 1))) (J (.z (P.faceZ f))) u v
def faceGrid (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) : GridMap S E :=
  fun i j => facePoint P J f ((i.val : ℝ) / S.ell) ((j.val : ℝ) / S.ell)
def contractionRatio (S : OddScale) : ℝ := (2 * (S.half : ℝ)) / S.ell
def starVertexPoint (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (v : XStarVertex P x) : E :=
  (1 - contractionRatio S) • J (.x x) + contractionRatio S • J v.1
def subdivisionVertexPoint (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) : SubdivisionVertex P x S → E
  | .inl v => starVertexPoint P S J x v
  | .inr (.inl (edge, i)) =>
      let t : ℝ := ((i.val : ℝ) + 1) / S.half
      (1 - t) • starVertexPoint P S J x (xStarEdgeStart P x edge) +
        t • starVertexPoint P S J x (xStarEdgeEnd P x edge)
  | .inr (.inr (f, i, j)) =>
      facePoint P J f.1 (2 * ((i.val : ℝ) + 1) / S.ell)
        (2 * ((j.val : ℝ) + 1) / S.ell)
def rxZeroPoint (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (v : RX0 P S) : E :=
  subdivisionVertexPoint P S J v.1 v.2.2
def qSubdivisionVertexPoint (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (q : P.Q) : QSubdivisionVertex P q S → E
  | .inl (.inl _) => J (.q q)
  | .inl (.inr edge) =>
      (1 - contractionRatio S) • J (.q q) + contractionRatio S • J (.z edge.1)
  | .inr (edge, i) =>
      let t : ℝ := 2 * ((i.val : ℝ) + 1) / S.ell
      (1 - t) • J (.q q) + t • J (.z edge.1)
def rxOnePoint (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) : RX1 P S → E
  | .inl ⟨x, edge⟩ =>
      (1 / 2 : ℝ) • (subdivisionVertexPoint P S J x
        (tannerDoubleCylinderEdgeStart P x S edge).2 +
        subdivisionVertexPoint P S J x (tannerDoubleCylinderEdgeEnd P x S edge).2)
  | .inr ⟨q, _, vertex⟩ => qSubdivisionVertexPoint P S J q vertex
def rxTwoPoint (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) : RX2 P S → E
  | .inl (.inl ⟨_, .inl (_, f, i, j)⟩) =>
      facePoint P J f.1 ((2 * (i.val : ℝ) + 1) / S.ell)
        ((2 * (j.val : ℝ) + 1) / S.ell)
  | .inl (.inl ⟨x, .inr edge⟩) =>
      (1 / 2 : ℝ) • (subdivisionVertexPoint P S J x
        (subdivisionEdgeStart P x S edge.1) +
        subdivisionVertexPoint P S J x (subdivisionEdgeEnd P x S edge.1))
  | .inl (.inr ⟨q, edge⟩) =>
      (1 / 2 : ℝ) • (qSubdivisionVertexPoint P S J q
        (qDoubleCylinderEdgeStart P q S edge).2 +
        qSubdivisionVertexPoint P S J q (qDoubleCylinderEdgeEnd P q S edge).2)
  | .inr (z, _) => J (.z z)
noncomputable def rxFaceImage (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : RXFace P S) : Set E :=
  convexHull ℝ {rxZeroPoint P S J (rxFaceX P S f),
    rxOnePoint P S J (rxFaceQ P S f 0), rxTwoPoint P S J (rxFaceZ P S f)} ∪
  convexHull ℝ {rxZeroPoint P S J (rxFaceX P S f),
    rxTwoPoint P S J (rxFaceZ P S f), rxOnePoint P S J (rxFaceQ P S f 1)}
def rectangleEndpointPoint (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (edge : SubdivisionBoundaryEdge P x S)
    (endpoint : BDL26FiniteTannerSquare.Two) : E :=
  if endpoint = 0 then subdivisionVertexPoint P S J x (subdivisionEdgeStart P x S edge.1)
  else subdivisionVertexPoint P S J x (subdivisionEdgeEnd P x S edge.1)
def rectangleMidpoint (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (edge : SubdivisionBoundaryEdge P x S) : E :=
  (1 / 2 : ℝ) • (subdivisionVertexPoint P S J x (subdivisionEdgeStart P x S edge.1) +
    subdivisionVertexPoint P S J x (subdivisionEdgeEnd P x S edge.1))
def terminalRungFace (P : TannerSquarePresentation) (S : OddScale)
    (f : P.Face) (side copy : BDL26FiniteTannerSquare.Two) : RXFace P S :=
  .inr (.inl ⟨faceXQEdge P f side,
    .inr ⟨P.faceZ f, P.data.faceQ_qz f side⟩, copy⟩)
def pathStripFace (P : TannerSquarePresentation) (S : OddScale) (f : P.Face)
    (side copy : BDL26FiniteTannerSquare.Two) (i : Fin S.half)
    (endpoint : BDL26FiniteTannerSquare.Two) : RXFace P S :=
  .inr (.inl ⟨⟨(P.faceX f, P.faceQ f side), P.data.faceQ_xq f side⟩,
    .inl (copy, ⟨P.faceZ f, P.data.faceQ_qz f side⟩, i), endpoint⟩)
def transposePointMap (P : TannerSquarePresentation) (J : Vertex P → E) :
    Vertex (transposePresentation P) → E := J ∘ transposeVertexEquiv P
def rzXPoint (P : TannerSquarePresentation) (S : OddScale) (J : Vertex P → E) :
    BDL26RZLocalReplacement.RZX P S → E :=
  rxTwoPoint (transposePresentation P) S (transposePointMap P J)
def rzQPoint (P : TannerSquarePresentation) (S : OddScale) (J : Vertex P → E) :
    BDL26RZLocalReplacement.RZQ P S → E :=
  rxOnePoint (transposePresentation P) S (transposePointMap P J)
def rzZPoint (P : TannerSquarePresentation) (S : OddScale) (J : Vertex P → E) :
    BDL26RZLocalReplacement.RZZ P S → E :=
  rxZeroPoint (transposePresentation P) S (transposePointMap P J)
noncomputable def rzFaceImage (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) (f : BDL26RZLocalReplacement.RZFace P S) : Set E :=
  convexHull ℝ {rzXPoint P S J (BDL26RZLocalReplacement.rzFaceX P S f),
    rzQPoint P S J (BDL26RZLocalReplacement.rzFaceQ P A S f 0),
    rzZPoint P S J (BDL26RZLocalReplacement.rzFaceZ P A S f)} ∪
  convexHull ℝ {rzXPoint P S J (BDL26RZLocalReplacement.rzFaceX P S f),
    rzZPoint P S J (BDL26RZLocalReplacement.rzFaceZ P A S f),
    rzQPoint P S J (BDL26RZLocalReplacement.rzFaceQ P A S f 1)}
end PointMaps
noncomputable section TriangleFrame
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def triangleUnitDirection (b : E) : E := ‖b‖⁻¹ • b
def triangleAltitudeVector (b c : E) : E :=
  c - ⟪triangleUnitDirection b, c⟫_ℝ • triangleUnitDirection b
def triangleLatticeAnchor (o b c : E) (ell : ℝ) (p : ℤ × ℤ) : E :=
  o + ((p.1 : ℝ) / ell) • b + ((p.2 : ℝ) / ell) • c
end TriangleFrame
section AnchorGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end AnchorGeometry
noncomputable section WidthArea
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def TriangleWidthAtLeast (b c : E) (delta : ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → t ≤ 1 → delta ≤ ‖c - t • b‖) ∧
  (∀ t : ℝ, 0 ≤ t → t ≤ 1 → delta ≤ ‖b - t • c‖) ∧
  (∀ t : ℝ, 0 ≤ t → t ≤ 1 → delta ≤ ‖(1 - t) • b + t • c‖)
def triangleAreaProduct (b c : E) : ℝ := ‖b‖ * ‖triangleAltitudeVector b c‖
end WidthArea
section WidthPacking
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end WidthPacking
noncomputable section GridCornerBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def foldedGridPoint (x q₀ q₁ z : E) (ell : ℝ) (m n : ℤ) : E :=
  foldedSquare x q₀ q₁ z ((m : ℝ) / ell) ((n : ℝ) / ell)
end GridCornerBounds
section MaterializedSlots
def boundaryRectangleFace (P : TannerSquarePresentation) (S : OddScale) (f : P.Face)
    (side copy : BDL26FiniteTannerSquare.Two) (i : Fin S.half)
    (endpoint : BDL26FiniteTannerSquare.Two) : RXFace P S :=
  .inl ⟨P.faceX f,
    .inr (qToXSubdivisionBoundaryEdge P (P.faceQ f side) (P.faceX f)
      (P.data.faceQ_xq f side) S (⟨P.faceZ f, P.data.faceQ_qz f side⟩, i)), copy, endpoint⟩
end MaterializedSlots
noncomputable section ActualSlotCharging
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
def chargePatchSlot (S : OddScale) : PatchSlot S → PatchSlot S
  | .inl (.inl p) => .inl (.inl p)
  | .inl (.inr (side, i, copy, endpoint)) =>
      .inr (.inl (side, .inl (copy, i), endpoint))
  | .inr (.inl (side, .inl edge, endpoint)) => .inr (.inl (side, .inl edge, endpoint))
  | .inr (.inl (_, .inr _, copy)) => .inr (.inr copy)
  | .inr (.inr copy) => .inr (.inr copy)
def actualFlatImage (P : TannerSquarePresentation) (S : OddScale) (J : Vertex P → E)
    (c : P.Face × FlatCell S) : Set E := rxFaceImage P S J ((rxFaceFlatEquiv P S).symm c)
end ActualSlotCharging
section ActualHitReindexing
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
end ActualHitReindexing
noncomputable section PathStripFineCoordinates
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
end PathStripFineCoordinates
noncomputable section PathStripUpperFineCoordinates
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
end PathStripUpperFineCoordinates
section LabeledTrianglePacking
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end LabeledTrianglePacking
noncomputable section PlanarFineCorners
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def faceFineCorner (P : TannerSquarePresentation) (S : OddScale) (J : Vertex P → E)
    (f : P.Face) (m n : ℤ) (a b : BDL26FiniteTannerSquare.Two) : E :=
  foldedGridPoint (J (.x (P.faceX f))) (J (.q (P.faceQ f 0)))
    (J (.q (P.faceQ f 1))) (J (.z (P.faceZ f))) S.ell (m + a.val) (n + b.val)
end PlanarFineCorners
noncomputable section IncomingTriangles
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def oldTriangleImage (P : TannerSquarePresentation) (J : Vertex P → E)
    (t : P.Face × BDL26FiniteTannerSquare.Two) : Set E :=
  convexHull ℝ {J (.x (P.faceX t.1)), J (.q (P.faceQ t.1 t.2)), J (.z (P.faceZ t.1))}
def faceFineAnchor (P : TannerSquarePresentation) (S : OddScale) (J : Vertex P → E)
    (f : P.Face) (m n : ℤ) : E :=
  foldedGridPoint (J (.x (P.faceX f))) (J (.q (P.faceQ f 0)))
    (J (.q (P.faceQ f 1))) (J (.z (P.faceZ f))) S.ell m n
end IncomingTriangles
section WidthPermutation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end WidthPermutation
noncomputable section ActualPositiveFaces
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def rawPositiveCellEquiv (S : OddScale) : RawPositiveCell S ≃ PositiveCell S :=
  Equiv.prodCongr (Equiv.refl _)
    (Equiv.prodCongr (fineCoordinateEquiv S) (fineCoordinateEquiv S))
def rawPositiveFace (P : TannerSquarePresentation) (S : OddScale) (f : P.Face) :
    RawPositiveCell S → RXFace P S
  | (copy, .inl (i, a), .inl (j, b)) =>
      .inl ⟨P.faceX f, .inl (copy, oldFaceInXStar P f, i, j), a, b⟩
  | (copy, .inr _, .inl (i, endpoint)) => pathStripFace P S f 0 copy i endpoint
  | (copy, .inl (i, endpoint), .inr _) => pathStripFace P S f 1 copy i endpoint
  | (copy, .inr _, .inr _) => .inr (.inr (f, copy))
def fineQuadrantImage (P : TannerSquarePresentation) (S : OddScale) (J : Vertex P → E)
    (f : P.Face) (m n : ℤ) (a b : BDL26FiniteTannerSquare.Two) : Set E :=
  convexHull ℝ {faceFineCorner P S J f m n a b,
    faceFineCorner P S J f m n (1 - a) b,
    faceFineCorner P S J f m n (1 - a) (1 - b)} ∪
  convexHull ℝ {faceFineCorner P S J f m n a b,
    faceFineCorner P S J f m n (1 - a) (1 - b),
    faceFineCorner P S J f m n a (1 - b)}
end ActualPositiveFaces
section ActualTriangleIndices
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def fineEndpointBit (S : OddScale) : FineCoordinate S → BDL26FiniteTannerSquare.Two
  | .inl (_, a) => a
  | .inr _ => 0
def triangleGridIndex (side : BDL26FiniteTannerSquare.Two) (p : ℤ × ℤ) : ℤ × ℤ :=
  if side = 0 then (p.1 - p.2, p.2) else (p.2 - p.1, p.1)
end ActualTriangleIndices
section FineTriangleAssignment
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end FineTriangleAssignment
section FineHitMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end FineHitMetric
noncomputable section PositiveImageBridge
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def rawFineInteger (S : OddScale) (i : FineCoordinate S) : ℤ :=
  (fineCoordinateEquiv S i).val
end PositiveImageBridge
section ActualPositiveWitness
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end ActualPositiveWitness
section ActualPositivePacking
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end ActualPositivePacking
noncomputable section ActualPositiveSelection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def actualPositiveHitSide (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (c : PositiveCell S) (region : Set E) :
    BDL26FiniteTannerSquare.Two := by
  classical
  exact if c.2.2.val ≤ c.2.1.val ∧ (oldTriangleImage P J (f, 0) ∩ region).Nonempty
    then 0 else 1
structure IncomingFaceGeometry (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (lower width : ℝ) : Prop where
  side_lower : ∀ f side, lower ≤ ‖J (.q (P.faceQ f side)) - J (.x (P.faceX f))‖
  diagonal_lower : ∀ f, lower ≤ ‖J (.z (P.faceZ f)) - J (.x (P.faceX f))‖
  opposite_lower : ∀ f side, lower ≤ ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f side))‖
  side_upper : ∀ f side, ‖J (.q (P.faceQ f side)) - J (.x (P.faceX f))‖ ≤ S.ell
  diagonal_upper : ∀ f, ‖J (.z (P.faceZ f)) - J (.x (P.faceX f))‖ ≤ S.ell
  opposite_upper : ∀ f side, ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f side))‖ ≤ S.ell
  triangle_width : ∀ f side, TriangleWidthAtLeast
    (J (.q (P.faceQ f side)) - J (.x (P.faceX f)))
    (J (.z (P.faceZ f)) - J (.x (P.faceX f))) width
end ActualPositiveSelection
section ActualPositiveDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end ActualPositiveDensity
section ActualFullDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end ActualFullDensity
section RZDensityGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end RZDensityGeometry
section RZDensityCount
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end RZDensityCount
section FineEdgeLength
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end FineEdgeLength
section AdmissibleReplacementScale
end AdmissibleReplacementScale
section RoundedRZDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end RoundedRZDensity
section FaceBoundaryUnit
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def BoundaryUnit (x q₀ q₁ z : E) : Prop :=
  dist x q₀ ≤ 1 ∧ dist x q₁ ≤ 1 ∧ dist q₀ z ≤ 1 ∧ dist q₁ z ≤ 1
def rxFaceBoundaryUnit (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (c : RXFace P S) : Prop :=
  BoundaryUnit (rxZeroPoint P S J (rxFaceX P S c))
    (rxOnePoint P S J (rxFaceQ P S c 0))
    (rxOnePoint P S J (rxFaceQ P S c 1))
    (rxTwoPoint P S J (rxFaceZ P S c))
end FaceBoundaryUnit
section SeamBoundaryUnit
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end SeamBoundaryUnit
section AllFaceBoundaryUnit
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end AllFaceBoundaryUnit
section GlobalRXEdgeLength
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end GlobalRXEdgeLength
section GlobalRZEdgeLength
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end GlobalRZEdgeLength
section AffineBoundaryGluing
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def tannerTrianglePoint (P : TannerSquarePresentation) (J : Vertex P → E)
    (f : P.Face) (side : BDL26FiniteTannerSquare.Two) (a b : ℝ) : E :=
  (1 - a - b) • J (.x (P.faceX f)) + a • J (.q (P.faceQ f side)) + b • J (.z (P.faceZ f))
def xqEdgePoint (P : TannerSquarePresentation) (J : Vertex P → E) (e : XQEdge P) (t : ℝ) : E :=
  (1 - t) • J (.x e.1.1) + t • J (.q e.1.2)
def qzEdgePoint (P : TannerSquarePresentation) (J : Vertex P → E) (e : QZEdge P) (t : ℝ) : E :=
  (1 - t) • J (.q e.1.1) + t • J (.z e.1.2)
end AffineBoundaryGluing
noncomputable section ConstructedLocalMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def tannerFaceImage (P : TannerSquarePresentation) (J : Vertex P → E) (f : P.Face) : Set E :=
  convexHull ℝ {J (.x (P.faceX f)), J (.q (P.faceQ f 0)), J (.z (P.faceZ f))} ∪
    convexHull ℝ {J (.x (P.faceX f)), J (.z (P.faceZ f)), J (.q (P.faceQ f 1))}
def IsBoundedDensityLocalMap (P : TannerSquarePresentation) (J : Vertex P → E) (t : ℝ) : Prop :=
  (∀ x q, P.xq x q = true → dist (J (.x x)) (J (.q q)) ≤ 1) ∧
  (∀ q z, P.qz q z = true → dist (J (.q q)) (J (.z z)) ≤ 1) ∧
  ∀ center, ((familyHits (tannerFaceImage P J) (Metric.closedBall center 1)).card : ℝ) ≤ t
def rxVertexPoint (P : TannerSquarePresentation) (S : OddScale) (J : Vertex P → E) :
    Vertex (rxReplacementPresentation P S) → E
  | .x x => rxZeroPoint P S J x
  | .q q => rxOnePoint P S J q
  | .z z => rxTwoPoint P S J z
def rzVertexPoint (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) :
    Vertex (BDL26RZLocalReplacement.rzReplacementPresentation P A S) → E
  | .x x => rzXPoint P S J x
  | .q q => rzQPoint P S J q
  | .z z => rzZPoint P S J z
end ConstructedLocalMap
section RoundedConstructedLocalMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end RoundedConstructedLocalMap
section ConstructedDegreeBounds
open BDL26BoundedValence
end ConstructedDegreeBounds
section CanonicalReplacementHandoff
open BDL26BoundedValence
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
noncomputable def replacementScale (alpha lambda : ℝ)
    (hscale : 13 ≤ (2 * alpha + 1) * lambda) : OddScale :=
  leastOddScaleAbove ((2 * alpha + 1) * lambda) (by linarith)
end CanonicalReplacementHandoff
noncomputable section IntrinsicLocalCompatibility
open BDL26DecodingGraph
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def rxIntrinsicPoint (P : TannerSquarePresentation) (S : OddScale) (J : Vertex P → E) :
    (u : Vertex P) → RXZeroCell P S u → E
  | .x x, v => subdivisionVertexPoint P S J x v.2
  | .q q, v => qSubdivisionVertexPoint P S J q v.2
  | .z z, _ => J (.z z)
def rzIntrinsicPoint (P : TannerSquarePresentation) (S : OddScale) (J : Vertex P → E) :
    (u : Vertex P) → RZZeroCell P S u → E
  | .x x, _ => J (.x x)
  | .q q, v => qSubdivisionVertexPoint (transposePresentation P) S (transposePointMap P J) q v.2
  | .z z, v => subdivisionVertexPoint (transposePresentation P) S (transposePointMap P J) z v.2
end IntrinsicLocalCompatibility
section LocalFaceRestriction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def rxLocalFaceInclude (P : TannerSquarePresentation) (S : OddScale) (x : P.X) :
    DoubleCylinderFace P x S × (BDL26FiniteTannerSquare.Two × BDL26FiniteTannerSquare.Two) →
      RXFace P S := fun f => .inl ⟨x, f⟩
def rxLocalSquareImage (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) :
    DoubleCylinderFace P x S × (BDL26FiniteTannerSquare.Two × BDL26FiniteTannerSquare.Two) → Set E :=
  rxFaceImage P S J ∘ rxLocalFaceInclude P S x
def rzLocalFaceInclude (P : TannerSquarePresentation) (S : OddScale) (z : P.Z) :
    ZDoubleCylinderFace P z S × (BDL26FiniteTannerSquare.Two × BDL26FiniteTannerSquare.Two) →
      BDL26RZLocalReplacement.RZFace P S := fun f => .inl ⟨z, f⟩
def rzLocalSquareImage (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) (z : P.Z) :
    ZDoubleCylinderFace P z S × (BDL26FiniteTannerSquare.Two × BDL26FiniteTannerSquare.Two) → Set E :=
  rzFaceImage P A S J ∘ rzLocalFaceInclude P S z
end LocalFaceRestriction
section IntrinsicFaceDensity
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def rxIntrinsicFaceImage (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (f : DoubleCylinderFace P x S) : Set E :=
  ⋃ corner, rxLocalSquareImage P S J x (f, corner)
def rzIntrinsicFaceImage (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) (z : P.Z) (f : ZDoubleCylinderFace P z S) : Set E :=
  ⋃ corner, rzLocalSquareImage P A S J z (f, corner)
end IntrinsicFaceDensity
end QEC.Coding.BDL26ReplacementEmbedding


