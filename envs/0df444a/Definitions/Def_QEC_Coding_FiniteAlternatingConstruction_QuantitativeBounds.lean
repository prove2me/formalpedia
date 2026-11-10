-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
-- name    : QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T01:19:42.276205+00:00
-- url     : https://prove2.me/theorems/d4c3ff7e-d339-45f9-bf14-73df652e6e97
-- title:
--   Quantitative Bounds
-- statement:
--   Definitions and structural lemmas for Quantitative Bounds, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_correctionRegion_mem
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_syndromeRegion_mem
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
namespace QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph
noncomputable instance rzQFintype (P : TannerSquarePresentation) (S : OddScale) :
    Fintype (BDL26RZLocalReplacement.RZQ P S) := by
  classical
  dsimp [BDL26RZLocalReplacement.RZQ, ZDoubleCylinderEdge, QDoubleCylinderVertex,
    DoubleCylinderEdge, transposePresentation, transposeTannerSquareData]
  infer_instance
def rxQubitRoots (P : TannerSquarePresentation) (S : OddScale) :
    P.Q × BDL26FiniteTannerSquare.Two ↪ RX1 P S where
  toFun qt := Sum.inr ⟨qt.1, qt.2, Sum.inl (Sum.inl ())⟩
  inj' := by
    rintro ⟨q, t⟩ ⟨q', t'⟩ h
    have hs := Sum.inr.inj h
    have hq := congrArg Sigma.fst hs
    cases hq
    have hv := eq_of_heq (Sigma.mk.inj_iff.mp hs).2
    have ht := congrArg Prod.fst hv
    cases ht
    rfl
def rzQubitRoots (P : TannerSquarePresentation) (S : OddScale) :
    P.Q × BDL26FiniteTannerSquare.Two ↪ BDL26RZLocalReplacement.RZQ P S where
  toFun qt := Sum.inr ⟨qt.1, qt.2, Sum.inl (Sum.inl ())⟩
  inj' := by
    rintro ⟨q, t⟩ ⟨q', t'⟩ h
    have hs := Sum.inr.inj h
    have hq := congrArg Sigma.fst hs
    cases hq
    have hv := eq_of_heq (Sigma.mk.inj_iff.mp hs).2
    have ht := congrArg Prod.fst hv
    cases ht
    rfl
abbrev TannerWedge (P : TannerSquarePresentation) :=
  {t : P.X × P.Q × P.Z // P.xq t.1 t.2.1 = true ∧ P.qz t.2.1 t.2.2 = true}
def faceCornerWedge (P : TannerSquarePresentation) :
    P.Face × BDL26FiniteTannerSquare.Two → TannerWedge P :=
  fun fi => ⟨(P.faceX fi.1, P.faceQ fi.1 fi.2, P.faceZ fi.1),
    P.data.faceQ_xq fi.1 fi.2, P.data.faceQ_qz fi.1 fi.2⟩
def xStarFaceEquiv (P : TannerSquarePresentation) :
    (Σ x : P.X, XStarFace P x) ≃ P.Face where
  toFun f := f.2.1
  invFun f := ⟨P.faceX f, f, by simp [xStarFaceMember]⟩
  left_inv := by
    rintro ⟨x, f, hf⟩
    have hx : P.faceX f = x := by simpa [xStarFaceMember] using hf
    subst x
    rfl
  right_inv := fun _ => rfl
def faceCornerBoundaryEdge (P : TannerSquarePresentation) :
    P.Face × BDL26FiniteTannerSquare.Two → Σ x : P.X, XStarBoundaryEdge P x :=
  fun fi => ⟨P.faceX fi.1, Sum.inr (faceQZEdge P fi.1 fi.2), by
    simp only [xStarBoundaryEdgeMember, decide_eq_true_eq]
    refine ⟨fi.1, by simp [xStarFaceMember], ?_⟩
    change decide (faceQZEdge P fi.1 fi.2 = faceQZEdge P fi.1 0 ∨
      faceQZEdge P fi.1 fi.2 = faceQZEdge P fi.1 1) = true
    have hi : fi.2 = 0 ∨ fi.2 = 1 := by
      have hlt : fi.2.val < 2 := fi.2.isLt
      apply or_iff_not_imp_left.mpr
      intro hzero
      apply Fin.ext
      have hne : fi.2.val ≠ 0 := fun h => hzero (Fin.ext h)
      omega
    rcases hi with hi | hi <;> simp [hi]⟩
def subdivisionBoundaryEdgeEquiv (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :
    SubdivisionBoundaryEdge P x S ≃ XStarBoundaryEdge P x × Fin S.half where
  toFun e := by
    rcases e with ⟨e, he⟩
    cases e with
    | inl ei => exact (⟨ei.1.1, he⟩, ei.2)
    | inr fi => simp [subdivisionBoundaryEdgeMember] at he
  invFun ei := subdivisionOriginalBoundaryEdge P x S ei.1 ei.2
  left_inv := by
    rintro ⟨e, he⟩
    cases e with
    | inl ei => rfl
    | inr fi => simp [subdivisionBoundaryEdgeMember] at he
  right_inv := by rintro ⟨⟨e, he⟩, i⟩; rfl
def xqQStarEdgeEquiv (P : TannerSquarePresentation) :
    (Σ a : XQEdge P, QStarEdge P a.1.2) ≃ TannerWedge P where
  toFun az := ⟨(az.1.1.1, az.1.1.2, az.2.1), az.1.2, az.2.2⟩
  invFun w := ⟨⟨(w.1.1,w.1.2.1),w.2.1⟩,w.1.2.2,w.2.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
def faceGrowthFactor (S : OddScale) : Nat := 2 * S.ell * (S.ell + 2)
noncomputable instance rzFaceFintype (P : TannerSquarePresentation) (S : OddScale) :
    Fintype (BDL26RZLocalReplacement.RZFace P S) := by
  classical
  dsimp [BDL26RZLocalReplacement.RZFace, BDL26RZLocalReplacement.RZLocalFace,
    BDL26RZLocalReplacement.RZQZGlueFace, BDL26RZLocalReplacement.RZOldXFace,
    ZDoubleCylinderFace, QDoubleCylinderEdge, DoubleCylinderFace,
    transposePresentation, transposeTannerSquareData]
  infer_instance
noncomputable def rzFaceEquiv (P : TannerSquarePresentation) (S : OddScale) :
    BDL26RZLocalReplacement.RZFace P S ≃ RXFace (transposePresentation P) S :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr
    (Equiv.sigmaCongr (transposeXQEdgeEquiv P).symm (fun _ => Equiv.refl _))
    (Equiv.refl _))
def leastOddAbove (threshold : Nat) : Nat := 2 * ((threshold + 1) / 2) + 1
theorem leastOddAbove_odd (threshold : Nat) : leastOddAbove threshold % 2 = 1 := by
  unfold leastOddAbove
  omega
theorem leastOddAbove_gt (threshold : Nat) : threshold < leastOddAbove threshold := by
  unfold leastOddAbove
  omega
noncomputable def leastOddScaleAbove (threshold : ℝ) (hone : 1 ≤ threshold) : OddScale where
  ell := leastOddAbove ⌊threshold⌋₊
  odd := leastOddAbove_odd _
  three_le := by
    have hf : 1 ≤ ⌊threshold⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by simpa using hone)
    have hg := leastOddAbove_gt ⌊threshold⌋₊
    have ho := leastOddAbove_odd ⌊threshold⌋₊
    omega
end QEC.Coding.BDL26QuantitativeBounds


