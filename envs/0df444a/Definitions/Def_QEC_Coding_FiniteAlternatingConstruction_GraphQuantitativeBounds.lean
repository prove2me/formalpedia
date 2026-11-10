-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
-- name    : QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T01:21:18.261527+00:00
-- url     : https://prove2.me/theorems/16649b69-512a-4234-8fb1-2467622e113b
-- title:
--   Graph Quantitative Bounds
-- statement:
--   Definitions and structural lemmas for Graph Quantitative Bounds, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
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
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_map2Coord_canonicalBasis
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
namespace QEC.Coding.BDL26GraphQuantitativeBounds
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26RXLocalReplacement
open scoped BigOperators Classical
def tannerDegree (P : TannerSquarePresentation) (v : Vertex P) : Nat :=
  Fintype.card {w : Vertex P // tannerAdjacent P v w}
def xNeighborEquiv (P : TannerSquarePresentation) (x : P.X) :
    {v : Vertex P // tannerAdjacent P (.x x) v} ≃ {q : P.Q // P.xq x q = true} where
  toFun v := by
    rcases v with ⟨v,h⟩
    cases v with
    | x _ => cases h
    | q q => exact ⟨q,h⟩
    | z _ => cases h
  invFun q := ⟨.q q.1,q.2⟩
  left_inv := by
    rintro ⟨v,h⟩
    cases v with
    | x _ => cases h
    | q q => rfl
    | z _ => cases h
  right_inv := fun _ => rfl
def zNeighborEquiv (P : TannerSquarePresentation) (z : P.Z) :
    {v : Vertex P // tannerAdjacent P (.z z) v} ≃ {q : P.Q // P.qz q z = true} where
  toFun v := by
    rcases v with ⟨v,h⟩
    cases v with
    | x _ => cases h
    | q q => exact ⟨q,h⟩
    | z _ => cases h
  invFun q := ⟨.q q.1,q.2⟩
  left_inv := by
    rintro ⟨v,h⟩
    cases v with
    | x _ => cases h
    | q q => rfl
    | z _ => cases h
  right_inv := fun _ => rfl
def qNeighborEquiv (P : TannerSquarePresentation) (q : P.Q) :
    {v : Vertex P // tannerAdjacent P (.q q) v} ≃
      ({x : P.X // P.xq x q = true} ⊕ {z : P.Z // P.qz q z = true}) where
  toFun v := by
    rcases v with ⟨v,h⟩
    cases v with
    | x x => exact Sum.inl ⟨x,h⟩
    | q _ => cases h
    | z z => exact Sum.inr ⟨z,h⟩
  invFun v := match v with
    | Sum.inl x => ⟨.x x.1,x.2⟩
    | Sum.inr z => ⟨.z z.1,z.2⟩
  left_inv := by
    rintro ⟨v,h⟩
    cases v with
    | x x => rfl
    | q _ => cases h
    | z z => rfl
  right_inv := by intro v; cases v <;> rfl
def localCoordinateBound (S : OddScale) : Nat := 14 * S.ell ^ 2
def fullGraphDegreeBound (S : OddScale) : Nat := localCoordinateBound S + 8
def xStarCornerWedge (P : TannerSquarePresentation) (x : P.X) :
    XStarFace P x × BDL26FiniteTannerSquare.Two →
      Σ q : {q : P.Q // P.xq x q = true}, QStarEdge P q.1 := fun fi =>
  ⟨⟨P.faceQ fi.1.1 fi.2, by
    have hx : P.faceX fi.1.1 = x := by simpa [xStarFaceMember] using fi.1.2
    simpa only [hx] using P.data.faceQ_xq fi.1.1 fi.2⟩,
    P.faceZ fi.1.1, P.data.faceQ_qz fi.1.1 fi.2⟩
def xStarFaceEdge (P : TannerSquarePresentation) (x : P.X)
    (fe : XStarFace P x × (BDL26FiniteTannerSquare.Two × BDL26FiniteTannerSquare.Two)) :
    XStarEdge P x :=
  if fe.2.1 = 0 then xStarFaceXQEdge P x fe.1 fe.2.2
  else xStarFaceQZEdge P x fe.1 fe.2.2
def boundaryEdgeEmbedding (P : TannerSquarePresentation) (x : P.X) :
    XStarBoundaryEdge P x ↪ XStarEdge P x where
  toFun e := ⟨e.1,xStarBoundaryEdgeMember_to_star P x e.1 e.2⟩
  inj' := by
    intro e f h
    exact Subtype.ext (congrArg (fun a : XStarEdge P x => a.1) h)
noncomputable instance rxZeroCellFintype (P : TannerSquarePresentation)
    (S : OddScale) (u : Vertex P) : Fintype (RXZeroCell P S u) := by
  classical
  cases u <;> dsimp [RXZeroCell] <;> infer_instance
noncomputable instance rzZeroCellFintype (P : TannerSquarePresentation)
    (S : OddScale) (u : Vertex P) : Fintype (RZZeroCell P S u) := by
  classical
  cases u <;> dsimp [RZZeroCell,ZDoubleCylinderVertex,DoubleCylinderVertex,
    transposePresentation,transposeTannerSquareData] <;> infer_instance
namespace DegreeCover
open MultiscaleDecoder
variable {depth : Nat} {V : LevelIndex depth → Type}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
abbrev Same (G : DecodingGraphFamily depth V) (u : G.Node) :=
  {y : V u.1 // (G.level u.1).skeleton.adjacent u.2 y}
abbrev Up (G : DecodingGraphFamily depth V) (u : G.Node) :=
  Σ s : {s : StepIndex depth // u.1 = s.castSucc},
    {y : V s.1.succ // G.interLevel s.1 (s.2 ▸ u.2) y = true}
abbrev Down (G : DecodingGraphFamily depth V) (u : G.Node) :=
  Σ s : {s : StepIndex depth // u.1 = s.succ},
    {y : V s.1.castSucc // G.interLevel s.1 y (s.2 ▸ u.2) = true}
def cover (G : DecodingGraphFamily depth V) (u : G.Node) :
    Same G u ⊕ (Up G u ⊕ Down G u) → {v : G.Node // G.adjacent u v}
  | .inl y => ⟨⟨u.1,y.1⟩, by
      left
      simpa only [dif_pos rfl,dite_true] using y.2⟩
  | .inr (.inl sy) => ⟨⟨sy.1.1.succ,sy.2.1⟩, by
      right; left
      exact ⟨sy.1.1,by simpa only [dif_pos sy.1.2,dif_pos rfl,dite_true] using sy.2.2⟩⟩
  | .inr (.inr sy) => ⟨⟨sy.1.1.castSucc,sy.2.1⟩, by
      right; right
      exact ⟨sy.1.1,by simpa only [dif_pos rfl,dif_pos sy.1.2,dite_true] using sy.2.2⟩⟩
instance upStepSubsingleton (i : LevelIndex depth) :
    Subsingleton {s : StepIndex depth // i = s.castSucc} where
  allEq a b := Subtype.ext (Fin.ext (by
    have h := congrArg Fin.val (a.2.symm.trans b.2)
    exact h))
instance downStepSubsingleton (i : LevelIndex depth) :
    Subsingleton {s : StepIndex depth // i = s.succ} where
  allEq a b := Subtype.ext (Fin.ext (by
    have h := congrArg Fin.val (a.2.symm.trans b.2)
    exact Nat.succ.inj h))
end DegreeCover
open BDL26ReplacementSupport
def RXSyndromeCell (P : TannerSquarePresentation) (S : OddScale) : Vertex P → Type
  | .x x => DoubleCylinderFace P x S
  | .q q => QDoubleCylinderEdge P q S
  | .z _ => BDL26FiniteTannerSquare.Two
noncomputable instance rxSyndromeCellFintype (P : TannerSquarePresentation)
    (S : OddScale) (u : Vertex P) : Fintype (RXSyndromeCell P S u) := by
  classical
  cases u <;> dsimp [RXSyndromeCell] <;> infer_instance
def rxSyndromeCellToFiber (P : TannerSquarePresentation) (S : OddScale) :
    (u : Vertex P) → RXSyndromeCell P S u →
      {c : RX2 P S // rxSyndromeOwner P S c = u}
  | .x x, a => ⟨.inl (.inl ⟨x,a⟩),rfl⟩
  | .q q, a => ⟨.inl (.inr ⟨q,a⟩),rfl⟩
  | .z z, a => ⟨.inr (z,a),rfl⟩
noncomputable def maxLocalSyndromeSize (P : TannerSquarePresentation) (S : OddScale) : Nat :=
  max (Finset.univ.sup (fun u : Vertex P =>
      Nat.card {c : RX2 P S // rxSyndromeOwner P S c = u}))
    (Finset.univ.sup (fun z : P.Z =>
      Nat.card {c : BDL26RZLocalReplacement.RZZ P S // rzSyndromeOwner P S c = z}))
noncomputable def maxDecodingGraphDegree (S : OddScale) (depth : Nat) : Nat :=
  Finset.univ.sup (fun u : (decodingGraph S depth).Node =>
    Nat.card {v : (decodingGraph S depth).Node // (decodingGraph S depth).adjacent u v})
end QEC.Coding.BDL26GraphQuantitativeBounds


