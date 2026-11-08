-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
-- name    : QEC_Coding_ExpanderCodes_TannerLabelledEdges
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T07:57:44.391647+00:00
-- url     : https://prove2.me/theorems/4afe39b4-6345-4247-9d4f-59e625f2d380
-- title:
--   Tanner Labelled Edges
-- statement:
--   Definitions and structural lemmas for Tanner Labelled Edges, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_labelledVertices_isClosed
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_mem_labelledVertices_iff
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_blockLength_eq_card
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_incidence_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_mem_variableSupport_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheck_globalOperator_eq_extendLocalToRegister
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
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.ProductExpansion.HammingWeight_neg
attribute [local simp] QEC.Coding.ProductExpansion.column_transpose
attribute [local simp] QEC.Coding.ProductExpansion.row_transpose
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.FiniteQuditCheck.globalOperator_eq_extendLocalToRegister
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.blockLength_eq_card
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.incidence_iff_mem_region
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.mem_variableSupport_iff_mem_region
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
namespace QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
def verticalEdgeEndpoint (label : W → G) (e : VerticalEdgeIndex W G)
    (endpointSide : Fin 2) : VertexIndex G :=
  match e with
  | (side, b, g) =>
      (side, endpointSide, doubleCoverVoltage label endpointSide b * g)
omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] in
@[simp] theorem verticalEdgeAtVertex_verticalEdgeEndpoint
    (label : W → G) (e : VerticalEdgeIndex W G)
    (endpointSide : Fin 2) :
    verticalEdgeAtVertex label (verticalEdgeEndpoint label e endpointSide)
      e.2.1 = e := by
  rcases e with ⟨side, b, g⟩
  simp [verticalEdgeAtVertex, verticalEdgeEndpoint]
omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] in
@[simp] theorem verticalEdgeAtVertex_direction
    (label : W → G) (v : VertexIndex G) (b : W) :
    (verticalEdgeAtVertex label v b).2.1 = b := by
  rcases v with ⟨side, side', g⟩
  rfl
omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] in
@[simp] theorem verticalNeighbor_verticalNeighbor
    (label : W → G) (v : VertexIndex G) (b : W) :
    verticalNeighbor label (verticalNeighbor label v b) b = v := by
  rcases v with ⟨side, side', g⟩
  simp [verticalNeighbor, mul_assoc]
omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] in
/-- Horizontal and vertical moves commute around every Tanner square. -/
theorem verticalNeighbor_horizontalNeighbor_commute
    (label : W → G) (v : VertexIndex G) (a b : W) :
    verticalNeighbor label (horizontalNeighbor label v a) b =
      horizontalNeighbor label (verticalNeighbor label v b) a := by
  rcases v with ⟨side, side', g⟩
  simp [verticalNeighbor, horizontalNeighbor, mul_assoc]
def verticalFaceNeighbor (label : W → G) (e : VerticalEdgeIndex W G)
    (a : W) : VerticalEdgeIndex W G :=
  verticalEdgeAtVertex label
    (horizontalNeighbor label (verticalEdgeEndpoint label e 0) a) e.2.1
def faceAtVerticalEdge (label : W → G) (e : VerticalEdgeIndex W G)
    (a : W) : FaceIndex W G :=
  faceAtVertex label (verticalEdgeEndpoint label e 0) a e.2.1
omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] in
@[simp] theorem verticalEdgeEndpoint_verticalFaceNeighbor_zero
    (label : W → G) (e : VerticalEdgeIndex W G) (a : W) :
    verticalEdgeEndpoint label (verticalFaceNeighbor label e a) 0 =
      horizontalNeighbor label (verticalEdgeEndpoint label e 0) a := by
  rcases e with ⟨side, b, g⟩
  simp [verticalFaceNeighbor, verticalEdgeEndpoint, verticalEdgeAtVertex,
    horizontalNeighbor, mul_assoc]
omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] in
@[simp] theorem verticalFaceNeighbor_direction
    (label : W → G) (e : VerticalEdgeIndex W G) (a : W) :
    (verticalFaceNeighbor label e a).2.1 = e.2.1 := by
  rcases e with ⟨side, b, g⟩
  rfl
omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] in
@[simp] theorem verticalNeighbor_verticalFaceNeighbor_endpoint
    (label : W → G) (e : VerticalEdgeIndex W G) (a : W) :
    verticalNeighbor label
        (verticalEdgeEndpoint label (verticalFaceNeighbor label e a) 0)
        (verticalFaceNeighbor label e a).2.1 =
      horizontalNeighbor label
        (verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1) a := by
  rw [verticalEdgeEndpoint_verticalFaceNeighbor_zero,
    verticalFaceNeighbor_direction,
    verticalNeighbor_horizontalNeighbor_commute]
omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] in
@[simp] theorem faceAtVerticalEdge_verticalFaceNeighbor
    (label : W → G) (e : VerticalEdgeIndex W G) (a : W) :
    faceAtVerticalEdge label (verticalFaceNeighbor label e a) a =
      faceAtVerticalEdge label e a := by
  simp [faceAtVerticalEdge]
def verticalFaceGraph (label : W → G) :
    SmallSetExpansion.WeightedGraph (VerticalEdgeIndex W G) :=
  fun e e' =>
    (Finset.univ.filter fun a : W => verticalFaceNeighbor label e a = e').card
def verticalEdgeOfFace (label : W → G) (p : FaceIndex W G)
    (side : Fin 2) : VerticalEdgeIndex W G :=
  match p with
  | (a, b, g) => (side, b, g * doubleCoverVoltage label side a)
def vertexAtFaceSides (label : W → G) (p : FaceIndex W G)
    (side side' : Fin 2) : VertexIndex G :=
  match p with
  | (a, b, g) =>
      (side, side', doubleCoverVoltage label side' b * g *
        doubleCoverVoltage label side a)
omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] in
@[simp] theorem verticalEdgeOfFace_faceAtVerticalEdge
    (label : W → G) (e : VerticalEdgeIndex W G) (a : W) :
    verticalEdgeOfFace label (faceAtVerticalEdge label e a) e.1 = e := by
  rcases e with ⟨side, b, g⟩
  fin_cases side <;>
    simp [verticalEdgeOfFace, faceAtVerticalEdge, faceAtVertex,
      verticalEdgeEndpoint, doubleCoverVoltage, mul_assoc]
omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] in
@[simp] theorem verticalEdgeAtVertex_verticalNeighbor
    (label : W → G) (v : VertexIndex G) (b : W) :
    verticalEdgeAtVertex label (verticalNeighbor label v b) b =
      verticalEdgeAtVertex label v b := by
  rcases v with ⟨side, side', g⟩
  simp [verticalEdgeAtVertex, verticalNeighbor, mul_assoc]
def CarriesActiveFaceVerticalEdge (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (e : VerticalEdgeIndex W G) : Prop :=
  ∃ a, localFaceMatrix label c (verticalEdgeEndpoint label e 0) e.2.1 a ≠ 0
def IsActiveVerticalEdge (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (e : VerticalEdgeIndex W G) : Prop :=
  verticalEdgeEndpoint label e 0 ∈ vertexBlockSupport c ∨
    verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1 ∈
      vertexBlockSupport c ∨
    CarriesActiveFaceVerticalEdge label c e
def IsFaceActiveVerticalEdge (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (e : VerticalEdgeIndex W G) : Prop :=
  IsFaceActiveVerticalEdgeAt label c
    (verticalEdgeEndpoint label e 0) e.2.1
noncomputable def activeVerticalEdges (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    Finset (VerticalEdgeIndex W G) := by
  classical
  exact Finset.univ.filter (IsActiveVerticalEdge label c)
noncomputable def activeVertexIncidentVerticalEdges (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    Finset (VerticalEdgeIndex W G) := by
  classical
  exact (vertexBlockSupport c ×ˢ (Finset.univ : Finset W)).image fun p =>
    verticalEdgeAtVertex label p.1 p.2
noncomputable def activeFaceIncidentVerticalEdges (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    Finset (VerticalEdgeIndex W G) := by
  classical
  exact (faceSupport c ×ˢ (Finset.univ : Finset (Fin 2))).image fun p =>
    verticalEdgeOfFace label p.1 p.2
omit [Fintype F] [DecidableEq W] [DecidableEq R] [DecidableEq R'] in
/-- A non-active member of the least labelled closure must have entered via
the face-active-edge closure rule, not merely satisfy its degree conclusion. -/
theorem labelledVertices_nonactive_incident
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (m : Nat) (v : VertexIndex G)
    (hv : v ∈ labelledVertices label c m)
    (hvInactive : v ∉ vertexBlockSupport c) :
    IsIncidentToFaceActiveVerticalEdge label c v := by
  by_contra hvIncident
  let L := labelledVertices label c m
  have hClosed := labelledVertices_isClosed label c m
  have hEraseClosed : IsClosedLabelledSet label c m (L.erase v) := by
    constructor
    · intro u hu
      exact Finset.mem_erase.mpr ⟨by
        intro huv
        subst u
        exact hvInactive hu, hClosed.1 hu⟩
    · intro u huIncident huDegree
      have huDegreeL : m ≤ ∑ x ∈ L, adjacencyGraph label u x :=
        huDegree.trans (Finset.sum_le_sum_of_subset (Finset.erase_subset v L))
      have huL : u ∈ L := hClosed.2 u huIncident huDegreeL
      have huv : u ≠ v := by
        intro huv
        subst u
        exact hvIncident huIncident
      exact Finset.mem_erase.mpr ⟨huv, huL⟩
  have hvErase : v ∈ L.erase v :=
    (mem_labelledVertices_iff label c m v).mp hv (L.erase v) hEraseClosed
  simp at hvErase
noncomputable def activeFaceIncidences (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (L : Finset (VertexIndex G)) :
    Finset (VertexIndex G × FaceIndex W G) := by
  classical
  exact (L ×ˢ faceSupport c).filter fun vp => vp.2 ∈ faceStar label vp.1
noncomputable def nonactiveLabelledVertices (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (m : Nat) : Finset (VertexIndex G) :=
  labelledVertices label c m \ vertexBlockSupport c
noncomputable def selectedFaceActiveDirection (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (m : Nat)
    (v : {v // v ∈ nonactiveLabelledVertices label c m}) : W := by
  classical
  have hvData := Finset.mem_sdiff.mp v.2
  have hvIncident := labelledVertices_nonactive_incident
    label c m v.1 hvData.1 hvData.2
  exact Classical.choose hvIncident
noncomputable def selectedFaceDirectionIncidences (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (m : Nat) :
    Finset ({v // v ∈ nonactiveLabelledVertices label c m} × W) := by
  classical
  exact Finset.univ.filter fun va =>
    localFaceMatrix label c va.1.1
      (selectedFaceActiveDirection label c m va.1) va.2 ≠ 0
noncomputable def unlabelledActiveVerticalEdges (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (L : Finset (VertexIndex G)) : Finset (VerticalEdgeIndex W G) := by
  classical
  exact (activeVerticalEdges label c).filter fun e =>
    verticalEdgeEndpoint label e 0 ∉ L ∧
      verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1 ∉ L
end QEC.Coding.TannerLiftedProduct


