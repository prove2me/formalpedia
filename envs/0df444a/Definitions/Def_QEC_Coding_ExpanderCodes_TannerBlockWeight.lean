-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
-- name    : QEC_Coding_ExpanderCodes_TannerBlockWeight
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T07:31:39.288391+00:00
-- url     : https://prove2.me/theorems/8dd1bf1e-7935-4a25-8d3f-4446f35de749
-- title:
--   Tanner Block Weight
-- statement:
--   Definitions and structural lemmas for Tanner Block Weight, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
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
abbrev FaceIndex (W G : Type v) := W × W × G
abbrev VertexIndex (G : Type v) := Fin 2 × Fin 2 × G
def oppositeSide (side : Fin 2) : Fin 2 :=
  Fin.rev side
def faceAtVertex (label : W → G) (v : VertexIndex G) (a b : W) :
    FaceIndex W G :=
  match v with
  | (side, side', g) =>
      (a, b, (doubleCoverVoltage label side' b)⁻¹ * g *
        (doubleCoverVoltage label side a)⁻¹)
def faceAtVertexEmbedding (label : W → G) (v : VertexIndex G) :
    W × W ↪ FaceIndex W G where
  toFun p := faceAtVertex label v p.2 p.1
  inj' := by
    rintro ⟨b, a⟩ ⟨b', a'⟩ h
    have ha : a = a' := congrArg (fun z : FaceIndex W G => z.1) h
    have hb : b = b' := congrArg (fun z : FaceIndex W G => z.2.1) h
    cases hb
    cases ha
    rfl
noncomputable def faceStar (label : W → G) (v : VertexIndex G) :
    Finset (FaceIndex W G) :=
  Finset.univ.map (faceAtVertexEmbedding label v)
omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
/-- A vertex star has exactly `|W|²` distinct faces. -/
@[simp] theorem card_faceStar (label : W → G) (v : VertexIndex G) :
    (faceStar label v).card = Fintype.card W * Fintype.card W := by
  simp [faceStar]
def faceCoordinate (p : FaceIndex W G) :
    LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G :=
  Sum.inl p
def vertexCoordinate (v : VertexIndex G) (r : R) (r' : R') :
    LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G :=
  match v with
  | (side, side', g) => Sum.inr ((side, r), (side', r'), g)
def coordinateVertex :
    LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G →
      Option (VertexIndex G)
  | Sum.inl _ => none
  | Sum.inr ((side, _r), (side', _r'), g) => some (side, side', g)
def verticalEdgeCoordinate (label : W → G) (v : VertexIndex G)
    (r : R) (b : W) :
    LiftedProduct.C0Index (Fin 2 × R) W G :=
  match v with
  | (side, side', g) =>
      ((side, r), b, (doubleCoverVoltage label side' b)⁻¹ * g)
def horizontalEdgeCoordinate (label : W → G) (v : VertexIndex G)
    (a : W) (r' : R') :
    LiftedProduct.C2Index W (Fin 2 × R') G :=
  match v with
  | (side, side', g) =>
      (a, (side', r'), g * (doubleCoverVoltage label side a)⁻¹)
def verticalNeighbor (label : W → G) (v : VertexIndex G) (b : W) :
    VertexIndex G :=
  match v with
  | (side, side', g) =>
      (side, oppositeSide side',
        doubleCoverVoltage label (oppositeSide side') b *
          (doubleCoverVoltage label side' b)⁻¹ * g)
def horizontalNeighbor (label : W → G) (v : VertexIndex G) (a : W) :
    VertexIndex G :=
  match v with
  | (side, side', g) =>
      (oppositeSide side, side',
        g * (doubleCoverVoltage label side a)⁻¹ *
          doubleCoverVoltage label (oppositeSide side) a)
def verticalEndpointCoordinate (label : W → G) (v : VertexIndex G)
    (r : R) (b : W) (endpointSide : Fin 2) (r' : R') :
    LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G :=
  match v with
  | (side, side', g) =>
      vertexCoordinate (W := W)
        (side, endpointSide,
          doubleCoverVoltage label endpointSide b *
            (doubleCoverVoltage label side' b)⁻¹ * g)
        r r'
def horizontalEndpointCoordinate (label : W → G) (v : VertexIndex G)
    (a : W) (endpointSide : Fin 2) (r : R) (r' : R') :
    LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G :=
  match v with
  | (side, side', g) =>
      vertexCoordinate (W := W)
        (endpointSide, side',
          g * (doubleCoverVoltage label side a)⁻¹ *
            doubleCoverVoltage label endpointSide a)
        r r'
omit [Field F] [Fintype F] [DecidableEq F] [Group G] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W] [Fintype R]
    [DecidableEq R] [Fintype R'] [DecidableEq R'] in
@[simp] theorem oppositeSide_oppositeSide (side : Fin 2) :
    oppositeSide (oppositeSide side) = side := by
  fin_cases side <;> rfl
omit [Field F] [Fintype F] [DecidableEq F] [Group G] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W] [Fintype R]
    [DecidableEq R] [Fintype R'] [DecidableEq R'] in
@[simp] theorem oppositeSide_ne (side : Fin 2) :
    oppositeSide side ≠ side := by
  fin_cases side <;> decide
omit [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]
    [Fintype W] [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
/-- Moving to the other vertical endpoint preserves the underlying edge
coordinate. -/
@[simp] theorem verticalEdgeCoordinate_verticalNeighbor
    (label : W → G) (v : VertexIndex G) (r : R) (b : W) :
    verticalEdgeCoordinate label (verticalNeighbor label v b) r b =
      verticalEdgeCoordinate label v r b := by
  rcases v with ⟨side, side', g⟩
  simp [verticalEdgeCoordinate, verticalNeighbor, mul_assoc]
omit [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]
    [Fintype W] [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
/-- Moving to the other horizontal endpoint preserves the underlying edge
coordinate. -/
@[simp] theorem horizontalEdgeCoordinate_horizontalNeighbor
    (label : W → G) (v : VertexIndex G) (a : W) (r' : R') :
    horizontalEdgeCoordinate label (horizontalNeighbor label v a) a r' =
      horizontalEdgeCoordinate label v a r' := by
  rcases v with ⟨side, side', g⟩
  simp [horizontalEdgeCoordinate, horizontalNeighbor, mul_assoc]
omit [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]
    [Fintype W] [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
/-- A face through v and direction b is also through the other endpoint of
that vertical edge. -/
@[simp] theorem faceAtVertex_verticalNeighbor
    (label : W → G) (v : VertexIndex G) (a b : W) :
    faceAtVertex label (verticalNeighbor label v b) a b =
      faceAtVertex label v a b := by
  rcases v with ⟨side, side', g⟩
  simp [faceAtVertex, verticalNeighbor, mul_assoc]
omit [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]
    [Fintype W] [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
/-- A face through v and direction a is also through the other endpoint of
that horizontal edge. -/
@[simp] theorem faceAtVertex_horizontalNeighbor
    (label : W → G) (v : VertexIndex G) (a b : W) :
    faceAtVertex label (horizontalNeighbor label v a) a b =
      faceAtVertex label v a b := by
  rcases v with ⟨side, side', g⟩
  simp [faceAtVertex, horizontalNeighbor, mul_assoc]
omit [DecidableEq F] [DecidableEq G] in
/-- The face in local directions (a,b) meets the vertical edge at v with
the first local-check coefficient. -/
@[simp] theorem boundary1Matrix_vertical_face_apply
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (v : VertexIndex G) (r : R) (b a : W) :
    LiftedProduct.boundary1Matrix (data label h h')
        (verticalEdgeCoordinate label v r b)
        (faceCoordinate (R := R) (R' := R') (faceAtVertex label v a b)) =
      h r a := by
  rcases v with ⟨side, side', g⟩
  simp [verticalEdgeCoordinate, faceCoordinate, faceAtVertex, data,
    doubleCoverTannerMatrix, LiftedProduct.rightRegularMatrix, mul_assoc]
omit [DecidableEq F] [DecidableEq G] in
/-- The coefficient at v in its incident vertical-edge equation is the
negative second local-check coefficient. -/
@[simp] theorem boundary1Matrix_vertical_vertex_apply
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (v : VertexIndex G) (r : R) (r' : R') (b : W) :
    LiftedProduct.boundary1Matrix (data label h h')
        (verticalEdgeCoordinate label v r b)
        (vertexCoordinate (W := W) v r r') =
      -h' r' b := by
  rcases v with ⟨side, side', g⟩
  simp [verticalEdgeCoordinate, vertexCoordinate, data,
    doubleCoverTannerMatrix, LiftedProduct.starTranspose,
    LiftedProduct.groupConj, LiftedProduct.leftRegularMatrix]
omit [DecidableEq F] [DecidableEq G] in
/-- The same local face meets the horizontal edge at v with the second
local-check coefficient. -/
@[simp] theorem boundary2Matrix_face_horizontal_apply
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (v : VertexIndex G) (r' : R') (b a : W) :
    LiftedProduct.boundary2Matrix (data label h h')
        (faceCoordinate (R := R) (R' := R') (faceAtVertex label v a b))
        (horizontalEdgeCoordinate label v a r') =
      h' r' b := by
  rcases v with ⟨side, side', g⟩
  simp [horizontalEdgeCoordinate, faceCoordinate, faceAtVertex, data,
    doubleCoverTannerMatrix, LiftedProduct.starTranspose,
    LiftedProduct.groupConj, LiftedProduct.leftRegularMatrix]
omit [DecidableEq F] [DecidableEq G] in
/-- The coefficient at v in its incident horizontal-edge equation is the
first local-check coefficient. -/
@[simp] theorem boundary2Matrix_vertex_horizontal_apply
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (v : VertexIndex G) (r : R) (r' : R') (a : W) :
    LiftedProduct.boundary2Matrix (data label h h')
        (vertexCoordinate (W := W) v r r')
        (horizontalEdgeCoordinate label v a r') =
      h r a := by
  rcases v with ⟨side, side', g⟩
  simp [horizontalEdgeCoordinate, vertexCoordinate, data,
    doubleCoverTannerMatrix, LiftedProduct.rightRegularMatrix]
def localFaceMatrix (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) : Matrix W W F :=
  fun b a => c (faceCoordinate (R := R) (R' := R')
    (faceAtVertex label v a b))
def localVertexMatrix
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) : Matrix R R' F :=
  fun r r' => c (vertexCoordinate (W := W) v r r')
def verticalEndpointSyndrome (label : W → G) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) : Matrix W R F :=
  fun b r =>
    ∑ endpoint : Fin 2 × R',
      h' endpoint.2 b *
        c (verticalEndpointCoordinate label v r b endpoint.1 endpoint.2)
def verticalVertexSyndrome (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) : Matrix W R F :=
  fun b r => ∑ r', h' r' b * localVertexMatrix c v r r'
def verticalNeighborSyndrome (label : W → G) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) : Matrix W R F :=
  fun b r => ∑ r', h' r' b *
    localVertexMatrix c (verticalNeighbor label v b) r r'
noncomputable def localVertexCosetLeaderMatrix
    (h : Matrix R W F) (hRank : h.rank = Fintype.card R)
    (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) : Matrix W W F :=
  ProductExpansion.fullRowRankCosetLeaderMatrix h hRank
    (verticalVertexSyndrome h' c v)
noncomputable def localFaceDifference
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) : Matrix W W F :=
  localFaceMatrix label c v - localVertexCosetLeaderMatrix h hRank h' c v
noncomputable def verticalInactiveDirections (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) : Finset W := by
  classical
  exact Finset.univ.filter fun b =>
    localVertexMatrix c (verticalNeighbor label v b) = 0
noncomputable def horizontalInactiveDirections (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) : Finset W := by
  classical
  exact Finset.univ.filter fun a =>
    localVertexMatrix c (horizontalNeighbor label v a) = 0
noncomputable def localHeavyDifferenceDirections
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) : Finset W := by
  classical
  exact (verticalInactiveDirections label c v).filter fun b =>
    ProductExpansion.row (localFaceDifference label h hRank h' c v) b ≠ 0
noncomputable def localAgreementDirections
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) : Finset W := by
  classical
  exact (verticalInactiveDirections label c v).filter fun b =>
    ProductExpansion.row (localFaceDifference label h hRank h' c v) b = 0
noncomputable def localFaceSupport (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) : Finset (W × W) := by
  classical
  exact Finset.univ.filter (fun p => localFaceMatrix label c v p.1 p.2 ≠ 0)
omit [Field F] [Fintype F] [DecidableEq F] [Group G] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W] [Fintype R]
    [DecidableEq R] [Fintype R'] [DecidableEq R'] in
@[simp] theorem coordinateVertex_faceCoordinate (p : FaceIndex W G) :
    coordinateVertex (R := R) (R' := R') (faceCoordinate (R := R) (R' := R') p) = none :=
  rfl
omit [Field F] [Fintype F] [DecidableEq F] [Group G] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W] [Fintype R]
    [DecidableEq R] [Fintype R'] [DecidableEq R'] in
@[simp] theorem coordinateVertex_vertexCoordinate
    (v : VertexIndex G) (r : R) (r' : R') :
    coordinateVertex (W := W) (vertexCoordinate (W := W) v r r') = some v := by
  rcases v with ⟨⟨side, side'⟩, g⟩
  rfl
noncomputable def faceSupport
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    Finset (FaceIndex W G) := by
  classical
  exact Finset.univ.filter (fun p => c (faceCoordinate (R := R) (R' := R') p) ≠ 0)
noncomputable def vertexBlockSupport
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    Finset (VertexIndex G) := by
  classical
  exact Finset.univ.filter (fun v =>
    ∃ r : R, ∃ r' : R', c (vertexCoordinate (W := W) v r r') ≠ 0)
noncomputable def blockWeight
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) : Nat :=
  (faceSupport c).card + (vertexBlockSupport c).card
noncomputable def vertexWitness
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : {v // v ∈ vertexBlockSupport c}) : R × R' := by
  classical
  have hv : ∃ r : R, ∃ r' : R',
      c (vertexCoordinate (W := W) v.1 r r') ≠ 0 := by
    simpa [vertexBlockSupport] using v.2
  exact ⟨Classical.choose hv, Classical.choose (Classical.choose_spec hv)⟩
omit [Fintype F] [Group G] [DecidableEq G] [Fintype W] [DecidableEq W]
    [DecidableEq R] [DecidableEq R'] in
/-- The chosen vertex-block witness is genuinely nonzero. -/
theorem vertexWitness_nonzero
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : {v // v ∈ vertexBlockSupport c}) :
    c (vertexCoordinate (W := W) v.1 (vertexWitness c v).1
      (vertexWitness c v).2) ≠ 0 := by
  classical
  have hv : ∃ r : R, ∃ r' : R',
      c (vertexCoordinate (W := W) v.1 r r') ≠ 0 := by
    simpa [vertexBlockSupport] using v.2
  exact Classical.choose_spec (Classical.choose_spec hv)
noncomputable def blockSupportToHammingSupport
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    Sum {p // p ∈ faceSupport c} {v // v ∈ vertexBlockSupport c} →
      {q // q ∈ hammingSupport c}
  | Sum.inl p => ⟨faceCoordinate (R := R) (R' := R') p.1, by
      simpa [faceSupport, hammingSupport] using p.2⟩
  | Sum.inr v =>
      ⟨vertexCoordinate (W := W) v.1 (vertexWitness c v).1
          (vertexWitness c v).2, by
        simpa [hammingSupport] using vertexWitness_nonzero c v⟩
noncomputable def chainComplex
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F) :=
  LiftedProduct.chainComplex (data label h g')
abbrev HorizontalEdgeIndex (W G : Type v) := W × Fin 2 × G
abbrev VerticalEdgeIndex (W G : Type v) := Fin 2 × W × G
def horizontalEdgeAtVertex (label : W → G) (v : VertexIndex G) (a : W) :
    HorizontalEdgeIndex W G :=
  match v with
  | (side, side', g) =>
      (a, side', g * (doubleCoverVoltage label side a)⁻¹)
def verticalEdgeAtVertex (label : W → G) (v : VertexIndex G) (b : W) :
    VerticalEdgeIndex W G :=
  match v with
  | (side, side', g) =>
      (side, b, (doubleCoverVoltage label side' b)⁻¹ * g)
def horizontalFaceColumnEmbedding (label : W → G)
    (v : VertexIndex G) (a : W) : W ↪ FaceIndex W G where
  toFun b := faceAtVertex label v a b
  inj' := by
    intro b b' hbb
    exact congrArg (fun p : FaceIndex W G => p.2.1) hbb
noncomputable def horizontalFaceColumn (label : W → G)
    (v : VertexIndex G) (a : W) : Finset (FaceIndex W G) :=
  Finset.univ.map (horizontalFaceColumnEmbedding label v a)
noncomputable def horizontalVertexEndpoints (label : W → G)
    (v : VertexIndex G) (a : W) : Finset (VertexIndex G) :=
  {v, horizontalNeighbor label v a}
noncomputable def horizontalFiberChain
    (edge : HorizontalEdgeIndex W G) (u : Word F R') :
    Word F (LiftedProduct.C2Index W (Fin 2 × R') G) := by
  classical
  exact ∑ r', u r' • canonicalBasisWord
    (edge.1, (edge.2.1, r'), edge.2.2)
noncomputable def verticalFiberCochain
    (edge : VerticalEdgeIndex W G) (u : Word F R) :
    Word F (LiftedProduct.C0Index (Fin 2 × R) W G) := by
  classical
  exact ∑ r, u r • canonicalBasisWord
    ((edge.1, r), edge.2.1, edge.2.2)
noncomputable def horizontalFiberBoundaryMoves
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F) :
    Finset (Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) := by
  classical
  exact Finset.univ.image (fun p : HorizontalEdgeIndex W G × Word F R' =>
    (chainComplex label h g').boundary2 (horizontalFiberChain p.1 p.2))
noncomputable def verticalFiberCoboundaryMoves
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F) :
    Finset (Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) := by
  classical
  exact Finset.univ.image (fun p : VerticalEdgeIndex W G × Word F R =>
    wordLinearMapTranspose (chainComplex label h g').boundary1
      (verticalFiberCochain p.1 p.2))
noncomputable def horizontalFiberBoundaryMoveAtVertex
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (v : VertexIndex G) (a : W) (u : Word F R') :
    Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G) :=
  (chainComplex label h g').boundary2
    (horizontalFiberChain (horizontalEdgeAtVertex label v a) u)
end QEC.Coding.TannerLiftedProduct


