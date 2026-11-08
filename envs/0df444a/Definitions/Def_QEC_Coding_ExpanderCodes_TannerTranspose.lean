-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_TannerTranspose
-- name    : QEC_Coding_ExpanderCodes_TannerTranspose
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T08:40:07.266342+00:00
-- url     : https://prove2.me/theorems/f3cce956-833d-4bdb-b3d3-7e260950e06d
-- title:
--   Tanner Transpose
-- statement:
--   Definitions and structural lemmas for Tanner Transpose, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_LiftedProduct_dualData_A
import Theorems.Thm_QEC_Coding_LiftedProduct_dualData_B
import Theorems.Thm_QEC_Coding_LiftedProduct_dualData_dualData
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_signedSwapWord_inl_apply
import Theorems.Thm_QEC_Coding_LiftedProduct_signedSwapWord_inr_apply
import Theorems.Thm_QEC_Coding_LiftedProduct_signedSwapWord_neg
import Theorems.Thm_QEC_Coding_LiftedProduct_signedSwapWord_signedSwapWord
import Theorems.Thm_QEC_Coding_LiftedProduct_signedSwapWord_signedUnswapWord
import Theorems.Thm_QEC_Coding_LiftedProduct_signedUnswapWord_signedSwapWord
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_horizontalNeighbor_horizontalNeighbor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightDoubleCoverNeighbor_rightDoubleCoverNeighbor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_sideInverseEquiv_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_sideInverseEquiv_symm_apply
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
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
attribute [local simp] QEC.Coding.LiftedProduct.dualData_A
attribute [local simp] QEC.Coding.LiftedProduct.dualData_B
attribute [local simp] QEC.Coding.LiftedProduct.dualData_dualData
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.signedSwapWord_inl_apply
attribute [local simp] QEC.Coding.LiftedProduct.signedSwapWord_inr_apply
attribute [local simp] QEC.Coding.LiftedProduct.signedSwapWord_neg
attribute [local simp] QEC.Coding.LiftedProduct.signedSwapWord_signedSwapWord
attribute [local simp] QEC.Coding.LiftedProduct.signedSwapWord_signedUnswapWord
attribute [local simp] QEC.Coding.LiftedProduct.signedUnswapWord_signedSwapWord
attribute [local simp] QEC.Coding.ProductExpansion.HammingWeight_neg
attribute [local simp] QEC.Coding.ProductExpansion.column_transpose
attribute [local simp] QEC.Coding.ProductExpansion.row_transpose
attribute [local simp] QEC.Coding.TannerLiftedProduct.horizontalNeighbor_horizontalNeighbor
attribute [local simp] QEC.Coding.TannerLiftedProduct.rightDoubleCoverNeighbor_rightDoubleCoverNeighbor
attribute [local simp] QEC.Coding.TannerLiftedProduct.sideInverseEquiv_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.sideInverseEquiv_symm_apply
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
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
def transposeVertexEquiv : VertexIndex G ≃ VertexIndex G where
  toFun v := (v.2.1, v.1, v.2.2⁻¹)
  invFun v := (v.2.1, v.1, v.2.2⁻¹)
  left_inv v := by rcases v with ⟨i, j, g⟩; simp
  right_inv v := by rcases v with ⟨i, j, g⟩; simp
omit [Field F] [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]
    [Fintype W] [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
@[simp] theorem transposeVertexEquiv_apply (v : VertexIndex G) :
    transposeVertexEquiv v = (v.2.1, v.1, v.2.2⁻¹) := rfl
def transposeFaceEquiv (inverseDirection : W ≃ W) :
    FaceIndex W G ≃ FaceIndex W G where
  toFun p := (inverseDirection p.2.1, inverseDirection p.1, p.2.2⁻¹)
  invFun p :=
    (inverseDirection.symm p.2.1, inverseDirection.symm p.1, p.2.2⁻¹)
  left_inv p := by rcases p with ⟨a, b, g⟩; simp
  right_inv p := by rcases p with ⟨a, b, g⟩; simp
omit [Field F] [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]
    [Fintype W] [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
@[simp] theorem transposeFaceEquiv_apply
    (inverseDirection : W ≃ W) (p : FaceIndex W G) :
    transposeFaceEquiv inverseDirection p =
      (inverseDirection p.2.1, inverseDirection p.1, p.2.2⁻¹) := rfl
def transposeQubitEquiv (inverseDirection : W ≃ W) :
    LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G ≃
      LiftedProduct.QubitIndex (Fin 2 × R') W W (Fin 2 × R) G where
  toFun q :=
    match q with
    | Sum.inl p => Sum.inl (transposeFaceEquiv inverseDirection p)
    | Sum.inr ((side, r), (side', r'), g) =>
        Sum.inr ((side', r'), (side, r), g⁻¹)
  invFun q :=
    match q with
    | Sum.inl p => Sum.inl ((transposeFaceEquiv inverseDirection).symm p)
    | Sum.inr ((side', r'), (side, r), g) =>
        Sum.inr ((side, r), (side', r'), g⁻¹)
  left_inv q := by
    cases q with
    | inl p =>
        exact congrArg Sum.inl
          ((transposeFaceEquiv inverseDirection).symm_apply_apply p)
    | inr p => rcases p with ⟨⟨side, r⟩, ⟨side', r'⟩, g⟩; simp
  right_inv q := by
    cases q with
    | inl p => simp
    | inr p => rcases p with ⟨⟨side', r'⟩, ⟨side, r⟩, g⟩; simp
def transposeEdgeEquiv (inverseDirection : W ≃ W) :
    LiftedProduct.C2Index W (Fin 2 × R') G ≃
      LiftedProduct.C0Index (Fin 2 × R') W G where
  toFun e := (e.2.1, inverseDirection e.1, e.2.2⁻¹)
  invFun e := (inverseDirection.symm e.2.1, e.1, e.2.2⁻¹)
  left_inv e := by rcases e with ⟨a, sr', g⟩; simp
  right_inv e := by rcases e with ⟨sr', a, g⟩; simp
def reindexColumns (e : W ≃ W) (M : Matrix R W F) : Matrix R W F :=
  fun r j => M r (e.symm j)
omit [Fintype F] [Fintype G] [DecidableEq G] [Fintype W] [DecidableEq W]
    [Field F] [DecidableEq F] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
@[simp] theorem reindexColumns_apply (e : W ≃ W)
    (M : Matrix R W F) (r : R) (j : W) :
    reindexColumns e M r j = M r (e.symm j) := rfl
omit [Fintype F] [Fintype G] [DecidableEq G] [Fintype W] [DecidableEq W]
    [Field F] [DecidableEq F] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
@[simp] theorem reindexColumns_refl (M : Matrix R W F) :
    reindexColumns (Equiv.refl W) M = M := by
  rfl
omit [Fintype F] [Fintype G] [DecidableEq G] [Fintype W] [DecidableEq W]
    [Field F] [DecidableEq F] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
@[simp] theorem reindexColumns_symm_reindexColumns
    (e : W ≃ W) (M : Matrix R W F) :
    reindexColumns e.symm (reindexColumns e M) = M := by
  funext r j
  simp [reindexColumns]
def transposeTannerWord (inverseDirection : W ≃ W)
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    Word F
      (LiftedProduct.QubitIndex (Fin 2 × R') W W (Fin 2 × R) G) :=
  fun q =>
    match q with
    | Sum.inl _ => z ((transposeQubitEquiv inverseDirection).symm q)
    | Sum.inr _ => -z ((transposeQubitEquiv inverseDirection).symm q)
omit [Fintype F] [Fintype G] [DecidableEq G] [Fintype W] [DecidableEq W]
    [DecidableEq F] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
@[simp] theorem transposeTannerWord_face_apply
    (inverseDirection : W ≃ W)
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (p : FaceIndex W G) :
    transposeTannerWord inverseDirection z
      (faceCoordinate (R := R') (R' := R)
        (transposeFaceEquiv inverseDirection p)) =
      z (faceCoordinate (R := R) (R' := R') p) := by
  change z (Sum.inl ((transposeFaceEquiv inverseDirection).symm
    (transposeFaceEquiv inverseDirection p))) = z (Sum.inl p)
  rw [(transposeFaceEquiv inverseDirection).symm_apply_apply]
omit [Fintype F] [Fintype G] [DecidableEq G] [Fintype W] [DecidableEq W]
    [DecidableEq F] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
@[simp] theorem transposeTannerWord_vertex_apply
    (inverseDirection : W ≃ W)
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (r : R) (r' : R') :
    transposeTannerWord inverseDirection z
      (vertexCoordinate (W := W) (transposeVertexEquiv v) r' r) =
      -z (vertexCoordinate (W := W) v r r') := by
  rcases v with ⟨side, side', g⟩
  simp [transposeTannerWord, transposeQubitEquiv, transposeVertexEquiv,
    vertexCoordinate]
def transposeC0Word (inverseDirection : W ≃ W)
    (x : Word F (LiftedProduct.C0Index (Fin 2 × R) W G)) :
    Word F (LiftedProduct.C2Index W (Fin 2 × R) G) :=
  fun c2 => x (transposeEdgeEquiv inverseDirection.symm c2)
def transposeVerticalEdge (inverseDirection : W ≃ W)
    (edge : VerticalEdgeIndex W G) : HorizontalEdgeIndex W G :=
  (inverseDirection edge.2.1, edge.1, edge.2.2⁻¹)
def untransposeHorizontalEdge (inverseDirection : W ≃ W)
    (edge : HorizontalEdgeIndex W G) : VerticalEdgeIndex W G :=
  (edge.2.1, inverseDirection.symm edge.1, edge.2.2⁻¹)
omit [Field F] [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]
    [Fintype W] [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
@[simp] theorem transposeVerticalEdge_untransposeHorizontalEdge
    (inverseDirection : W ≃ W) (edge : HorizontalEdgeIndex W G) :
    transposeVerticalEdge inverseDirection
      (untransposeHorizontalEdge inverseDirection edge) = edge := by
  rcases edge with ⟨a, side, g⟩
  simp [transposeVerticalEdge, untransposeHorizontalEdge]
def inverseGeneratorLabel (label : W → G) : W → G :=
  fun a => (label a)⁻¹
def doubleCoverSideSwapEquiv : (Fin 2 × G) ≃ (Fin 2 × G) where
  toFun x := (oppositeSide x.1, x.2)
  invFun x := (oppositeSide x.1, x.2)
  left_inv x := by rcases x with ⟨side, g⟩; simp
  right_inv x := by rcases x with ⟨side, g⟩; simp
end QEC.Coding.TannerLiftedProduct


