-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
-- name    : QEC_Coding_ExpanderCodes_TannerGraphExpansion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T07:59:20.771205+00:00
-- url     : https://prove2.me/theorems/9cf4756a-cb31-4beb-8c82-45993d975ce7
-- title:
--   Tanner Graph Expansion
-- statement:
--   Definitions and structural lemmas for Tanner Graph Expansion, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
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
universe v
variable {G W : Type v}
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
def rightDoubleCoverNeighbor (label : W → G) (x : Fin 2 × G) (a : W) :
    Fin 2 × G :=
  (oppositeSide x.1,
    x.2 * (doubleCoverVoltage label x.1 a)⁻¹ *
      doubleCoverVoltage label (oppositeSide x.1) a)
def leftDoubleCoverNeighbor (label : W → G) (x : Fin 2 × G) (a : W) :
    Fin 2 × G :=
  (oppositeSide x.1,
    doubleCoverVoltage label (oppositeSide x.1) a *
      (doubleCoverVoltage label x.1 a)⁻¹ * x.2)
def rightDoubleCoverGraph (label : W → G) :
    SmallSetExpansion.WeightedGraph (Fin 2 × G) :=
  fun x y =>
    (Finset.univ.filter fun a : W =>
      rightDoubleCoverNeighbor label x a = y).card
def leftDoubleCoverGraph (label : W → G) :
    SmallSetExpansion.WeightedGraph (Fin 2 × G) :=
  fun x y =>
    (Finset.univ.filter fun a : W =>
      leftDoubleCoverNeighbor label x a = y).card
def rightCayleyGraph (label : W → G) :
    SmallSetExpansion.WeightedGraph G :=
  fun g h =>
    (Finset.univ.filter fun a : W => g * label a = h).card
omit [Fintype G] [DecidableEq W] in
@[simp] theorem rightDoubleCoverGraph_zero_one
    (label : W → G) (g h : G) :
    rightDoubleCoverGraph label (0, g) (1, h) =
      rightCayleyGraph label g h := by
  simp [rightDoubleCoverGraph, rightCayleyGraph,
    rightDoubleCoverNeighbor, doubleCoverVoltage, oppositeSide]
omit [Fintype G] [DecidableEq W] in
@[simp] theorem rightDoubleCoverGraph_one_zero
    (label : W → G) (g h : G) :
    rightDoubleCoverGraph label (1, g) (0, h) =
      rightCayleyGraph label h g := by
  unfold rightDoubleCoverGraph rightCayleyGraph
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro a _ha
  simp [rightDoubleCoverNeighbor, doubleCoverVoltage, oppositeSide]
  constructor
  · intro hga
    calc
      h * label a = (g * (label a)⁻¹) * label a := by rw [hga]
      _ = g := by simp
  · intro hga
    calc
      g * (label a)⁻¹ = (h * label a) * (label a)⁻¹ := by rw [hga]
      _ = h := by simp
omit [Fintype G] [DecidableEq W] in
@[simp] theorem rightDoubleCoverGraph_zero_zero
    (label : W → G) (g h : G) :
    rightDoubleCoverGraph label (0, g) (0, h) = 0 := by
  simp [rightDoubleCoverGraph, rightDoubleCoverNeighbor,
    doubleCoverVoltage, oppositeSide]
omit [Fintype G] [DecidableEq W] in
@[simp] theorem rightDoubleCoverGraph_one_one
    (label : W → G) (g h : G) :
    rightDoubleCoverGraph label (1, g) (1, h) = 0 := by
  simp [rightDoubleCoverGraph, rightDoubleCoverNeighbor,
    doubleCoverVoltage, oppositeSide]
def sideInverseEquiv : (Fin 2 × G) ≃ (Fin 2 × G) where
  toFun x := (oppositeSide x.1, x.2⁻¹)
  invFun x := (oppositeSide x.1, x.2⁻¹)
  left_inv x := by rcases x with ⟨side, g⟩; simp
  right_inv x := by rcases x with ⟨side, g⟩; simp
def horizontalGraph (label : W → G) :
    SmallSetExpansion.WeightedGraph (VertexIndex G) :=
  fun v u =>
    (Finset.univ.filter fun a : W => horizontalNeighbor label v a = u).card
def verticalGraph (label : W → G) :
    SmallSetExpansion.WeightedGraph (VertexIndex G) :=
  fun v u =>
    (Finset.univ.filter fun b : W => verticalNeighbor label v b = u).card
def horizontalFiberEquiv :
    (Fin 2 × (Fin 2 × G)) ≃ VertexIndex G where
  toFun x := (x.2.1, x.1, x.2.2)
  invFun v := (v.2.1, v.1, v.2.2)
  left_inv x := by rcases x with ⟨i, j, g⟩; rfl
  right_inv v := by rcases v with ⟨i, j, g⟩; rfl
def verticalFiberEquiv :
    (Fin 2 × (Fin 2 × G)) ≃ VertexIndex G := Equiv.refl _
def verticalEdgeFiberEquiv :
    (W × (Fin 2 × G)) ≃ VerticalEdgeIndex W G where
  toFun x := (x.2.1, x.1, x.2.2)
  invFun e := (e.2.1, e.1, e.2.2)
  left_inv x := by rcases x with ⟨b, side, g⟩; rfl
  right_inv e := by rcases e with ⟨side, b, g⟩; rfl
def HasPartiteExpanderMixingBound
    (M : SmallSetExpansion.WeightedGraph (Fin 2 × G))
    (degree : Nat) (spectral : ℝ) : Prop :=
  ∀ S T : Finset (Fin 2 × G),
    (Fintype.card G : ℝ) * SmallSetExpansion.crossCount M S T ≤
      degree * (S.card : ℝ) * T.card +
        spectral * Fintype.card G *
          Real.sqrt ((S.card : ℝ) * T.card)
def sideSlice (S : Finset (Fin 2 × G)) (side : Fin 2) : Finset G :=
  Finset.univ.filter fun g => (side, g) ∈ S
section GlobalZero
universe u
variable {F : Type u} {R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
end GlobalZero
end QEC.Coding.TannerLiftedProduct


