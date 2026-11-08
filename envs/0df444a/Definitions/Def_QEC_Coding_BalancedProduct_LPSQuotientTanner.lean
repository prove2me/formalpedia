-- Prove2me | Definitions.Def_QEC_Coding_BalancedProduct_LPSQuotientTanner
-- name    : QEC_Coding_BalancedProduct_LPSQuotientTanner
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T07:30:26.561027+00:00
-- url     : https://prove2.me/theorems/0646f627-cb4d-45e9-95c4-b2678c35550c
-- title:
--   LPSQuotient Tanner
-- statement:
--   Definitions and structural lemmas for LPSQuotient Tanner, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_FreeOrbitCoordinates
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTannerExpansion
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Mathlib.Data.Fintype.EquivFin
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_finCyclicEquiv_apply_eq_generator_pow
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_finCyclicInvEquiv_apply_eq_invGenerator_pow
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_liftedProductData_A
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_liftedProductData_B_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_FreeOrbitCoordinates_freeOrbitEquiv_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_FreeOrbitCoordinates_freeOrbitEquiv_symm_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_FreeOrbitCoordinates_groupAlgebraMatrix_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_upperUnipotent_edge_fixed_iff_one
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_checkBlock_basis_same
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_incidentAsEdge_edgeAsIncident
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_dualData_A
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_dualData_B
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_dualData_dualData
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_swapWord_inl_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_swapWord_inr_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_swapWord_swapWord
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_horizontalPart_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_verticalPart_apply
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_groupedDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomTwist_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_blockEquiv_apply
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_inNeighbor_eq_sub
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_inNeighbor_outNeighbor
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_outNeighbor_eq_add
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_outNeighbor_inNeighbor
import Theorems.Thm_QEC_Coding_FiberBundle_homologyBaseProjection_add
import Theorems.Thm_QEC_Coding_FiberBundle_mem_horizontalBoundaryShadow_iff
import Theorems.Thm_QEC_Coding_FiberBundle_multipleRotation_val
import Theorems.Thm_QEC_Coding_FiberBundle_translateBundleWord_apply_inl
import Theorems.Thm_QEC_Coding_FiberBundle_translateBundleWord_apply_inr
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
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
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.BalancedProduct.Cyclic.finCyclicEquiv_apply_eq_generator_pow
attribute [local simp] QEC.Coding.BalancedProduct.Cyclic.finCyclicInvEquiv_apply_eq_invGenerator_pow
attribute [local simp] QEC.Coding.BalancedProduct.Cyclic.liftedProductData_A
attribute [local simp] QEC.Coding.BalancedProduct.Cyclic.liftedProductData_B_apply
attribute [local simp] QEC.Coding.BalancedProduct.FreeOrbitCoordinates.freeOrbitEquiv_apply
attribute [local simp] QEC.Coding.BalancedProduct.FreeOrbitCoordinates.freeOrbitEquiv_symm_apply
attribute [local simp] QEC.Coding.BalancedProduct.FreeOrbitCoordinates.groupAlgebraMatrix_apply
attribute [local simp] QEC.Coding.BalancedProduct.LPSTanner.checkBlock_basis_same
attribute [local simp] QEC.Coding.BalancedProduct.LPSTanner.incidentAsEdge_edgeAsIncident
attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.dualData_A
attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.dualData_B
attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.dualData_dualData
attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.swapWord_inl_apply
attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.swapWord_inr_apply
attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.swapWord_swapWord
attribute [local simp] QEC.Coding.BalancedProduct.PKDistance.horizontalPart_apply
attribute [local simp] QEC.Coding.BalancedProduct.PKDistance.verticalPart_apply
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.originalBoundary_single
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.columnDistribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.groupedDistribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.independentProduct_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomTwist.distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.blockEquiv_apply
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.inNeighbor_eq_sub
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.inNeighbor_outNeighbor
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.outNeighbor_eq_add
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.outNeighbor_inNeighbor
attribute [local simp] QEC.Coding.FiberBundle.homologyBaseProjection_add
attribute [local simp] QEC.Coding.FiberBundle.mem_horizontalBoundaryShadow_iff
attribute [local simp] QEC.Coding.FiberBundle.multipleRotation_val
attribute [local simp] QEC.Coding.FiberBundle.translateBundleWord_apply_inl
attribute [local simp] QEC.Coding.FiberBundle.translateBundleWord_apply_inr
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
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
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
namespace QEC.Coding.BalancedProduct.LPSQuotientTanner
open Classical
open QEC.Coding
open QEC.Coding.BalancedProduct
open Cyclic FreeOrbitCoordinates LPSTanner LPSArithmetic LPSGraph
open PKDistance
def cyclicUpperHom (q : ℕ) :
    CyclicGroup q →* PGL(2, ZMod q) where
  toFun h := upperUnipotentPGL h.toAdd
  map_one' := by simp
  map_mul' x y := by
    exact upperUnipotentPGL_add x.toAdd y.toAdd
theorem cyclicUpperHom_injective (q : ℕ) :
    Function.Injective (cyclicUpperHom q) := by
  intro x y hxy
  apply Multiplicative.toAdd.injective
  exact upperUnipotentPGL_injective hxy
instance cyclicVertexMulAction (q : ℕ) :
    MulAction (CyclicGroup q) (Vertex401 q) where
  smul h g := g * cyclicUpperHom q h
  one_smul g := by
    change g * cyclicUpperHom q 1 = g
    rw [map_one, mul_one]
  mul_smul x y g := by
    change g * cyclicUpperHom q (x * y) =
      (g * cyclicUpperHom q y) * cyclicUpperHom q x
    rw [map_mul, mul_assoc]
    congr 1
    rw [← map_mul, mul_comm, map_mul]
@[simp]
theorem cyclic_smul_vertex (q : ℕ) (h : CyclicGroup q) (g : Vertex401 q) :
    h • g = g * cyclicUpperHom q h := rfl
instance cyclicVertexIsCancelSMul (q : ℕ) :
    IsCancelSMul (CyclicGroup q) (Vertex401 q) where
  right_cancel' x y g hxy := by
    apply cyclicUpperHom_injective q
    apply mul_left_cancel (a := g)
    exact hxy
def smulEdge401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (h : CyclicGroup q) : Edge401 q hq ≃ Edge401 q hq :=
  (lpsRightIso401 q hq (cyclicUpperHom q h)).mapEdgeSet
instance cyclicEdgeMulAction
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) :
    MulAction (CyclicGroup q) (Edge401 q hq) where
  smul h e := smulEdge401 q hq h e
  one_smul e := by
    apply Subtype.ext
    change Sym2.map (Equiv.mulRight (cyclicUpperHom q 1)) e.1 = e.1
    rw [map_one]
    have hfun : (Equiv.mulRight (1 : Vertex401 q) : Vertex401 q → Vertex401 q) = id := by
      funext g
      simp
    rw [hfun]
    exact congrFun Sym2.map_id e.1
  mul_smul x y e := by
    apply Subtype.ext
    change Sym2.map (Equiv.mulRight (cyclicUpperHom q (x * y))) e.1 =
      Sym2.map (Equiv.mulRight (cyclicUpperHom q x))
        (Sym2.map (Equiv.mulRight (cyclicUpperHom q y)) e.1)
    rw [Sym2.map_map]
    let f : Vertex401 q → Vertex401 q :=
      fun g => g * cyclicUpperHom q (x * y)
    let k : Vertex401 q → Vertex401 q :=
      fun g => (g * cyclicUpperHom q y) * cyclicUpperHom q x
    have hfk : f = k := by
      funext g
      dsimp [f, k]
      rw [map_mul, mul_assoc]
      congr 1
      rw [← map_mul, mul_comm, map_mul]
    exact congrArg (fun z => Sym2.map z e.1) hfk
@[simp]
theorem cyclic_smul_edge_val
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (h : CyclicGroup q) (e : Edge401 q hq) :
    (h • e).1 = Sym2.map (Equiv.mulRight (cyclicUpperHom q h)) e.1 := rfl
instance cyclicEdgeIsCancelSMul
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) :
    IsCancelSMul (CyclicGroup q) (Edge401 q hq) where
  right_cancel' x y e hxy := by
    have hfix : (x * y⁻¹) • e = e := by
      rw [mul_smul]
      calc
        x • (y⁻¹ • e) = y⁻¹ • (x • e) := by
          rw [← mul_smul, ← mul_smul, mul_comm]
        _ = y⁻¹ • (y • e) := congrArg (fun z => y⁻¹ • z) hxy
        _ = e := inv_smul_smul y e
    have hout : s(e.1.out.1, e.1.out.2) = e.1 := e.1.out_eq
    have hedge :
        s((e.1.out.1 * cyclicUpperHom q (x * y⁻¹)),
          (e.1.out.2 * cyclicUpperHom q (x * y⁻¹))) = e.1 := by
      have hv := congrArg Subtype.val hfix
      rw [cyclic_smul_edge_val, ← hout] at hv
      rw [Sym2.map_mk] at hv
      change
        s((e.1.out.1 * cyclicUpperHom q (x * y⁻¹)),
          (e.1.out.2 * cyclicUpperHom q (x * y⁻¹))) =
            s(e.1.out.1, e.1.out.2) at hv
      exact hv.trans hout
    have hadj : (lpsCayleyGraph401 q hq).Adj e.1.out.1 e.1.out.2 := by
      have he := e.2
      rw [← hout, SimpleGraph.mem_edgeSet] at he
      exact he
    let u : upperUnipotentSubgroup (R := ZMod q) :=
      ⟨cyclicUpperHom q (x * y⁻¹), upperUnipotentPGL_mem _⟩
    have hu : u = 1 := by
      apply (upperUnipotent_edge_fixed_iff_one q hq hadj u).1
      change
        s((e.1.out.1 * cyclicUpperHom q (x * y⁻¹)),
          (e.1.out.2 * cyclicUpperHom q (x * y⁻¹))) =
            s(e.1.out.1, e.1.out.2)
      exact hedge.trans hout.symm
    have hupper : cyclicUpperHom q (x * y⁻¹) = 1 :=
      congrArg Subtype.val hu
    have hxyOne : x * y⁻¹ = 1 :=
      cyclicUpperHom_injective q (by simpa using hupper)
    exact (mul_inv_eq_one.mp hxyOne)
instance cyclicCheckMulAction (q : ℕ) :
    MulAction (CyclicGroup q) (Check401 q) where
  smul h gj := (h • gj.1, gj.2)
  one_smul gj := by
    apply Prod.ext
    · exact one_smul _ _
    · rfl
  mul_smul x y gj := by
    apply Prod.ext
    · exact mul_smul x y gj.1
    · rfl
@[simp]
theorem cyclic_smul_check (q : ℕ) (h : CyclicGroup q) (g : Vertex401 q)
    (j : Fin 200) : h • (g, j) = (h • g, j) := rfl
instance cyclicCheckIsCancelSMul (q : ℕ) :
    IsCancelSMul (CyclicGroup q) (Check401 q) where
  right_cancel' x y gj hxy := by
    apply IsCancelSMul.right_cancel x y gj.1
    exact congrArg Prod.fst hxy
theorem mem_smul_edge_iff
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (h : CyclicGroup q) (e : Edge401 q hq) (g : Vertex401 q) :
    h • g ∈ (h • e).1 ↔ g ∈ e.1 := by
  rw [cyclic_smul_edge_val, Sym2.mem_map]
  constructor
  · rintro ⟨w, hw, hwh⟩
    have hwg : w = g := by
      apply (Equiv.mulRight (cyclicUpperHom q h)).injective
      exact hwh
    simpa [hwg] using hw
  · intro hg
    exact ⟨g, hg, rfl⟩
def tannerCoefficient
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    Matrix (Check401 q) (Edge401 q hq) (ZMod 2) :=
  fun c e => tannerBoundary q hq40 hq (canonicalBasisWord e) c
abbrev CheckOrbit401 (q : ℕ) :=
  OrbitIndex (CyclicGroup q) (Check401 q)
abbrev EdgeOrbit401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) :=
  OrbitIndex (CyclicGroup q) (Edge401 q hq)
def lpsTannerGroupAlgebraMatrix
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    Matrix (CheckOrbit401 q) (EdgeOrbit401 q hq)
      (MonoidAlgebra (ZMod 2) (CyclicGroup q)) :=
  groupAlgebraMatrix (CyclicGroup q) (tannerCoefficient q hq40 hq)
noncomputable instance edge401Fintype'
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) : Fintype (Edge401 q hq) := by
  letI : DecidableRel (lpsCayleyGraph401 q hq).Adj := Classical.decRel _
  exact SimpleGraph.fintypeEdgeSet (lpsCayleyGraph401 q hq)
noncomputable instance checkOrbitFintype
    (q : ℕ) [Fact q.Prime] : Fintype (CheckOrbit401 q) := by
  letI : Finite (Check401 q) := inferInstance
  letI : Finite (CheckOrbit401 q) :=
    Quotient.finite (MulAction.orbitRel (CyclicGroup q) (Check401 q))
  exact Fintype.ofFinite _
noncomputable instance edgeOrbitFintype
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) : Fintype (EdgeOrbit401 q hq) := by
  letI : Finite (Edge401 q hq) := inferInstance
  letI : Finite (EdgeOrbit401 q hq) :=
    Quotient.finite (MulAction.orbitRel (CyclicGroup q) (Edge401 q hq))
  exact Fintype.ofFinite _
noncomputable instance checkOrbitDecidableEq
    (q : ℕ) [Fact q.Prime] : DecidableEq (CheckOrbit401 q) :=
  Classical.decEq _
noncomputable instance edgeOrbitDecidableEq
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) : DecidableEq (EdgeOrbit401 q hq) :=
  Classical.decEq _
def edgeWordInOrbitCoordinates
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) :
    Word (ZMod 2) (EdgeOrbit401 q hq × CyclicGroup q) :=
  fun p => x ((freeOrbitEquiv (CyclicGroup q) (Edge401 q hq)).symm p)
def checkWordInOrbitCoordinates
    (q : ℕ)
    (y : Word (ZMod 2) (Check401 q)) :
    Word (ZMod 2) (CheckOrbit401 q × CyclicGroup q) :=
  fun p => y ((freeOrbitEquiv (CyclicGroup q) (Check401 q)).symm p)
def checkWordFromOrbitCoordinates
    (q : ℕ)
    (z : Word (ZMod 2) (CheckOrbit401 q × CyclicGroup q)) :
    Word (ZMod 2) (Check401 q) :=
  fun c => z (freeOrbitEquiv (CyclicGroup q) (Check401 q) c)
def edgeWordFromOrbitCoordinates
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (z : Word (ZMod 2) (EdgeOrbit401 q hq × CyclicGroup q)) :
    Word (ZMod 2) (Edge401 q hq) :=
  fun e => z (freeOrbitEquiv (CyclicGroup q) (Edge401 q hq) e)
def lpsPrimalQuotientDistanceScale
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) : Nat :=
  Fintype.card (EdgeOrbit401 q hq) / 10000000
def lpsDualQuotientDistanceScale
    (q : ℕ) [Fact q.Prime] : Nat :=
  Fintype.card (CheckOrbit401 q) / 10000000
def lpsDressedZLowerBound
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) : Nat :=
  (q * lpsPrimalQuotientDistanceScale q hq) / 3739
def lpsDressedXLowerBound
    (q : ℕ) [Fact q.Prime] : Nat :=
  min (q * lpsDualQuotientDistanceScale q) (q / 804) / 37273
end QEC.Coding.BalancedProduct.LPSQuotientTanner


