-- Prove2me | Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
-- name    : QEC_Coding_BalancedProduct_PKDistance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:57:00.679966+00:00
-- url     : https://prove2.me/theorems/5b17a076-961a-4a99-a76d-1f085a9a45f2
-- title:
--   PKDistance
-- statement:
--   Definitions and structural lemmas for PKDistance, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_finCyclicEquiv_apply_eq_generator_pow
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_finCyclicInvEquiv_apply_eq_invGenerator_pow
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_liftedProductData_A
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_liftedProductData_B_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_dualData_A
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_dualData_B
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_dualData_dualData
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_swapWord_inl_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_swapWord_inr_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_swapWord_swapWord
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
attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.dualData_A
attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.dualData_B
attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.dualData_dualData
attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.swapWord_inl_apply
attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.swapWord_inr_apply
attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.swapWord_swapWord
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
namespace QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w
def cyclicShift
    {I : Type u} {G : Type v} [Group G] (t : G) :
    Word (ZMod 2) (I × G) →ₗ[ZMod 2] Word (ZMod 2) (I × G) where
  toFun z p := z (p.1, p.2 * t⁻¹)
  map_add' z w := by ext p; rfl
  map_smul' c z := by ext p; rfl
@[simp]
theorem cyclicShift_apply
    {I : Type u} {G : Type v} [Group G]
    (t : G) (z : Word (ZMod 2) (I × G)) (i : I) (g : G) :
    cyclicShift t z (i, g) = z (i, g * t⁻¹) := rfl
def binaryOverlap
    {ι : Type u} [Fintype ι]
    (left right : Word (ZMod 2) ι) : Nat :=
  HammingWeight fun i => left i * right i
def fibreWeight
    {I : Type u} {G : Type v} [Fintype G]
    (z : Word (ZMod 2) (I × G)) (i : I) : Nat :=
  HammingWeight fun g => z (i, g)
def cyclicPrefix
    {I : Type u} {G : Type v} [Group G]
    (x : G) (t : Nat) (z : Word (ZMod 2) (I × G)) :
    Word (ZMod 2) (I × G) :=
  ∑ k ∈ Finset.range t, cyclicShift (x ^ k) z
@[simp]
theorem cyclicPrefix_zero
    {I : Type u} {G : Type v} [Group G]
    (x : G) (z : Word (ZMod 2) (I × G)) :
    cyclicPrefix x 0 z = 0 := by
  simp [cyclicPrefix]
noncomputable def tannerAction
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) :
    Word (ZMod 2) (aCol × G) →ₗ[ZMod 2]
      Word (ZMod 2) (aRow × G) :=
  Matrix.toLin' fun (r, go) (c, gi) =>
    LiftedProduct.rightRegularMatrix (A r c) go gi
@[simp]
theorem tannerAction_apply
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G))
    (z : Word (ZMod 2) (aCol × G)) (r : aRow) (go : G) :
    tannerAction A z (r, go) =
      ∑ c, ∑ gi,
        LiftedProduct.rightRegularMatrix (A r c) go gi * z (c, gi) := by
  change (∑ pair : aCol × G,
    LiftedProduct.rightRegularMatrix (A r pair.1) go pair.2 * z pair) = _
  exact Fintype.sum_prod_type _
def constantOrbitWord
    {I G : Type} (z : Word (ZMod 2) I) : Word (ZMod 2) (I × G) :=
  fun p => z p.1
@[simp]
theorem constantOrbitWord_apply
    {I G : Type} (z : Word (ZMod 2) I) (i : I) (g : G) :
    constantOrbitWord (G := G) z (i, g) = z i := rfl
def horizontalPart
    {G aRow aCol : Type} :
    Word (ZMod 2)
        (LiftedProduct.QubitIndex aRow aCol Unit Unit G) →ₗ[ZMod 2]
      Word (ZMod 2) (aCol × G) where
  toFun z p := z (Sum.inl (p.1, (), p.2))
  map_add' z w := by ext p; rfl
  map_smul' c z := by ext p; rfl
def verticalPart
    {G aRow aCol : Type} :
    Word (ZMod 2)
        (LiftedProduct.QubitIndex aRow aCol Unit Unit G) →ₗ[ZMod 2]
      Word (ZMod 2) (aRow × G) where
  toFun z p := z (Sum.inr (p.1, (), p.2))
  map_add' z w := by ext p; rfl
  map_smul' c z := by ext p; rfl
def primitiveTwoChain
    {G aCol : Type}
    (h : Word (ZMod 2) (aCol × G)) :
    Word (ZMod 2) (LiftedProduct.C2Index aCol Unit G) :=
  fun p => h (p.1, p.2.2)
noncomputable def caseTwoRemainder
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G))
    (h : Word (ZMod 2) (aCol × G)) : Word (ZMod 2) (aRow × G) :=
  verticalPart z + tannerAction A h
noncomputable def fibreSum
    {I : Type u} {G : Type v} [Fintype G]
    (z : Word (ZMod 2) (I × G)) : Word (ZMod 2) I :=
  fun i => ∑ g, z (i, g)
def cyclicFibrePrimitive
    {I : Type u} (q : Nat) [NeZero q]
    (z : Word (ZMod 2) (I × Cyclic.CyclicGroup q)) :
    Word (ZMod 2) (I × Cyclic.CyclicGroup q) :=
  fun p =>
    FiberBundle.cycleFiberChainPrimitive q
      (fun a : ZMod q => z (p.1, Multiplicative.ofAdd a)) p.2.toAdd
def normalizeCyclicFibres
    {I : Type u} {G : Type v} [Fintype G]
    (z : Word (ZMod 2) (I × G)) : Word (ZMod 2) (I × G) :=
  fun p => FiberBundle.normalizeBinaryWord (fun g : G => z (p.1, g)) p.2
end QEC.Coding.BalancedProduct.PKDistance


