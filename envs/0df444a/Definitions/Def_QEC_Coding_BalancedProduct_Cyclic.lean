-- Prove2me | Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
-- name    : QEC_Coding_BalancedProduct_Cyclic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:03:48.269203+00:00
-- url     : https://prove2.me/theorems/af94c92c-8384-4860-9d68-2b44e9b57a9a
-- title:
--   Cyclic
-- statement:
--   Definitions and structural lemmas for Cyclic, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/Cyclic.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_secondZeroExtension
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
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_secondZeroExtension
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
namespace QEC.Coding.BalancedProduct.Cyclic
universe u v
abbrev CyclicGroup (q : Nat) := Multiplicative (ZMod q)
def cyclicGenerator (q : Nat) : CyclicGroup q :=
  Multiplicative.ofAdd (1 : ZMod q)
def finCyclicEquiv (q : Nat) [NeZero q] : Fin q ≃ CyclicGroup q where
  toFun k := Multiplicative.ofAdd (ZMod.finEquiv q k)
  invFun g := (ZMod.finEquiv q).symm g.toAdd
  left_inv k := by simp
  right_inv g := by simp
def finCyclicInvEquiv (q : Nat) [NeZero q] : Fin q ≃ CyclicGroup q :=
  (finCyclicEquiv q).trans (Equiv.inv (CyclicGroup q))
noncomputable def cyclicBoundaryElement {G : Type u} [Group G] (x : G) :
    MonoidAlgebra (ZMod 2) G :=
  MonoidAlgebra.single 1 1 + MonoidAlgebra.single x 1
noncomputable def cyclicBoundaryMatrix {G : Type u} [Group G] (x : G) :
    Matrix Unit Unit (MonoidAlgebra (ZMod 2) G) :=
  fun _ _ => cyclicBoundaryElement x
noncomputable def liftedProductData
    {G : Type u} {aRow aCol : Type v} [Group G]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G) :
    LiftedProduct.Data (ZMod 2) G aRow aCol Unit Unit where
  A := A
  B := cyclicBoundaryMatrix x
noncomputable def data
    {aRow aCol : Type} (q : Nat)
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) (CyclicGroup q))) :
    LiftedProduct.Data (ZMod 2) (CyclicGroup q) aRow aCol Unit Unit :=
  liftedProductData (G := CyclicGroup q) (aRow := aRow) (aCol := aCol)
    A (cyclicGenerator q)
noncomputable abbrev chainComplex
    {aRow aCol : Type} [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) (CyclicGroup q))) :=
  LiftedProduct.chainComplex (data (aRow := aRow) (aCol := aCol) q A)
end QEC.Coding.BalancedProduct.Cyclic


