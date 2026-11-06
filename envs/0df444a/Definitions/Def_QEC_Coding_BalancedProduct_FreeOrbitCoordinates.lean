-- Prove2me | Definitions.Def_QEC_Coding_BalancedProduct_FreeOrbitCoordinates
-- name    : QEC_Coding_BalancedProduct_FreeOrbitCoordinates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:37:53.369559+00:00
-- url     : https://prove2.me/theorems/0247b7fe-0807-4ca3-8e9f-8c87a7e3c1db
-- title:
--   Free Orbit Coordinates
-- statement:
--   Definitions and structural lemmas for Free Orbit Coordinates, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/FreeOrbitCoordinates.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Mathlib.GroupTheory.GroupAction.Quotient
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
noncomputable section
namespace QEC.Coding.BalancedProduct.FreeOrbitCoordinates
universe u v
variable (G : Type u) (X : Type v) [Group G] [MulAction G X]
abbrev OrbitIndex := Quotient (MulAction.orbitRel G X)
def orbitOf (x : X) : OrbitIndex G X := Quotient.mk'' x
def orbitRep (o : OrbitIndex G X) : X := Quotient.out o
theorem exists_smul_orbitRep_eq (x : X) :
    ∃ g : G, g • orbitRep G X (orbitOf G X x) = x := by
  have hout :
      Quotient.mk'' (orbitRep G X (orbitOf G X x)) = orbitOf G X x :=
    Quotient.out_eq' _
  have hrel :
      MulAction.orbitRel G X (orbitRep G X (orbitOf G X x)) x :=
    Quotient.eq''.mp hout
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  rcases hrel with ⟨g, hg⟩
  exact ⟨g⁻¹, by simpa using (congrArg (fun y => g⁻¹ • y) hg).symm⟩
def groupCoordinate [IsCancelSMul G X] (x : X) : G :=
  Classical.choose (exists_smul_orbitRep_eq G X x)
@[simp]
theorem groupCoordinate_smul_orbitRep [IsCancelSMul G X] (x : X) :
    groupCoordinate G X x • orbitRep G X (orbitOf G X x) = x :=
  Classical.choose_spec (exists_smul_orbitRep_eq G X x)
@[simp]
theorem orbitOf_smul (g : G) (x : X) :
    orbitOf G X (g • x) = orbitOf G X x := by
  apply Quotient.sound
  exact (MulAction.orbitRel_apply).2 (MulAction.mem_orbit x g)
@[simp]
theorem groupCoordinate_smul [IsCancelSMul G X] (g : G) (x : X) :
    groupCoordinate G X (g • x) = g * groupCoordinate G X x := by
  apply IsCancelSMul.right_cancel _ _ (orbitRep G X (orbitOf G X x))
  rw [mul_smul]
  rw [groupCoordinate_smul_orbitRep]
  simpa using groupCoordinate_smul_orbitRep G X (g • x)
def freeOrbitEquiv [IsCancelSMul G X] :
    X ≃ OrbitIndex G X × G where
  toFun x := (orbitOf G X x, groupCoordinate G X x)
  invFun og := og.2 • orbitRep G X og.1
  left_inv x := groupCoordinate_smul_orbitRep G X x
  right_inv og := by
    rcases og with ⟨o, g⟩
    apply Prod.ext
    · change orbitOf G X (g • orbitRep G X o) = o
      rw [orbitOf_smul]
      exact Quotient.out_eq' o
    · change groupCoordinate G X (g • orbitRep G X o) = g
      rw [groupCoordinate_smul]
      have hcoord : groupCoordinate G X (orbitRep G X o) = 1 := by
        apply IsCancelSMul.right_cancel _ _ (orbitRep G X o)
        have hs := groupCoordinate_smul_orbitRep G X (orbitRep G X o)
        have horbit : orbitOf G X (orbitRep G X o) = o := Quotient.out_eq' o
        rw [horbit] at hs
        simpa using hs
      simp [hcoord]
section MatrixCompression
variable {F : Type*} [Semiring F]
variable {R : Type*} {C : Type*}
variable [MulAction G R] [MulAction G C]
variable [IsCancelSMul G R] [IsCancelSMul G C]
variable [Fintype G]
def groupAlgebraMatrix
    (P : Matrix R C F) :
    Matrix (OrbitIndex G R) (OrbitIndex G C) (MonoidAlgebra F G) :=
  fun ro co => MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun h =>
    P (h • orbitRep G R ro) (orbitRep G C co))
end MatrixCompression
end QEC.Coding.BalancedProduct.FreeOrbitCoordinates


