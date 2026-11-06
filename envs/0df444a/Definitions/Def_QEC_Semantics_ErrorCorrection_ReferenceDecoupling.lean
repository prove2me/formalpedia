-- Prove2me | Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
-- name    : QEC_Semantics_ErrorCorrection_ReferenceDecoupling
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:41:40.070965+00:00
-- url     : https://prove2.me/theorems/f59619fc-a2bc-4214-a23d-745e636f15fc
-- title:
--   Reference Decoupling
-- statement:
--   Definitions and structural lemmas for Reference Decoupling, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_Correctable_unitaryTransport
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_KnillLaflamme_unitaryTransport
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.log2Matrix_apply
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.logMatrix_apply
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
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Semantics
open Classical
open DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v w
namespace DensityOperator
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
structure FinitePurification (rho : DensityOperator H) (Ref : Type u)
    [NormedAddCommGroup Ref] [InnerProductSpace Complex Ref] [FiniteQuantumSystem Ref] where
  vector : CompositeSystem H Ref
  normSq_one : ‖vector‖ ^ 2 = 1
  rightMarginal_eq : (rightMarginal (pureDensity vector normSq_one)).toOperator = rho.toOperator
end DensityOperator
namespace FiniteKrausFamily
variable {H : Type u} {K : Type u} {ι : Type v} {κ : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [Fintype ι] [Fintype κ]
end FiniteKrausFamily
namespace QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
noncomputable def identityTransport (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace Complex H] [FiniteQuantumSystem H] : UnitaryTransport H H where
  toLinearEquiv := LinearEquiv.refl Complex H
  map_inner := by intro x y; rfl
noncomputable def erasureFactorizedKraus (S : QuditSubsystem q) :
    FiniteKrausFamily (Fin (Module.finrank Complex S.selectedSystem))
      S.factorizedSystem S.complementSystem where
  operator := fun a => LinearMap.adjoint
    (S.prepareFactorizedBranch ((stdOrthonormalBasis Complex S.selectedSystem) a))
noncomputable def erasureKraus (S : QuditSubsystem q) :
    FiniteKrausFamily (Fin (Module.finrank Complex S.selectedSystem))
      (Qudit.QuditRegister q) S.complementSystem :=
  S.erasureFactorizedKraus.unitaryTransport
      S.registerFactorization.symm (identityTransport S.complementSystem)
@[simp]
theorem erasureKraus_operator (S : QuditSubsystem q)
    (a : Fin (Module.finrank Complex S.selectedSystem)) :
    (S.erasureKraus).operator a =
      (LinearMap.adjoint
        (S.prepareFactorizedBranch ((stdOrthonormalBasis Complex S.selectedSystem) a))).comp
        S.registerFactorization.toLinearEquiv.toLinearMap := by
  rfl
section TensorReordering
variable (S : QuditSubsystem q)
variable (Ref : Type u) [NormedAddCommGroup Ref] [InnerProductSpace Complex Ref]
    [FiniteQuantumSystem Ref]
noncomputable def selectedReferenceReordering :
    UnitaryTransport
      (CompositeSystem S.factorizedSystem Ref)
      (CompositeSystem (CompositeSystem S.selectedSystem Ref) S.complementSystem) := by
  let e1 := TensorProduct.assocIsometry Complex S.selectedSystem S.complementSystem Ref
  let e2 := (TensorProduct.commIsometry Complex S.complementSystem Ref).lTensor
    S.selectedSystem
  let e3 := (TensorProduct.assocIsometry Complex S.selectedSystem Ref
    S.complementSystem).symm
  let e := e1.trans (e2.trans e3)
  exact
    { toLinearEquiv := e.toLinearEquiv
      map_inner := by
        intro x y
        simpa [e, e1, e2, e3] using e.inner_map_map x y }
noncomputable def registerFactorizationWithReference :
    UnitaryTransport
      (CompositeSystem (Qudit.QuditRegister q) Ref)
      (CompositeSystem S.factorizedSystem Ref) := by
  let e := S.registerFactorization.toLinearIsometryEquiv.rTensor Ref
  exact
    { toLinearEquiv := e.toLinearEquiv
      map_inner := by
        intro x y
        change inner Complex (e x) (e y) = inner Complex x y
        exact e.inner_map_map x y }
noncomputable def selectedReferenceTransport :
    UnitaryTransport
      (CompositeSystem (Qudit.QuditRegister q) Ref)
      (CompositeSystem (CompositeSystem S.selectedSystem Ref) S.complementSystem) := by
  let e := (S.registerFactorizationWithReference Ref).toLinearIsometryEquiv.trans
    (S.selectedReferenceReordering Ref).toLinearIsometryEquiv
  exact
    { toLinearEquiv := e.toLinearEquiv
      map_inner := by
        intro x y
        change inner Complex (e x) (e y) = inner Complex x y
        exact e.inner_map_map x y }
noncomputable def selectedReferenceMarginal
  (omega : DensityOperator (CompositeSystem (Qudit.QuditRegister q) Ref)) :
    DensityOperator (CompositeSystem S.selectedSystem Ref) :=
  (partialTraceRightRaw_cptp (CompositeSystem S.selectedSystem Ref) S.complementSystem).mapDensity
    ((QuantumChannel.unitaryConj
      (S.selectedReferenceTransport Ref)).mapDensity omega)
end TensorReordering
noncomputable def selectedReferenceRaw (S : QuditSubsystem q)
    (Ref : Type u) [NormedAddCommGroup Ref] [InnerProductSpace Complex Ref]
    [FiniteQuantumSystem Ref] :
    Operator (CompositeSystem (Qudit.QuditRegister q) Ref) →ₗ[Complex]
      Operator (CompositeSystem S.selectedSystem Ref) :=
  (partialTraceRightRaw (CompositeSystem S.selectedSystem Ref) S.complementSystem).comp
    (S.selectedReferenceTransport Ref).conjOperatorLinearMap
end QuditSubsystem
end Semantics
end QEC


