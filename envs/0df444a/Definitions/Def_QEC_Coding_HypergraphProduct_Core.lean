-- Prove2me | Definitions.Def_QEC_Coding_HypergraphProduct_Core
-- name    : QEC_Coding_HypergraphProduct_Core
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:47:28.696806+00:00
-- url     : https://prove2.me/theorems/a8428639-84ca-4aaf-bc01-a15d89d0bd46
-- title:
--   Core
-- statement:
--   Definitions and structural lemmas for Core, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Core.lean

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.LinearAlgebra.Matrix.ToLin
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
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
namespace QEC.Coding.HypergraphProduct
universe u v
structure Data (F rowOne colOne rowTwo colTwo : Type*) where
  first : Matrix rowOne colOne F
  second : Matrix rowTwo colTwo F
abbrev C0Index (rowOne colTwo : Type*) := rowOne × colTwo
abbrev QubitIndex (rowOne colOne rowTwo colTwo : Type*) :=
  Sum (colOne × colTwo) (rowOne × rowTwo)
abbrev C2Index (colOne rowTwo : Type*) := colOne × rowTwo
def boundary1Matrix
    {F rowOne colOne rowTwo colTwo : Type*}
    [Field F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) :
    Matrix (C0Index rowOne colTwo)
      (QubitIndex rowOne colOne rowTwo colTwo) F :=
  fun (r₁, c₂) q =>
    match q with
    | Sum.inl (c₁, c₂') => if c₂ = c₂' then D.first r₁ c₁ else 0
    | Sum.inr (r₁', r₂) => if r₁ = r₁' then -D.second r₂ c₂ else 0
def boundary2Matrix
    {F rowOne colOne rowTwo colTwo : Type*}
    [Field F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) :
    Matrix (QubitIndex rowOne colOne rowTwo colTwo)
      (C2Index colOne rowTwo) F :=
  fun q (c₁', r₂') =>
    match q with
    | Sum.inl (c₁, c₂) => if c₁ = c₁' then D.second r₂' c₂ else 0
    | Sum.inr (r₁, r₂) => if r₂ = r₂' then D.first r₁ c₁' else 0
@[simp]
theorem boundary1Matrix_inl_apply
    {F rowOne colOne rowTwo colTwo : Type*}
    [Field F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (r₁ : rowOne) (c₂ c₂' : colTwo) (c₁ : colOne) :
    boundary1Matrix D (r₁, c₂) (Sum.inl (c₁, c₂')) =
      if c₂ = c₂' then D.first r₁ c₁ else 0 := by
  rfl
@[simp]
theorem boundary1Matrix_inr_apply
    {F rowOne colOne rowTwo colTwo : Type*}
    [Field F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (r₁ r₁' : rowOne) (r₂ : rowTwo) (c₂ : colTwo) :
    boundary1Matrix D (r₁, c₂) (Sum.inr (r₁', r₂)) =
      if r₁ = r₁' then -D.second r₂ c₂ else 0 := by
  rfl
@[simp]
theorem boundary2Matrix_inl_apply
    {F rowOne colOne rowTwo colTwo : Type*}
    [Field F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (c₁ c₁' : colOne) (r₂ : rowTwo) (c₂ : colTwo) :
    boundary2Matrix D (Sum.inl (c₁, c₂)) (c₁', r₂) =
      if c₁ = c₁' then D.second r₂ c₂ else 0 := by
  rfl
@[simp]
theorem boundary2Matrix_inr_apply
    {F rowOne colOne rowTwo colTwo : Type*}
    [Field F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (r₁ : rowOne) (c₁ : colOne) (r₂ r₂' : rowTwo) :
    boundary2Matrix D (Sum.inr (r₁, r₂)) (c₁, r₂') =
      if r₂ = r₂' then D.first r₁ c₁ else 0 := by
  rfl
theorem boundary1Matrix_mul_boundary2Matrix
    {F rowOne colOne rowTwo colTwo : Type*}
    [Field F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) :
    boundary1Matrix D * boundary2Matrix D = 0 := by
  ext ⟨r₁, c₂⟩ ⟨c₁, r₂⟩
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type, boundary1Matrix_inl_apply,
    boundary1Matrix_inr_apply, boundary2Matrix_inl_apply,
    boundary2Matrix_inr_apply]
  calc
    _ = D.first r₁ c₁ * D.second r₂ c₂ -
        D.second r₂ c₂ * D.first r₁ c₁ := by
      simp [sub_eq_add_neg]
    _ = 0 := by
      rw [mul_comm]
      exact sub_self _
noncomputable def boundary1
    {F rowOne colOne rowTwo colTwo : Type*}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) :
    Word F (QubitIndex rowOne colOne rowTwo colTwo) →ₗ[F]
      Word F (C0Index rowOne colTwo) :=
  Matrix.toLin' (boundary1Matrix D)
noncomputable def boundary2
    {F rowOne colOne rowTwo colTwo : Type*}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) :
    Word F (C2Index colOne rowTwo) →ₗ[F]
      Word F (QubitIndex rowOne colOne rowTwo colTwo) :=
  Matrix.toLin' (boundary2Matrix D)
theorem boundary_squared
    {F rowOne colOne rowTwo colTwo : Type*}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) :
    (boundary1 D).comp (boundary2 D) = 0 := by
  change (Matrix.toLin' (boundary1Matrix D)).comp
    (Matrix.toLin' (boundary2Matrix D)) = 0
  rw [← Matrix.toLin'_mul, boundary1Matrix_mul_boundary2Matrix]
  simp
noncomputable def chainComplex
    {F : Type u} {rowOne colOne rowTwo colTwo : Type v}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) :
    ChainComplexData F
      (Word F (C0Index rowOne colTwo))
      (Word F (QubitIndex rowOne colOne rowTwo colTwo))
      (Word F (C2Index colOne rowTwo)) where
  boundary1 := boundary1 D
  boundary2 := boundary2 D
  boundary_squared := boundary_squared D
noncomputable def binaryCSSCode
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    CSSCode (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo)
      (Semantics.Qubit.QubitRegister
        (QubitIndex rowOne colOne rowTwo colTwo)) :=
  (chainComplex D).binaryCSSCode
end QEC.Coding.HypergraphProduct


