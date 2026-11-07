-- Prove2me | Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
-- name    : QEC_Coding_QuditQubitConversion_U7Gate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T11:18:06.005636+00:00
-- url     : https://prove2.me/theorems/5e009ba7-ff7a-4955-bb3c-71c40ce7d40d
-- title:
--   U7 Gate
-- statement:
--   Definitions and structural lemmas for U7 Gate, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/U7Gate.lean

import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_why24QuditZ_apply
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
attribute [local simp] QEC.Coding.why24QuditZ_apply
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
namespace QEC.Coding
open scoped BigOperators
noncomputable def why24U (β : F1024) (n : ℕ) : Semantics.Operator Why24QuditSpace where
  toFun ψ := WithLp.toLp 2 (fun η =>
    PauliSymplectic.binaryPhaseScalar
      (Algebra.trace (ZMod 2) F1024 (β * η ^ n)) * ψ η)
  map_add' ψ φ := by
    ext η
    simp [mul_add]
  map_smul' c ψ := by
    ext η
    simp [smul_eq_mul, mul_left_comm]
def why24FrobeniusRootTwo (x : F1024) : F1024 := x ^ 512
def why24FrobeniusRootFour (x : F1024) : F1024 := x ^ 256
abbrev why24UOneSeven : Semantics.Operator Why24QuditSpace := why24U (1 : F1024) 7
def why24FieldPauliMul (P Q : Why24FieldPauli) : Why24FieldPauli :=
  (P.1 + Q.1 + 2 *
      ((Algebra.trace (ZMod 2) F1024 (P.2.2 * Q.2.1)).val : ZMod 4),
    P.2.1 + Q.2.1, P.2.2 + Q.2.2)
def why24FieldPauliDagger (P : Why24FieldPauli) : Why24FieldPauli :=
  (-P.1 + 2 *
      ((Algebra.trace (ZMod 2) F1024 (P.2.1 * P.2.2)).val : ZMod 4),
    P.2.1, P.2.2)
def why24InCliffordHierarchy : Nat → Semantics.Operator Why24QuditSpace → Prop
  | 0, _ => False
  | 1, C => ∃ P : Why24FieldPauli, C = why24FieldPauliOperator P
  | n + 2, C => ∀ P : Why24FieldPauli, ∃ D : Semantics.Operator Why24QuditSpace,
      why24InCliffordHierarchy (n + 1) D ∧
        C * why24FieldPauliOperator P * LinearMap.adjoint C = D
noncomputable def why24QubitUOneSeven : Semantics.Operator Why24QubitSpace :=
  why24QuditQubitUnitary.conjOperator why24UOneSeven
end QEC.Coding


