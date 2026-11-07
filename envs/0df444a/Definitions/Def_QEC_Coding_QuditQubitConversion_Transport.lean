-- Prove2me | Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
-- name    : QEC_Coding_QuditQubitConversion_Transport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T11:14:37.600588+00:00
-- url     : https://prove2.me/theorems/23656905-35c2-4492-92cc-cf5a28c5d8ca
-- title:
--   Transport
-- statement:
--   Definitions and structural lemmas for Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/Transport.lean

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
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
noncomputable def why24ComputationalLabelEquiv :
    F1024 ≃ Semantics.Qubit.Bitstring (Fin 10) :=
  f1024SelectedCoordinates.toEquiv.trans
    (PauliSymplectic.bitstringWordEquiv (Fin 10)).symm
abbrev Why24QuditSpace : Type := EuclideanSpace Complex F1024
abbrev Why24QubitSpace : Type := Semantics.Qubit.QubitRegister (Fin 10)
noncomputable def why24QuditComputationalBasis (β : F1024) : Why24QuditSpace :=
  EuclideanSpace.single β 1
noncomputable def why24QubitComputationalBasis
    (bits : Semantics.Qubit.Bitstring (Fin 10)) : Why24QubitSpace :=
  EuclideanSpace.single bits 1
noncomputable def why24QuditQubitBasisIsometry :
    Why24QuditSpace ≃ₗᵢ[Complex] Why24QubitSpace :=
  LinearIsometryEquiv.piLpCongrLeft 2 Complex Complex why24ComputationalLabelEquiv
noncomputable def why24QuditQubitUnitary :
    Semantics.UnitaryTransport Why24QuditSpace Why24QubitSpace where
  toLinearEquiv := why24QuditQubitBasisIsometry.toLinearEquiv
  map_inner := why24QuditQubitBasisIsometry.toLinearIsometry.inner_map_map
@[simp] theorem why24QuditQubitBasisIsometry_apply
    (ψ : Why24QuditSpace) (bits : Semantics.Qubit.Bitstring (Fin 10)) :
    why24QuditQubitBasisIsometry ψ bits =
      ψ (why24ComputationalLabelEquiv.symm bits) :=
  rfl
@[simp] theorem why24QuditQubitBasisIsometry_symm_apply
    (ψ : Why24QubitSpace) (β : F1024) :
    why24QuditQubitBasisIsometry.symm ψ β = ψ (why24ComputationalLabelEquiv β) := by
  have hβ := congrArg (fun φ : Why24QubitSpace => φ (why24ComputationalLabelEquiv β))
    (why24QuditQubitBasisIsometry.apply_symm_apply ψ)
  change why24QuditQubitBasisIsometry
      (why24QuditQubitBasisIsometry.symm ψ) (why24ComputationalLabelEquiv β) =
        ψ (why24ComputationalLabelEquiv β) at hβ
  rw [why24QuditQubitBasisIsometry_apply] at hβ
  simpa only [Equiv.symm_apply_apply] using hβ
noncomputable def why24QuditX (β : F1024) : Semantics.Operator Why24QuditSpace where
  toFun ψ := WithLp.toLp 2 (fun η => ψ (η + β))
  map_add' ψ φ := by
    ext η
    simp
  map_smul' c ψ := by
    ext η
    simp [smul_eq_mul]
@[simp] theorem why24QuditX_apply (β : F1024) (ψ : Why24QuditSpace) (η : F1024) :
    why24QuditX β ψ η = ψ (η + β) :=
  rfl
noncomputable def why24QuditZ (γ : F1024) : Semantics.Operator Why24QuditSpace where
  toFun ψ := WithLp.toLp 2 (fun η =>
    PauliSymplectic.binaryPhaseScalar (Algebra.trace (ZMod 2) F1024 (γ * η)) * ψ η)
  map_add' ψ φ := by
    ext η
    simp [mul_add]
  map_smul' c ψ := by
    ext η
    simp [smul_eq_mul, mul_left_comm]
abbrev Why24FieldPauli : Type := ZMod 4 × F1024 × F1024
abbrev Why24BinaryPauli : Type :=
  ZMod 4 × Word (ZMod 2) (Fin 10) × Word (ZMod 2) (Fin 10)
def why24PauliPhase (a : ZMod 4) : Complex := Complex.I ^ a.val
noncomputable def why24PauliLabelEquiv : Why24FieldPauli ≃ Why24BinaryPauli :=
  Equiv.prodCongr (Equiv.refl (ZMod 4))
    (Equiv.prodCongr f1024SelectedCoordinates.toEquiv f1024SelectedCoordinates.toEquiv)
noncomputable def why24FieldPauliOperator (P : Why24FieldPauli) :
    Semantics.Operator Why24QuditSpace :=
  why24PauliPhase P.1 • (why24QuditX P.2.1 * why24QuditZ P.2.2)
noncomputable def why24BinaryPauliOperator (P : Why24BinaryPauli) :
    Semantics.Operator Why24QubitSpace :=
  why24PauliPhase P.1 •
    (Semantics.Qubit.localXSupport (PauliSymplectic.binarySupport P.2.1) *
      Semantics.Qubit.localZSupport (PauliSymplectic.binarySupport P.2.2))
def Why24IsUnitary {H : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (A : Semantics.Operator H) : Prop :=
  ∀ x y, inner Complex (A x) (A y) = inner Complex x y
def why24FieldNormalizesPaulis (C : Semantics.Operator Why24QuditSpace) : Prop :=
  ∀ P : Why24FieldPauli, ∃ Q : Why24FieldPauli,
    C * why24FieldPauliOperator P * LinearMap.adjoint C = why24FieldPauliOperator Q
def why24BinaryNormalizesPaulis (C : Semantics.Operator Why24QubitSpace) : Prop :=
  ∀ P : Why24BinaryPauli, ∃ Q : Why24BinaryPauli,
    C * why24BinaryPauliOperator P * LinearMap.adjoint C = why24BinaryPauliOperator Q
def Why24FieldClifford (C : Semantics.Operator Why24QuditSpace) : Prop :=
  Why24IsUnitary C ∧ why24FieldNormalizesPaulis C
def Why24BinaryClifford (C : Semantics.Operator Why24QubitSpace) : Prop :=
  Why24IsUnitary C ∧ why24BinaryNormalizesPaulis C
end QEC.Coding


