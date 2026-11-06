-- Prove2me | Definitions.Def_QEC_Coding_Stabilizer_Detectability
-- name    : QEC_Coding_Stabilizer_Detectability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:42:43.740241+00:00
-- url     : https://prove2.me/theorems/4f37ee3b-9515-4435-8043-0d96e2fc53ae
-- title:
--   Detectability
-- statement:
--   Definitions and structural lemmas for Detectability, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Detectability.lean

import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Coding_Stabilizer_Symplectic
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_eq_phase_smul_id_of_vector_eq_zero
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
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
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
namespace QEC
namespace Coding
universe u
namespace PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] in
/-- Binary Pauli multiplication is associative in the stored sign convention. -/
theorem binaryMul_assoc (P Q R : Binary ι) :
    binaryMul (binaryMul P Q) R = binaryMul P (binaryMul Q R) := by
  rcases P with ⟨p, ⟨px, pz⟩⟩
  rcases Q with ⟨q, ⟨qx, qz⟩⟩
  rcases R with ⟨r, ⟨rx, rz⟩⟩
  simp [binaryMul, binaryMulPhase]
  constructor
  · simp_rw [mul_add, add_mul]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    abel
  · exact ⟨add_assoc _ _ _, add_assoc _ _ _⟩
omit [DecidableEq ι] in
/-- The named binary dagger is also a right inverse. -/
@[simp] theorem binaryMul_binaryDagger_right (P : Binary ι) :
    binaryMul P (binaryDagger P) = binaryOne := by
  rcases P with ⟨phase, ⟨x, z⟩⟩
  have hbit_add_self (a : ZMod 2) : a + a = 0 := by
    by_cases ha : a = 0
    · simp [ha]
    · have ha1 : a = 1 := zmod_two_eq_one_of_ne_zero ha
      subst a
      decide
  simp [binaryMul, binaryMulPhase, binaryDagger, binaryDaggerPhase, binaryOne]
  constructor
  · let s : ZMod 2 := ∑ i, x i * z i
    change phase + (phase + s) + s = 0
    calc
      phase + (phase + s) + s = (phase + phase) + (s + s) := by abel
      _ = 0 := by simp [hbit_add_self]
  constructor
  · funext i
    exact hbit_add_self (x i)
  · funext i
    exact hbit_add_self (z i)
@[simp] theorem toQubitOperator_binarySign (p : ZMod 2) :
    toQubitOperator (binarySign (ι := ι) p) =
      binaryPhaseScalar p •
        (1 : Semantics.Operator (Semantics.Qubit.QubitRegister ι)) := by
  exact toQubitOperator_eq_phase_smul_id_of_vector_eq_zero (by rfl) (by rfl)
end PauliSymplectic
namespace StabilizerCode
open PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
theorem binaryOne_mem_generatedGroup
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι)) :
    binaryOne (ι := ι) ∈ Q.generatedGroup := by
  classical
  letI : Fintype {P : Binary ι // P ∈ Q.stabilizers} := Fintype.ofFinite _
  unfold generatedGroup
  simp only [Set.mem_setOf_eq]
  exact GeneratedStabilizer.one
theorem binaryMul_mem_generatedGroup
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    {P R : Binary ι} (hP : P ∈ Q.generatedGroup) (hR : R ∈ Q.generatedGroup) :
    binaryMul P R ∈ Q.generatedGroup := by
  classical
  letI : Fintype {S : Binary ι // S ∈ Q.stabilizers} := Fintype.ofFinite _
  unfold generatedGroup at hP hR ⊢
  simp only [Set.mem_setOf_eq] at hP hR ⊢
  exact GeneratedStabilizer.mul hP hR
def generatedVectorSubspace
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι)) :
    Submodule (ZMod 2) (SymplecticVector (ZMod 2) ι) where
  carrier := {v | ∃ P, P ∈ Q.generatedGroup ∧ P.vector = v}
  zero_mem' := by
    exact ⟨binaryOne, binaryOne_mem_generatedGroup Q, rfl⟩
  add_mem' := by
    rintro _ _ ⟨P, hP, rfl⟩ ⟨R, hR, rfl⟩
    exact ⟨binaryMul P R, binaryMul_mem_generatedGroup Q hP hR, rfl⟩
  smul_mem' := by
    rintro c _ ⟨P, hP, rfl⟩
    by_cases hc : c = 0
    · subst c
      refine ⟨binaryOne, binaryOne_mem_generatedGroup Q, ?_⟩
      rw [zero_smul]
      apply (SymplecticVector.toProdLinearEquiv (F := ZMod 2) (ι := ι)).injective
      simp [SymplecticVector.toProdLinearEquiv, SymplecticVector.toProdEquiv, binaryOne]
    · have hc1 : c = 1 := zmod_two_eq_one_of_ne_zero hc
      subst c
      exact ⟨P, hP, by simp⟩
def InGeneratedGroupUpToSign
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    (E : Binary ι) : Prop :=
  ∃ S, S ∈ Q.generatedGroup ∧ BinaryUpToSign E S
def InBinaryNormalizer
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    (E : Binary ι) : Prop :=
  ∀ S, S ∈ Q.generatedGroup → Commutes E S
theorem binaryDagger_mem_generatedGroup
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    {S : Binary ι} (hS : S ∈ Q.generatedGroup) :
    binaryDagger S ∈ Q.generatedGroup := by
  classical
  unfold generatedGroup at hS ⊢
  simp only [Set.mem_setOf_eq] at hS ⊢
  exact @GeneratedStabilizer.dagger ι _
    {P : Binary ι // P ∈ Q.stabilizers} (Fintype.ofFinite _)
    (fun check => check.1) S hS
def GeneratedGroupElement
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι)) :=
  {P : Binary ι // P ∈ Q.generatedGroup}
instance instFiniteGeneratedGroupElement
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι)) :
    Finite Q.GeneratedGroupElement :=
  Finite.of_injective Subtype.val Subtype.val_injective
noncomputable instance instFintypeGeneratedGroupElement
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι)) :
    Fintype Q.GeneratedGroupElement :=
  Fintype.ofFinite _
noncomputable instance instGroupGeneratedGroupElement
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι)) :
    Group Q.GeneratedGroupElement where
  mul P R := ⟨binaryMul P.1 R.1, binaryMul_mem_generatedGroup Q P.2 R.2⟩
  one := ⟨binaryOne, binaryOne_mem_generatedGroup Q⟩
  inv P := ⟨binaryDagger P.1, binaryDagger_mem_generatedGroup Q P.2⟩
  mul_assoc P R S := Subtype.ext (binaryMul_assoc P.1 R.1 S.1)
  one_mul P := Subtype.ext (binaryMul_binaryOne_left P.1)
  mul_one P := Subtype.ext (binaryMul_binaryOne_right P.1)
  inv_mul_cancel P := Subtype.ext (binaryMul_binaryDagger_left P.1)
def stabilizerAverage
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι)) :
    Semantics.Operator (Semantics.Qubit.QubitRegister ι) :=
  ∑ P : Q.GeneratedGroupElement, toQubitOperator P.1
end StabilizerCode
end Coding
end QEC


