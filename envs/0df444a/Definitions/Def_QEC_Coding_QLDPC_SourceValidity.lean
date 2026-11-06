-- Prove2me | Definitions.Def_QEC_Coding_QLDPC_SourceValidity
-- name    : QEC_Coding_QLDPC_SourceValidity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:41:30.410225+00:00
-- url     : https://prove2.me/theorems/b9a82f85-d348-4724-981f-55199a5edc91
-- title:
--   Source Validity
-- statement:
--   Definitions and structural lemmas for Source Validity, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/SourceValidity.lean

import Definitions.Def_QEC_Coding_QLDPC_Core
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_adjoint_comp_self
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_binaryDagger
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_binaryMul
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_one
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
namespace QEC
namespace Coding
open Classical
universe u w
namespace PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
theorem mem_generatedGroup_of_mem_stabilizers
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    {P : Binary ι} (hP : P ∈ Q.stabilizers) :
    P ∈ Q.generatedGroup := by
  classical
  unfold StabilizerCode.generatedGroup
  simp only [Set.mem_setOf_eq]
  exact @GeneratedStabilizer.generator ι _
    {S : Binary ι // S ∈ Q.stabilizers} (Fintype.ofFinite _)
    (fun check => check.1) ⟨P, hP⟩
theorem fixed_generatedGroup_iff_fixed_stabilizers
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    (ψ : Semantics.Qubit.QubitRegister ι) :
    (∀ P, P ∈ Q.generatedGroup → toQubitOperator P ψ = ψ) ↔
      ∀ P, P ∈ Q.stabilizers → toQubitOperator P ψ = ψ := by
  constructor
  · intro h P hP
    exact h P (mem_generatedGroup_of_mem_stabilizers Q hP)
  · intro h P hP
    unfold StabilizerCode.generatedGroup at hP
    simp only [Set.mem_setOf_eq] at hP
    induction hP with
    | one => simp [toQubitOperator_one]
    | generator check => exact h check.1 check.2
    | @mul P R hP hR ihP ihR =>
        rw [toQubitOperator_binaryMul, Module.End.mul_apply, ihR, ihP]
    | @dagger P hP ihP =>
        rw [toQubitOperator_binaryDagger]
        calc
          LinearMap.adjoint (toQubitOperator P) ψ =
              LinearMap.adjoint (toQubitOperator P) (toQubitOperator P ψ) := by rw [ihP]
          _ = ((LinearMap.adjoint (toQubitOperator P)).comp (toQubitOperator P)) ψ := rfl
          _ = ψ := by rw [toQubitOperator_adjoint_comp_self]; rfl
theorem binaryCSSStabilizerCodeOfDualLe_generatedGroup_components
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {P : Binary ι}
    (hP : P ∈ (binaryCSSStabilizerCodeOfDualLe xCode zCode hdual).generatedGroup) :
    P.phase = 0 ∧ P.vector.xPart ∈ xCode.carrier ∧
      P.vector.zPart ∈ zCode.carrier := by
  classical
  unfold StabilizerCode.generatedGroup at hP
  simp only [Set.mem_setOf_eq] at hP
  induction hP with
  | one =>
      exact ⟨rfl, xCode.carrier.zero_mem, zCode.carrier.zero_mem⟩
  | generator check =>
      have hcheck : check.1 ∈ binaryCSSCheckSet xCode zCode := by
        change check.1 ∈ binaryCSSCheckSet xCode zCode
        exact check.2
      rcases hcheck with ⟨x, hx, hcheck⟩ | ⟨z, hz, hcheck⟩
      · rw [hcheck]
        exact ⟨rfl, hx, zCode.carrier.zero_mem⟩
      · rw [hcheck]
        exact ⟨rfl, xCode.carrier.zero_mem, hz⟩
  | @mul P R hP hR ihP ihR =>
      rcases ihP with ⟨hPphase, hPx, hPz⟩
      rcases ihR with ⟨hRphase, hRx, hRz⟩
      have hcross :
          (∑ i, R.vector.xPart i * P.vector.zPart i) = (0 : ZMod 2) := by
        simpa [wordPairing_apply, dotProduct] using
          xCode.dual_orthogonal hRx (hdual hPz)
      refine ⟨?_, ?_, ?_⟩
      · simp [binaryMul, binaryMulPhase, hPphase, hRphase, hcross]
      · simpa [binaryMul] using xCode.carrier.add_mem hPx hRx
      · simpa [binaryMul] using zCode.carrier.add_mem hPz hRz
  | @dagger P hP ihP =>
      rcases ihP with ⟨hphase, hx, hz⟩
      have hcross :
          (∑ i, P.vector.xPart i * P.vector.zPart i) = (0 : ZMod 2) := by
        simpa [wordPairing_apply, dotProduct] using
          xCode.dual_orthogonal hx (hdual hz)
      refine ⟨?_, ?_, ?_⟩
      · simp [binaryDagger, binaryDaggerPhase, hphase, hcross]
      · simpa [binaryDagger] using hx
      · simpa [binaryDagger] using hz
theorem binaryCSSStabilizerCodeOfDualLe_generatedGroup_phase_eq_zero
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {P : Binary ι}
    (hP : P ∈ (binaryCSSStabilizerCodeOfDualLe xCode zCode hdual).generatedGroup) :
    P.phase = 0 :=
  (binaryCSSStabilizerCodeOfDualLe_generatedGroup_components
    xCode zCode hdual hP).1
theorem binarySign_one_not_mem_binaryCSSStabilizerCodeOfDualLe_generatedGroup
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    binarySign (ι := ι) 1 ∉
      (binaryCSSStabilizerCodeOfDualLe xCode zCode hdual).generatedGroup := by
  intro hsign
  have hphase :=
    binaryCSSStabilizerCodeOfDualLe_generatedGroup_phase_eq_zero
      xCode zCode hdual hsign
  norm_num [binarySign] at hphase
theorem binaryCSSStabilizerCodeOfDualLe_isSourceValidBinary
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    (binaryCSSStabilizerCodeOfDualLe xCode zCode hdual).IsSourceValidBinary := by
  let Q := binaryCSSStabilizerCodeOfDualLe xCode zCode hdual
  constructor
  · exact binarySign_one_not_mem_binaryCSSStabilizerCodeOfDualLe_generatedGroup
      xCode zCode hdual
  · intro ψ
    calc
      ψ ∈ Q.code.carrier ↔
          ∀ P, P ∈ Q.stabilizers → toQubitOperator P ψ = ψ := by
            simp [Q, binaryCSSStabilizerCodeOfDualLe]
      _ ↔ ∀ P, P ∈ Q.generatedGroup → toQubitOperator P ψ = ψ :=
        (fixed_generatedGroup_iff_fixed_stabilizers Q ψ).symm
end PauliSymplectic
namespace ChainComplexData
open PauliSymplectic
theorem binaryCSSCode_stabilizer_isSourceValidBinary
    {ι κ C2 : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [AddCommGroup C2] [Module (ZMod 2) C2]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) κ) (Word (ZMod 2) ι) C2) :
    (K.binaryCSSCode).stabilizer.IsSourceValidBinary := by
  simpa [binaryCSSCode] using
    binaryCSSStabilizerCodeOfDualLe_isSourceValidBinary
      K.firstCoboundaryCheckCode K.middleBoundaryCode
      K.middleBoundaryCode_le_firstCoboundaryCheckCode_dual
noncomputable def binaryCSSSourceValidStabilizer
    {ι κ C2 : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [AddCommGroup C2] [Module (ZMod 2) C2]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) κ) (Word (ZMod 2) ι) C2) :
    StabilizerCode.SourceValidBinary ι :=
  ⟨(K.binaryCSSCode).stabilizer,
    K.binaryCSSCode_stabilizer_isSourceValidBinary⟩
end ChainComplexData
end Coding
namespace QLDPC
open scoped Classical
universe u w
end QLDPC
end QEC


