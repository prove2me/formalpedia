-- Prove2me | Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
-- name    : QEC_Locality_CorrectableRegions_SemanticDistanceErasure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:49:14.728209+00:00
-- url     : https://prove2.me/theorems/55e76710-a53e-4fee-bc8f-c03111542dba
-- title:
--   Semantic Distance Erasure
-- statement:
--   Definitions and structural lemmas for Semantic Distance Erasure, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/SemanticDistanceErasure.lean

import Definitions.Def_QEC_Coding_Stabilizer_Correctability
import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Locality_extendLocal_smul
import Theorems.Thm_QEC_Locality_flipSupport_flipSupport
import Theorems.Thm_QEC_Locality_wordBinaryPauli_apply_ket
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
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_registerFactorization_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
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
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
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
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Locality
open QEC Semantics Coding
open scoped TensorProduct
open PauliSymplectic
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
def embedSelectedWord (S : FiniteSubsystem ι)
    (w : Coding.Word (ZMod 2) S.SelectedCoordinates) : Coding.Word (ZMod 2) ι :=
  fun i => if hi : i ∈ S.selected then w ⟨i, hi⟩ else 0
def selectedCoordinateEmbedding (S : FiniteSubsystem ι) : S.SelectedCoordinates ↪ ι where
  toFun := Subtype.val
  inj' := Subtype.val_injective
@[simp]
theorem embedSelectedWord_apply_mem (S : FiniteSubsystem ι)
    (w : Coding.Word (ZMod 2) S.SelectedCoordinates) {i : ι} (hi : i ∈ S.selected) :
    embedSelectedWord S w i = w ⟨i, hi⟩ := by
  simp [embedSelectedWord, hi]
@[simp]
theorem embedSelectedWord_apply_not_mem (S : FiniteSubsystem ι)
    (w : Coding.Word (ZMod 2) S.SelectedCoordinates) {i : ι} (hi : i ∉ S.selected) :
    embedSelectedWord S w i = 0 := by
  simp [embedSelectedWord, hi]
theorem binarySupport_embedSelectedWord (S : FiniteSubsystem ι)
    (w : Coding.Word (ZMod 2) S.SelectedCoordinates) :
    binarySupport (embedSelectedWord S w) =
      (binarySupport w).map (selectedCoordinateEmbedding S) := by
  ext i
  constructor
  · intro hi
    by_cases his : i ∈ S.selected
    · refine Finset.mem_map.2 ⟨⟨i, his⟩, ?_, rfl⟩
      have hnonzero := (mem_binarySupport (embedSelectedWord S w) i).1 hi
      rw [embedSelectedWord_apply_mem S w his] at hnonzero
      exact (mem_binarySupport w ⟨i, his⟩).2 hnonzero
    · have hzero : embedSelectedWord S w i = 0 :=
        embedSelectedWord_apply_not_mem S w his
      exact False.elim (((mem_binarySupport (embedSelectedWord S w) i).1 hi) hzero)
  · rintro hi
    rcases Finset.mem_map.1 hi with ⟨j, hj, rfl⟩
    rw [mem_binarySupport]
    change embedSelectedWord S w (j : ι) ≠ 0
    rw [embedSelectedWord_apply_mem S w j.property]
    exact (mem_binarySupport w j).1 hj
noncomputable def embeddedLocalPauli (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) : Binary ι :=
  { phase := 0
    vector :=
      { xPart := embedSelectedWord S p.1
        zPart := embedSelectedWord S p.2 } }
@[simp]
theorem xSupport_embeddedLocalPauli (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) :
    xSupport (embeddedLocalPauli S p) =
      (binarySupport p.1).map (selectedCoordinateEmbedding S) := by
  rw [show xSupport (embeddedLocalPauli S p) =
      binarySupport (embedSelectedWord S p.1) by rfl]
  exact binarySupport_embedSelectedWord S p.1
@[simp]
theorem zSupport_embeddedLocalPauli (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) :
    zSupport (embeddedLocalPauli S p) =
      (binarySupport p.2).map (selectedCoordinateEmbedding S) := by
  rw [show zSupport (embeddedLocalPauli S p) =
      binarySupport (embedSelectedWord S p.2) by rfl]
  exact binarySupport_embedSelectedWord S p.2
theorem splitBitstring_flipSupport_embedSelectedWord (S : FiniteSubsystem ι)
    (w : Coding.Word (ZMod 2) S.SelectedCoordinates) (bits : Qubit.Bitstring ι) :
    S.splitBitstring (Qubit.flipSupport (binarySupport (embedSelectedWord S w)) bits) =
      (Qubit.flipSupport (binarySupport w) (S.splitBitstring bits).1,
        (S.splitBitstring bits).2) := by
  apply Prod.ext
  · funext i
    have hvalue : embedSelectedWord S w (i : ι) = w i :=
      embedSelectedWord_apply_mem S w i.property
    simp only [FiniteSubsystem.splitBitstring, Qubit.flipSupport, mem_binarySupport]
    rw [hvalue]
  · funext i
    have hzero : embedSelectedWord S w (i : ι) = 0 :=
      embedSelectedWord_apply_not_mem S w i.property
    simp only [FiniteSubsystem.splitBitstring, Qubit.flipSupport, mem_binarySupport]
    rw [hzero]
    simp
theorem zSupportPhase_embedSelectedWord (S : FiniteSubsystem ι)
    (w : Coding.Word (ZMod 2) S.SelectedCoordinates) (bits : Qubit.Bitstring ι) :
    Qubit.zSupportPhase (binarySupport (embedSelectedWord S w)) bits =
      Qubit.zSupportPhase (binarySupport w) (S.splitBitstring bits).1 := by
  rw [binarySupport_embedSelectedWord]
  simp only [Qubit.zSupportPhase, Finset.prod_map]
  rfl
theorem flipSupport_embedSelectedWord_eq_recombine (S : FiniteSubsystem ι)
    (w : Coding.Word (ZMod 2) S.SelectedCoordinates) (bits : Qubit.Bitstring ι) :
    Qubit.flipSupport (binarySupport (embedSelectedWord S w)) bits =
      S.recombineBitstring
        (Qubit.flipSupport (binarySupport w) (S.splitBitstring bits).1,
          (S.splitBitstring bits).2) := by
  apply S.bitstringFactorization.injective
  change S.splitBitstring (Qubit.flipSupport (binarySupport (embedSelectedWord S w)) bits) =
    S.splitBitstring
      (S.recombineBitstring
        (Qubit.flipSupport (binarySupport w) (S.splitBitstring bits).1,
          (S.splitBitstring bits).2))
  rw [splitBitstring_flipSupport_embedSelectedWord]
  simpa [FiniteSubsystem.bitstringFactorization] using
    (S.bitstringFactorization.apply_symm_apply
      (Qubit.flipSupport (binarySupport w) (S.splitBitstring bits).1,
        (S.splitBitstring bits).2)).symm
theorem registerFactorization_symm_apply_factorizedBasis (S : FiniteSubsystem ι)
    (left : Qubit.Bitstring S.SelectedCoordinates)
    (right : Qubit.Bitstring S.ComplementCoordinates) :
    S.registerFactorization.symm
      (ket left ⊗ₜ[Complex] ket right) =
      ket (S.recombineBitstring (left, right)) := by
  apply S.registerFactorization.toLinearEquiv.injective
  rw [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.apply_symm_apply]
  rw [S.registerFactorization_apply_basis]
  have hsplit : S.splitBitstring (S.recombineBitstring (left, right)) = (left, right) := by
    simpa [FiniteSubsystem.bitstringFactorization] using
      S.bitstringFactorization.apply_symm_apply (left, right)
  rw [hsplit]
theorem toQubitOperator_apply_ket (P : Binary ι) (bits : Qubit.Bitstring ι) :
    toQubitOperator P (ket bits) =
      (binaryPhaseScalar P.phase * Qubit.zSupportPhase (zSupport P) bits) •
        ket (Qubit.flipSupport (xSupport P) bits) := by
  ext output
  rw [toQubitOperator_apply]
  by_cases hout : output = Qubit.flipSupport (xSupport P) bits
  · subst output
    rw [flipSupport_flipSupport]
    simp [ket, EuclideanSpace.basisFun_apply]
  · have hflip : Qubit.flipSupport (xSupport P) output ≠ bits := by
      intro hflip
      apply hout
      calc
        output = Qubit.flipSupport (xSupport P)
            (Qubit.flipSupport (xSupport P) output) :=
          (flipSupport_flipSupport (xSupport P) output).symm
        _ = Qubit.flipSupport (xSupport P) bits := by rw [hflip]
    simp [ket, EuclideanSpace.basisFun_apply, hflip, hout]
theorem toQubitOperator_embeddedLocalPauli_apply_ket (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) (bits : Qubit.Bitstring ι) :
    toQubitOperator (embeddedLocalPauli S p) (ket bits) =
      Qubit.zSupportPhase (binarySupport p.2) (S.splitBitstring bits).1 •
        ket (Qubit.flipSupport (binarySupport (embedSelectedWord S p.1)) bits) := by
  rw [toQubitOperator_apply_ket]
  rw [xSupport_embeddedLocalPauli, zSupport_embeddedLocalPauli]
  rw [← binarySupport_embedSelectedWord S p.2,
    ← binarySupport_embedSelectedWord S p.1]
  rw [zSupportPhase_embedSelectedWord]
  simp [embeddedLocalPauli]
theorem extendLocalToRegister_wordBinaryPauli_apply_ket (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) (bits : Qubit.Bitstring ι) :
    S.extendLocalToRegister (toQubitOperator (wordBinaryPauli S p)) (ket bits) =
      Qubit.zSupportPhase (binarySupport p.2) (S.splitBitstring bits).1 •
        ket (Qubit.flipSupport (binarySupport (embedSelectedWord S p.1)) bits) := by
  change S.registerFactorization.symm
    (S.extendLocal (toQubitOperator (wordBinaryPauli S p))
      (S.registerFactorization (ket bits))) = _
  rw [S.registerFactorization_apply_basis]
  simp only [FiniteSubsystem.extendLocal, TensorProduct.map_tmul, LinearMap.id_apply]
  rw [wordBinaryPauli_apply_ket]
  rw [← TensorProduct.smul_tmul']
  rw [map_smul]
  rw [registerFactorization_symm_apply_factorizedBasis]
  rw [flipSupport_embedSelectedWord_eq_recombine]
theorem toQubitOperator_embeddedLocalPauli_eq_extendLocalToRegister (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) :
    toQubitOperator (embeddedLocalPauli S p) =
      S.extendLocalToRegister (toQubitOperator (wordBinaryPauli S p)) := by
  let b := EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex
  apply LinearMap.ext
  intro psi
  rw [← b.sum_repr' psi, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro bits _
  rw [map_smul, map_smul]
  congr 1
  calc
    toQubitOperator (embeddedLocalPauli S p) (b bits) =
        Qubit.zSupportPhase (binarySupport p.2) (S.splitBitstring bits).1 •
          ket (Qubit.flipSupport (binarySupport (embedSelectedWord S p.1)) bits) := by
      simpa [b] using toQubitOperator_embeddedLocalPauli_apply_ket S p bits
    _ = S.extendLocalToRegister (toQubitOperator (wordBinaryPauli S p)) (b bits) := by
      symm
      simpa [b] using extendLocalToRegister_wordBinaryPauli_apply_ket S p bits
theorem extendLocalToRegister_smul (S : FiniteSubsystem ι)
    (c : Complex) (A : Operator S.selectedSystem) :
    S.extendLocalToRegister (c • A) = c • S.extendLocalToRegister A := by
  unfold FiniteSubsystem.extendLocalToRegister
  rw [extendLocal_smul]
  ext x
  simp [UnitaryTransport.conjOperator]
theorem finiteKrausFamily_ext
    {α : Type*} [Fintype α]
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
    (E F : FiniteKrausFamily α H K)
    (h : E.operator = F.operator) : E = F := by
  cases E
  cases F
  cases h
  rfl
theorem localPauliFamily_operator_eq_extendLocalToRegister (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) :
    (localPauliFamily S).operator p =
      S.extendLocalToRegister
        (localPauliAmplitude S • toQubitOperator (wordBinaryPauli S p)) := by
  rw [FiniteSubsystem.extendLocalToRegister, extendLocal_smul]
  rfl
theorem embeddedLocalPauliKrausFamily_eq_localPauliFamily (S : FiniteSubsystem ι) :
    binaryPauliKrausFamily (embeddedLocalPauli S) (fun _ => localPauliAmplitude S) =
      localPauliFamily S := by
  apply finiteKrausFamily_ext
  funext p
  rw [binaryPauliKrausFamily_operator]
  rw [localPauliFamily_operator_eq_extendLocalToRegister,
    extendLocalToRegister_smul,
    toQubitOperator_embeddedLocalPauli_eq_extendLocalToRegister]
theorem embeddedLocalPauliKrausFamily_complete (S : FiniteSubsystem ι) :
    (binaryPauliKrausFamily (embeddedLocalPauli S)
      (fun _ => localPauliAmplitude S)).Complete := by
  rw [embeddedLocalPauliKrausFamily_eq_localPauliFamily]
  exact localPauliFamily_complete S
end Locality
end QEC


