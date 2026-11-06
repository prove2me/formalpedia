-- Prove2me | Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
-- name    : QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:36:41.390323+00:00
-- url     : https://prove2.me/theorems/2dfd48c8-c872-414c-a59c-43be3f92aa0f
-- title:
--   Local Pauli Erasure Transfer
-- statement:
--   Definitions and structural lemmas for Local Pauli Erasure Transfer, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_adjoint_comp_self
import Theorems.Thm_QEC_Semantics_Correctable_unitaryTransport
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_scale_complete_of_adjoint_square_sum
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
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
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
namespace QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
abbrev LocalPauliIndex (S : FiniteSubsystem ι) : Type u :=
  Qubit.Bitstring S.SelectedCoordinates × Qubit.Bitstring S.SelectedCoordinates
noncomputable def localPauliAmplitude (S : FiniteSubsystem ι) : Complex :=
  (Fintype.card (Qubit.Bitstring S.SelectedCoordinates) : Complex)⁻¹
noncomputable abbrev ket {α : Type u} [Fintype α] [DecidableEq α]
    (bits : Qubit.Bitstring α) :
    Qubit.QubitRegister α :=
  EuclideanSpace.basisFun (Qubit.Bitstring α) Complex bits
noncomputable def tensorRight (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (k : K) : H →ₗ[Complex] CompositeSystem H K :=
  (TensorProduct.mk Complex H K).flip k
noncomputable def rightCompression (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {β : Type u} [Fintype β] (b : OrthonormalBasis β Complex K) :
    Operator (CompositeSystem H K) →ₗ[Complex] Operator H :=
  ∑ i : β,
    let S := tensorRight H K (b i)
    { toFun := fun A => (LinearMap.adjoint S).comp (A.comp S)
      map_add' := by
        intro A B
        ext x
        simp [LinearMap.comp_apply, map_add]
      map_smul' := by
        intro c A
        ext x
        simp [LinearMap.comp_apply] }
noncomputable def tensorLeft (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (h : H) : K →ₗ[Complex] CompositeSystem H K :=
  TensorProduct.mk Complex H K h
theorem tensorLeft_adjoint_tmul (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (h h' : H) (k : K) :
    LinearMap.adjoint (tensorLeft H K h) (h' ⊗ₜ[Complex] k) =
      (inner Complex h h') • k := by
  apply (ext_iff_inner_left Complex).mpr
  intro x
  rw [LinearMap.adjoint_inner_right]
  simp [tensorLeft, TensorProduct.inner_tmul, inner_smul_right]
theorem inner_ket_self {α : Type u} [Fintype α] [DecidableEq α]
    (bits : Qubit.Bitstring α) :
    inner Complex (ket bits) (ket bits) = 1 := by
  simp [ket]
theorem tensorLeft_ket_adjoint_comp_self (S : FiniteSubsystem ι)
    (bits : Qubit.Bitstring S.SelectedCoordinates) :
    (LinearMap.adjoint (tensorLeft S.selectedSystem S.complementSystem (ket bits))).comp
      (tensorLeft S.selectedSystem S.complementSystem (ket bits)) = 1 := by
  apply LinearMap.ext
  intro k
  change LinearMap.adjoint
      (tensorLeft S.selectedSystem S.complementSystem (ket bits))
      ((ket bits) ⊗ₜ[Complex] k) = k
  rw [tensorLeft_adjoint_tmul, inner_ket_self]
  simp
noncomputable def refillUnnormalizedFamilyFactorized (S : FiniteSubsystem ι) :
    FiniteKrausFamily (LocalPauliIndex S)
      S.complementSystem S.factorizedSystem where
  operator p := tensorLeft S.selectedSystem S.complementSystem (ket p.1)
noncomputable def refillFamilyFactorized (S : FiniteSubsystem ι) :
    FiniteKrausFamily (LocalPauliIndex S)
      S.complementSystem S.factorizedSystem :=
  (refillUnnormalizedFamilyFactorized S).scale (fun _ => localPauliAmplitude S)
theorem refillFamilyFactorized_complete (S : FiniteSubsystem ι) :
    (refillFamilyFactorized S).Complete := by
  apply FiniteKrausFamily.scale_complete_of_adjoint_square_sum
    (refillUnnormalizedFamilyFactorized S) (fun _ => localPauliAmplitude S)
  simp only [refillUnnormalizedFamilyFactorized]
  rw [show (∑ p : LocalPauliIndex S,
      (star (localPauliAmplitude S) * localPauliAmplitude S) •
        ((LinearMap.adjoint
          (tensorLeft S.selectedSystem S.complementSystem (ket p.1))).comp
          (tensorLeft S.selectedSystem S.complementSystem (ket p.1)))) =
      ∑ p : LocalPauliIndex S,
        (star (localPauliAmplitude S) * localPauliAmplitude S) •
          (1 : Operator S.complementSystem) by
        apply Finset.sum_congr rfl
        intro p _
        rw [tensorLeft_ket_adjoint_comp_self]
    ]
  rw [Finset.sum_const, Finset.card_univ]
  let d : Complex := Fintype.card (Qubit.Bitstring S.SelectedCoordinates)
  have hd : d ≠ 0 := by
    dsimp [d]
    exact_mod_cast Fintype.card_ne_zero
  have hcard : (Fintype.card (LocalPauliIndex S) : Complex) = d * d := by
    simp [LocalPauliIndex, d, Fintype.card_prod]
  have hstar_amplitude : star (localPauliAmplitude S) = localPauliAmplitude S := by
    unfold localPauliAmplitude
    simp
  have hscalar : (Fintype.card (LocalPauliIndex S) : Complex) *
      (star (localPauliAmplitude S) * localPauliAmplitude S) = 1 := by
    rw [hcard, hstar_amplitude]
    change (d * d) * (d⁻¹ * d⁻¹) = 1
    field_simp
  rw [← Nat.cast_smul_eq_nsmul Complex]
  rw [smul_smul, hscalar, one_smul]
noncomputable def refillFactorized (S : FiniteSubsystem ι) :
    QuantumChannel S.complementSystem S.factorizedSystem :=
  (refillFamilyFactorized S).toQuantumChannel (refillFamilyFactorized_complete S)
noncomputable def leftCompression (S : FiniteSubsystem ι) :
    Operator S.factorizedSystem →ₗ[Complex] Operator S.complementSystem :=
  ∑ h : Qubit.Bitstring S.SelectedCoordinates,
    let L := tensorLeft S.selectedSystem S.complementSystem (ket h)
    { toFun := fun A => (LinearMap.adjoint L).comp (A.comp L)
      map_add' := by
        intro A B
        ext x
        simp [LinearMap.comp_apply, map_add]
      map_smul' := by
        intro c A
        ext x
        simp [LinearMap.comp_apply] }
noncomputable def binaryPairingCharacter {α : Type u} [Fintype α] [DecidableEq α]
    (r : Coding.Word (ZMod 2) α) :
    AddChar (Coding.Word (ZMod 2) α) Complex where
  toFun z := PauliSymplectic.binaryPhaseScalar
    (Coding.wordPairing (F := ZMod 2) (ι := α) z r)
  map_zero_eq_one' := by
    simp [PauliSymplectic.binaryPhaseScalar]
  map_add_eq_mul' z z' := by
    rw [show Coding.wordPairing (F := ZMod 2) (ι := α) (z + z') r =
          Coding.wordPairing (F := ZMod 2) (ι := α) z r +
          Coding.wordPairing (F := ZMod 2) (ι := α) z' r by
          rw [(Coding.wordPairing (F := ZMod 2) (ι := α)).map_add z z']
          rfl,
      PauliSymplectic.binaryPhaseScalar_add]
noncomputable def factorizedBasis (S : FiniteSubsystem ι) :
    OrthonormalBasis
      (Qubit.Bitstring S.SelectedCoordinates × Qubit.Bitstring S.ComplementCoordinates)
      Complex S.factorizedSystem :=
  (EuclideanSpace.basisFun (Qubit.Bitstring S.SelectedCoordinates) Complex).tensorProduct
    (EuclideanSpace.basisFun (Qubit.Bitstring S.ComplementCoordinates) Complex)
abbrev LocalPauliWordIndex (S : FiniteSubsystem ι) : Type u :=
  Coding.Word (ZMod 2) S.SelectedCoordinates × Coding.Word (ZMod 2) S.SelectedCoordinates
noncomputable def wordBinaryPauli (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) : PauliSymplectic.Binary S.SelectedCoordinates :=
  { phase := 0
    vector := { xPart := p.1, zPart := p.2 } }
noncomputable def wordPauliOperatorFactorized (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) : Operator S.factorizedSystem :=
  TensorProduct.map (PauliSymplectic.toQubitOperator (wordBinaryPauli S p))
    (LinearMap.id : S.complementSystem →ₗ[Complex] S.complementSystem)
theorem wordPauliOperatorFactorized_adjoint_comp_self (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) :
    (LinearMap.adjoint (wordPauliOperatorFactorized S p)).comp
      (wordPauliOperatorFactorized S p) = 1 := by
  let P := PauliSymplectic.toQubitOperator (wordBinaryPauli S p)
  let I : Operator S.complementSystem := LinearMap.id
  have hP : (LinearMap.adjoint P).comp P = 1 :=
    PauliSymplectic.toQubitOperator_adjoint_comp_self _
  change (LinearMap.adjoint (TensorProduct.map P I)).comp (TensorProduct.map P I) = 1
  ext h k
  have hPh := congrArg (fun T : Operator S.selectedSystem => T h) hP
  simpa [TensorProduct.map_tmul, P, I, LinearMap.comp_apply] using
    congrArg (fun x : S.selectedSystem => x ⊗ₜ[Complex] k) hPh
noncomputable def wordPauliUnnormalizedFamilyFactorized (S : FiniteSubsystem ι) :
    FiniteKrausFamily (LocalPauliWordIndex S) S.factorizedSystem S.factorizedSystem where
  operator p := wordPauliOperatorFactorized S p
noncomputable def wordPauliFamilyFactorized (S : FiniteSubsystem ι) :
    FiniteKrausFamily (LocalPauliWordIndex S) S.factorizedSystem S.factorizedSystem :=
  (wordPauliUnnormalizedFamilyFactorized S).scale (fun _ => localPauliAmplitude S)
theorem wordPauliFamilyFactorized_complete (S : FiniteSubsystem ι) :
    (wordPauliFamilyFactorized S).Complete := by
  apply FiniteKrausFamily.scale_complete_of_adjoint_square_sum
    (wordPauliUnnormalizedFamilyFactorized S) (fun _ => localPauliAmplitude S)
  simp only [wordPauliUnnormalizedFamilyFactorized]
  rw [show (∑ p : LocalPauliWordIndex S,
      (star (localPauliAmplitude S) * localPauliAmplitude S) •
        ((LinearMap.adjoint (wordPauliOperatorFactorized S p)).comp
          (wordPauliOperatorFactorized S p))) =
      ∑ _p : LocalPauliWordIndex S,
        (star (localPauliAmplitude S) * localPauliAmplitude S) •
          (1 : Operator S.factorizedSystem) by
        apply Finset.sum_congr rfl
        intro p _
        rw [wordPauliOperatorFactorized_adjoint_comp_self]
    ]
  rw [Finset.sum_const, Finset.card_univ]
  let d : Complex := Fintype.card (Qubit.Bitstring S.SelectedCoordinates)
  have hd : d ≠ 0 := by
    dsimp [d]
    exact_mod_cast Fintype.card_ne_zero
  have hcard : (Fintype.card (LocalPauliWordIndex S) : Complex) = d * d := by
    simp [LocalPauliWordIndex, Fintype.card_prod, d]
  have hstar_amplitude : star (localPauliAmplitude S) = localPauliAmplitude S := by
    unfold localPauliAmplitude
    simp
  have hscalar : (Fintype.card (LocalPauliWordIndex S) : Complex) *
      (star (localPauliAmplitude S) * localPauliAmplitude S) = 1 := by
    rw [hcard, hstar_amplitude]
    change (d * d) * (d⁻¹ * d⁻¹) = 1
    field_simp
  rw [← Nat.cast_smul_eq_nsmul Complex]
  rw [smul_smul, hscalar, one_smul]
noncomputable def wordPauliTwirlFactorized (S : FiniteSubsystem ι) :
    QuantumChannel S.factorizedSystem S.factorizedSystem :=
  (wordPauliFamilyFactorized S).toQuantumChannel (wordPauliFamilyFactorized_complete S)
noncomputable def flipWordEquiv {α : Type u} [Fintype α] [DecidableEq α]
    (bits : Qubit.Bitstring α) :
    Coding.Word (ZMod 2) α ≃ Qubit.Bitstring α :=
  (Equiv.addLeft (PauliSymplectic.bitstringWordEquiv α bits)).trans
    (PauliSymplectic.bitstringWordEquiv α).symm
noncomputable def localPauliFamily (S : FiniteSubsystem ι) :
    FiniteKrausFamily (LocalPauliWordIndex S)
      (Qubit.QubitRegister ι) (Qubit.QubitRegister ι) :=
  (wordPauliFamilyFactorized S).unitaryTransport
    S.registerFactorization.symm S.registerFactorization.symm
theorem localPauliFamily_complete (S : FiniteSubsystem ι) :
    (localPauliFamily S).Complete := by
  exact (wordPauliFamilyFactorized S).unitaryTransport_complete
    S.registerFactorization.symm S.registerFactorization.symm
    (wordPauliFamilyFactorized_complete S)
noncomputable def localPauliTwirl (S : FiniteSubsystem ι) :
    QuantumChannel (Qubit.QubitRegister ι) (Qubit.QubitRegister ι) :=
  (localPauliFamily S).toQuantumChannel (localPauliFamily_complete S)
noncomputable def localPauliRefill (S : FiniteSubsystem ι) :
    QuantumChannel S.complementSystem (Qubit.QubitRegister ι) :=
  QuantumChannel.comp (QuantumChannel.unitaryConj S.registerFactorization.symm)
    (refillFactorized S)
end QEC.Locality


