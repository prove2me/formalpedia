-- Prove2me | Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
-- name    : QEC_Bounds_GeometricLocalityTradeoff_Entropy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:46:31.373198+00:00
-- url     : https://prove2.me/theorems/ab79ef77-0896-47be-8650-7b2696e50f2a
-- title:
--   Entropy
-- statement:
--   Definitions and structural lemmas for Entropy, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
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
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorizationWithReference_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceReordering_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceTransport_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.mem_regionSubsystem_selected_iff
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.regionSubsystem_selected
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
attribute [local simp] QEC.Semantics.QuditSubsystem.registerFactorizationWithReference_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.selectedReferenceReordering_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.selectedReferenceTransport_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open scoped TensorProduct
namespace BPTEntropy
open Semantics
open Semantics.DensityOperator
universe u
noncomputable def abcToBac (A B C : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [FiniteQuantumSystem C] :
    UnitaryTransport (CompositeSystem A (CompositeSystem B C))
      (CompositeSystem B (CompositeSystem A C)) := by
  let e1 := (TensorProduct.assocIsometry Complex A B C).symm
  let e2 := (TensorProduct.commIsometry Complex A B).rTensor C
  let e3 := TensorProduct.assocIsometry Complex B A C
  let e := e1.trans (e2.trans e3)
  exact
    { toLinearEquiv := e.toLinearEquiv
      map_inner := by
        intro x y
        simpa [e, e1, e2, e3] using e.inner_map_map x y }
@[simp]
theorem abcToBac_apply_tmul (A B C : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [FiniteQuantumSystem C]
    (a : A) (b : B) (c : C) :
    abcToBac A B C (a ⊗ₜ[Complex] (b ⊗ₜ[Complex] c)) =
      b ⊗ₜ[Complex] (a ⊗ₜ[Complex] c) := by
  simp [abcToBac]
noncomputable def codeReferenceVector {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (C : QuantumCode H) : CompositeSystem H H :=
  ∑ i : Fin C.dimension,
    (Real.sqrt ((C.dimension : Real)⁻¹) : Complex) •
      (((stdOrthonormalBasis Complex C.carrier i : C.carrier) : H) ⊗ₜ[Complex]
        ((stdOrthonormalBasis Complex C.carrier i : C.carrier) : H))
theorem codeReferenceVector_normSq {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (C : QuantumCode H) (hdim : 0 < C.dimension) :
    ‖codeReferenceVector C‖ ^ 2 = 1 := by
  classical
  let e : Fin C.dimension → H := fun i =>
    ((stdOrthonormalBasis Complex C.carrier i : C.carrier) : H)
  have he_inner (i j : Fin C.dimension) :
      inner Complex (e i) (e j) = if i = j then 1 else 0 :=
    (stdOrthonormalBasis Complex C.carrier).inner_eq_ite i j
  let a : Complex := Real.sqrt ((C.dimension : Real)⁻¹)
  have hpair (i j : Fin C.dimension) :
      inner Complex (a • (e i ⊗ₜ[Complex] e i)) (a • (e j ⊗ₜ[Complex] e j)) =
        if i = j then ((C.dimension : Real)⁻¹ : Complex) else 0 := by
    change inner Complex ((a • e i) ⊗ₜ[Complex] e i)
      ((a • e j) ⊗ₜ[Complex] e j) = _
    rw [TensorProduct.inner_tmul, inner_smul_left, inner_smul_right]
    simp only [he_inner, a, Complex.conj_ofReal]
    by_cases hij : i = j
    · subst j
      simp only [if_pos, mul_one]
      exact_mod_cast (show Real.sqrt ((C.dimension : Real)⁻¹) *
          Real.sqrt ((C.dimension : Real)⁻¹) = (C.dimension : Real)⁻¹ by
        simpa [pow_two] using Real.sq_sqrt (inv_nonneg.mpr (by positivity)))
    · simp_all
  have hinner :
      inner Complex (codeReferenceVector C) (codeReferenceVector C) =
        ∑ _ : Fin C.dimension, ((C.dimension : Real)⁻¹ : Complex) := by
    change inner Complex (∑ i, a • (e i ⊗ₜ[Complex] e i))
      (∑ i, a • (e i ⊗ₜ[Complex] e i)) = _
    rw [sum_inner]
    simp_rw [inner_sum, hpair]
    simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex), hinner, map_sum]
  have hdim_ne : (C.dimension : Real) ≠ 0 := by exact_mod_cast hdim.ne'
  have h_re_inv : RCLike.re ((C.dimension : Complex)⁻¹) =
      (C.dimension : Real)⁻¹ := by
    change ((C.dimension : Complex)⁻¹).re = _
    rw [Complex.inv_re]
    norm_num [Complex.normSq_apply]
  change ∑ _ : Fin C.dimension, RCLike.re ((C.dimension : Complex)⁻¹) = 1
  rw [Finset.sum_congr rfl (fun _ _ => h_re_inv)]
  rw [Finset.sum_const]
  have hcard : (Finset.univ : Finset (Fin C.dimension)).card = C.dimension := by
    exact Fintype.card_fin C.dimension
  rw [hcard, nsmul_eq_mul]
  field_simp
noncomputable def normalizedCodeProjector {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (C : QuantumCode H) (hdim : 0 < C.dimension) : DensityOperator H :=
  rightMarginal (pureDensity (codeReferenceVector C) (codeReferenceVector_normSq C hdim))
noncomputable def codeCarrierPurificationVector {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (C : QuantumCode H) : CompositeSystem H C.carrier :=
  ∑ i : Fin C.dimension,
    (Real.sqrt ((C.dimension : Real)⁻¹) : Complex) •
      (((stdOrthonormalBasis Complex C.carrier i : C.carrier) : H) ⊗ₜ[Complex]
        (stdOrthonormalBasis Complex C.carrier i))
theorem codeCarrierPurificationVector_normSq {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (C : QuantumCode H) (hdim : 0 < C.dimension) :
    ‖codeCarrierPurificationVector C‖ ^ 2 = 1 := by
  classical
  let b : OrthonormalBasis (Fin C.dimension) Complex C.carrier :=
    stdOrthonormalBasis Complex C.carrier
  let e : Fin C.dimension → H := fun i => (b i : H)
  let a : Complex := Real.sqrt ((C.dimension : Real)⁻¹)
  have hpair (i j : Fin C.dimension) :
      inner Complex (a • (e i ⊗ₜ[Complex] b i)) (a • (e j ⊗ₜ[Complex] b j)) =
        if i = j then ((C.dimension : Real)⁻¹ : Complex) else 0 := by
    change inner Complex ((a • e i) ⊗ₜ[Complex] b i)
      ((a • e j) ⊗ₜ[Complex] b j) = _
    rw [TensorProduct.inner_tmul, inner_smul_left, inner_smul_right]
    simp only [e, a, Complex.conj_ofReal]
    simp_rw [← C.carrier.coe_inner]
    simp only [b.inner_eq_ite]
    by_cases hij : i = j
    · subst j
      simp only [if_pos, mul_one]
      exact_mod_cast (show Real.sqrt ((C.dimension : Real)⁻¹) *
          Real.sqrt ((C.dimension : Real)⁻¹) = (C.dimension : Real)⁻¹ by
        simpa [pow_two] using Real.sq_sqrt (inv_nonneg.mpr (by positivity)))
    · simp_all
  have hinner :
      inner Complex (codeCarrierPurificationVector C) (codeCarrierPurificationVector C) =
        ∑ _ : Fin C.dimension, ((C.dimension : Real)⁻¹ : Complex) := by
    let f : Fin C.dimension → CompositeSystem H C.carrier := fun i =>
      (a • e i) ⊗ₜ[Complex] b i
    change inner Complex (∑ i, f i) (∑ i, f i) = _
    have hsum_inner (x : CompositeSystem H C.carrier) :
        inner Complex (∑ i, f i) x = ∑ i, inner Complex (f i) x :=
      sum_inner Finset.univ f x
    have hinter_sum (x : CompositeSystem H C.carrier) :
        inner Complex x (∑ i, f i) = ∑ i, inner Complex x (f i) :=
      inner_sum Finset.univ f x
    have hpairF (i j : Fin C.dimension) :
        inner Complex (f i) (f j) =
          if i = j then ((C.dimension : Real)⁻¹ : Complex) else 0 :=
      hpair i j
    calc
      inner Complex (∑ i, f i) (∑ i, f i) =
          ∑ i, inner Complex (f i) (∑ j, f j) := hsum_inner _
      _ = ∑ i, ∑ j, inner Complex (f i) (f j) := by
        simp_rw [hinter_sum]
      _ = ∑ _ : Fin C.dimension, ((C.dimension : Real)⁻¹ : Complex) := by
        simp_rw [hpairF]
        simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex), hinner, map_sum]
  have h_re_inv : RCLike.re ((C.dimension : Complex)⁻¹) =
      (C.dimension : Real)⁻¹ := by
    change ((C.dimension : Complex)⁻¹).re = _
    rw [Complex.inv_re]
    norm_num [Complex.normSq_apply]
  change ∑ _ : Fin C.dimension, RCLike.re ((C.dimension : Complex)⁻¹) = 1
  rw [Finset.sum_congr rfl (fun _ _ => h_re_inv)]
  rw [Finset.sum_const]
  have hcard : (Finset.univ : Finset (Fin C.dimension)).card = C.dimension := by
    exact Fintype.card_fin C.dimension
  rw [hcard, nsmul_eq_mul]
  have hdim_ne : (C.dimension : Real) ≠ 0 := by exact_mod_cast hdim.ne'
  field_simp
theorem bptCodeDimension_pos
    {L : BPTQuditLattice} {κ : Type u} [Fintype κ]
    (M : BPTCommutingProjectorModel L κ)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M) :
    0 < M.codeSpace.dimension := by
  rw [parameter.codeDimension_eq_two_pow]
  exact pow_pos (by omega) _
noncomputable def normalizedFullCodeProjector
    {L : BPTQuditLattice} {κ : Type u} [Fintype κ]
    (M : BPTCommutingProjectorModel L κ)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M) :
    DensityOperator L.Register :=
  normalizedCodeProjector M.codeSpace (bptCodeDimension_pos M parameter)
namespace QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι -> Nat}
def unionSubsystem (S T : QuditSubsystem q) : QuditSubsystem q where
  selected := S.selected ∪ T.selected
def splitABCLabel (S T : QuditSubsystem q) (labels : Qudit.Label q) :
    Qudit.Label S.selectedDimensions ×
      (Qudit.Label T.selectedDimensions ×
        Qudit.Label (unionSubsystem S T).complementDimensions) :=
  (fun i => labels i, fun i => labels i, fun i => labels i)
def recombineABCLabel (S T : QuditSubsystem q)
    (labels : Qudit.Label S.selectedDimensions ×
      (Qudit.Label T.selectedDimensions ×
        Qudit.Label (unionSubsystem S T).complementDimensions)) :
    Qudit.Label q :=
  fun i => if hiS : i ∈ S.selected then
    labels.1 ⟨i, hiS⟩
  else if hiT : i ∈ T.selected then
    labels.2.1 ⟨i, hiT⟩
  else labels.2.2 ⟨i, by
    simp only [unionSubsystem, Finset.mem_union, not_or]
    exact ⟨hiS, hiT⟩⟩
def abcLabelFactorization (S T : QuditSubsystem q) (hST : Disjoint S.selected T.selected) :
    Qudit.Label q ≃ Qudit.Label S.selectedDimensions ×
      (Qudit.Label T.selectedDimensions ×
        Qudit.Label (unionSubsystem S T).complementDimensions) where
  toFun := splitABCLabel S T
  invFun := recombineABCLabel S T
  left_inv := by
    intro labels
    funext i
    by_cases hiS : i ∈ S.selected
    · simp [splitABCLabel, recombineABCLabel, hiS]
    · by_cases hiT : i ∈ T.selected
      · simp [splitABCLabel, recombineABCLabel, hiS, hiT]
      · simp [splitABCLabel, recombineABCLabel, hiS, hiT]
  right_inv := by
    rintro ⟨selectedS, selectedT, complement⟩
    apply Prod.ext
    · funext i
      simp [splitABCLabel, recombineABCLabel]
    · apply Prod.ext
      · funext i
        have hiS : (i : ι) ∉ S.selected := by
          intro hmem
          exact (Finset.disjoint_left.mp hST) hmem i.property
        simp [splitABCLabel, recombineABCLabel, hiS]
      · funext i
        have hiS : (i : ι) ∉ S.selected := by
          intro hmem
          exact i.property (by simp [unionSubsystem, hmem])
        have hiT : (i : ι) ∉ T.selected := by
          intro hmem
          exact i.property (by simp [unionSubsystem, hmem])
        simp [splitABCLabel, recombineABCLabel, hiS, hiT]
noncomputable def abcFactorization (S T : QuditSubsystem q)
    (hST : Disjoint S.selected T.selected) :
    UnitaryTransport (Qudit.QuditRegister q)
      (CompositeSystem S.selectedSystem
        (CompositeSystem T.selectedSystem (unionSubsystem S T).complementSystem)) := by
  let sourceBasis := EuclideanSpace.basisFun (Qudit.Label q) Complex
  let selectedSBasis := EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
  let selectedTBasis := EuclideanSpace.basisFun (Qudit.Label T.selectedDimensions) Complex
  let complementBasis :=
    EuclideanSpace.basisFun (Qudit.Label (unionSubsystem S T).complementDimensions) Complex
  let targetBasis := selectedSBasis.tensorProduct (selectedTBasis.tensorProduct complementBasis)
  let U := sourceBasis.equiv targetBasis (abcLabelFactorization S T hST)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }
def splitComplementABCLabel (S T : QuditSubsystem q)
    (hST : Disjoint S.selected T.selected) (labels : Qudit.Label S.complementDimensions) :
    Qudit.Label T.selectedDimensions ×
      Qudit.Label (unionSubsystem S T).complementDimensions :=
  (fun i => labels ⟨i, by
      intro hiS
      exact (Finset.disjoint_left.mp hST) hiS i.property⟩,
    fun i => labels ⟨i, by
      exact fun hiS => i.property (by simp [unionSubsystem, hiS])⟩)
def recombineComplementABCLabel (S T : QuditSubsystem q)
    (labels : Qudit.Label T.selectedDimensions ×
      Qudit.Label (unionSubsystem S T).complementDimensions) :
    Qudit.Label S.complementDimensions :=
  fun i => if hiT : (i : ι) ∈ T.selected then
    labels.1 ⟨i, hiT⟩
  else labels.2 ⟨i, by
    simp only [unionSubsystem, Finset.mem_union, not_or]
    exact ⟨i.property, hiT⟩⟩
def complementABCLabelFactorization (S T : QuditSubsystem q)
    (hST : Disjoint S.selected T.selected) :
    Qudit.Label S.complementDimensions ≃
      Qudit.Label T.selectedDimensions ×
        Qudit.Label (unionSubsystem S T).complementDimensions where
  toFun := splitComplementABCLabel S T hST
  invFun := recombineComplementABCLabel S T
  left_inv := by
    intro labels
    funext i
    by_cases hiT : (i : ι) ∈ T.selected
    · simp [splitComplementABCLabel, recombineComplementABCLabel, hiT]
    · simp [splitComplementABCLabel, recombineComplementABCLabel, hiT]
  right_inv := by
    rintro ⟨selectedT, complement⟩
    apply Prod.ext
    · funext i
      have hiS : (i : ι) ∉ S.selected := by
        intro hmem
        exact (Finset.disjoint_left.mp hST) hmem i.property
      simp [splitComplementABCLabel, recombineComplementABCLabel]
    · funext i
      have hiS : (i : ι) ∉ S.selected := by
        intro hmem
        exact i.property (by simp [unionSubsystem, hmem])
      have hiT : (i : ι) ∉ T.selected := by
        intro hmem
        exact i.property (by simp [unionSubsystem, hmem])
      simp [splitComplementABCLabel, recombineComplementABCLabel, hiT]
noncomputable def complementABCFactorization (S T : QuditSubsystem q)
    (hST : Disjoint S.selected T.selected) :
    UnitaryTransport S.complementSystem
      (CompositeSystem T.selectedSystem (unionSubsystem S T).complementSystem) := by
  let sourceBasis := EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex
  let selectedTBasis := EuclideanSpace.basisFun (Qudit.Label T.selectedDimensions) Complex
  let complementBasis :=
    EuclideanSpace.basisFun (Qudit.Label (unionSubsystem S T).complementDimensions) Complex
  let targetBasis := selectedTBasis.tensorProduct complementBasis
  let U := sourceBasis.equiv targetBasis (complementABCLabelFactorization S T hST)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }
def splitComplementBACLabel (S T : QuditSubsystem q)
    (hST : Disjoint S.selected T.selected) (labels : Qudit.Label T.complementDimensions) :
    Qudit.Label S.selectedDimensions ×
      Qudit.Label (unionSubsystem S T).complementDimensions :=
  (fun i => labels ⟨i, by
      intro hiT
      exact (Finset.disjoint_left.mp hST) i.property hiT⟩,
    fun i => labels ⟨i, by
      exact fun hiT => i.property (by simp [unionSubsystem, hiT])⟩)
def recombineComplementBACLabel (S T : QuditSubsystem q)
    (labels : Qudit.Label S.selectedDimensions ×
      Qudit.Label (unionSubsystem S T).complementDimensions) :
    Qudit.Label T.complementDimensions :=
  fun i => if hiS : (i : ι) ∈ S.selected then
    labels.1 ⟨i, hiS⟩
  else labels.2 ⟨i, by
    simp only [unionSubsystem, Finset.mem_union, not_or]
    exact ⟨hiS, i.property⟩⟩
def complementBACLabelFactorization (S T : QuditSubsystem q)
    (hST : Disjoint S.selected T.selected) :
    Qudit.Label T.complementDimensions ≃
      Qudit.Label S.selectedDimensions ×
        Qudit.Label (unionSubsystem S T).complementDimensions where
  toFun := splitComplementBACLabel S T hST
  invFun := recombineComplementBACLabel S T
  left_inv := by
    intro labels
    funext i
    by_cases hiS : (i : ι) ∈ S.selected
    · simp [splitComplementBACLabel, recombineComplementBACLabel, hiS]
    · simp [splitComplementBACLabel, recombineComplementBACLabel, hiS]
  right_inv := by
    rintro ⟨selectedS, complement⟩
    apply Prod.ext
    · funext i
      have hiT : (i : ι) ∉ T.selected := by
        intro hmem
        exact (Finset.disjoint_left.mp hST) i.property hmem
      simp [splitComplementBACLabel, recombineComplementBACLabel]
    · funext i
      have hiS : (i : ι) ∉ S.selected := by
        intro hmem
        exact i.property (by simp [unionSubsystem, hmem])
      have hiT : (i : ι) ∉ T.selected := by
        intro hmem
        exact i.property (by simp [unionSubsystem, hmem])
      simp [splitComplementBACLabel, recombineComplementBACLabel, hiS]
noncomputable def complementBACFactorization (S T : QuditSubsystem q)
    (hST : Disjoint S.selected T.selected) :
    UnitaryTransport T.complementSystem
      (CompositeSystem S.selectedSystem (unionSubsystem S T).complementSystem) := by
  let sourceBasis := EuclideanSpace.basisFun (Qudit.Label T.complementDimensions) Complex
  let selectedSBasis := EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
  let complementBasis :=
    EuclideanSpace.basisFun (Qudit.Label (unionSubsystem S T).complementDimensions) Complex
  let targetBasis := selectedSBasis.tensorProduct complementBasis
  let U := sourceBasis.equiv targetBasis (complementBACLabelFactorization S T hST)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }
end QuditSubsystem
end BPTEntropy
end Bounds
end QEC


