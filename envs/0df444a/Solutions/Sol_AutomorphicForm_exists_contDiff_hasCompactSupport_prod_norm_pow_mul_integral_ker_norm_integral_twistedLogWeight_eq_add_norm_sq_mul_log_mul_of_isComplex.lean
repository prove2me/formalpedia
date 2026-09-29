-- Prove2me | solution 1 for AutomorphicForm.exists_contDiff_hasCompactSupport_prod_norm_pow_mul_integral_ker_norm_integral_twistedLogWeight_eq_add_norm_sq_mul_log_mul_of_isComplex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/04d4185f-8fd6-5a38-9c2b-055bc539d044

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_exists_linearMap_prod_norm_pow_mul_integral_comp_sigmaTensor_sub_mul_twistedLogWeight_eq_add_sum
import Theorems.Thm_NumberField_InfiniteAdeleRing_isHomeomorph_ringEquiv_mixedSpace
import Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_integral_ker_norm_integral_mul_log_sq_add_norm_resolvent_sq_eq_add_norm_sq_mul_log_mul_of_isComplex_isComplex
import Theorems.Thm_Algebra_TensorProduct_algebraMap_norm_eq_prod_map_algEquiv
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_prod_norm_pow_mul_integral_ker_norm_integral_twistedLogWeight_eq_add_norm_sq_mul_log_mul_of_isComplex

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

namespace C3Inst

open NumberField

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] in
theorem secondCountableTopology_infiniteAdeleRing' (F : Type) [Field F] [NumberField F] :
    SecondCountableTopology (InfiniteAdeleRing F) := by
  haveI : ∀ v : InfinitePlace F, SecondCountableTopology v.Completion := fun v =>
    (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))

theorem secondCountableTopology_E : SecondCountableTopology (L ⊗[K] InfiniteAdeleRing K) :=
  haveI := secondCountableTopology_infiniteAdeleRing' L
  (AutomorphicForm.archIdentHomeomorph K L).secondCountableTopology

theorem secondCountableTopology_unitsE : SecondCountableTopology (L ⊗[K] InfiniteAdeleRing K)ˣ := by
  haveI := secondCountableTopology_E K L
  haveI : SecondCountableTopology (L ⊗[K] InfiniteAdeleRing K)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

theorem locallyCompactSpace_unitsE : LocallyCompactSpace (L ⊗[K] InfiniteAdeleRing K)ˣ := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  haveI := AutomorphicForm.t2Space_tensor K L (InfiniteAdeleRing K)
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L (InfiniteAdeleRing K)
  haveI : LocallyCompactSpace (L ⊗[K] InfiniteAdeleRing K)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem continuous_includeRight :
    Continuous ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K) :
      InfiniteAdeleRing K → L ⊗[K] InfiniteAdeleRing K) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  have h : ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K) :
      InfiniteAdeleRing K → L ⊗[K] InfiniteAdeleRing K) = fun x => x • (1 : L ⊗[K] InfiniteAdeleRing K) := by
    funext x
    rw [AutomorphicForm.rightActions_smul_eq, mul_one]
    rfl
  rw [h]
  exact continuous_id.fun_smul continuous_const

theorem continuous_algebraNorm :
    Continuous (Algebra.norm (InfiniteAdeleRing K) : L ⊗[K] InfiniteAdeleRing K → InfiniteAdeleRing K) := by
  classical
  haveI hTR := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  haveI : ContinuousAdd (L ⊗[K] InfiniteAdeleRing K) := hTR.toContinuousAdd
  let b := Module.Free.chooseBasis (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)
  have : (Algebra.norm (InfiniteAdeleRing K) : L ⊗[K] InfiniteAdeleRing K → InfiniteAdeleRing K) =
      fun s => (Algebra.leftMulMatrix b s).det := funext (Algebra.norm_eq_matrix_det b)
  rw [this]
  refine Continuous.matrix_det ?_
  exact IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap

theorem continuous_iotaL :
    Continuous (fun z : L ⊗[K] InfiniteAdeleRing K =>
      NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L z)) :=
  (NumberField.InfiniteAdeleRing.isHomeomorph_ringEquiv_mixedSpace L).continuous.comp
    (AutomorphicForm.archIdentHomeomorph K L).continuous

theorem continuous_iotaK :
    Continuous (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K : InfiniteAdeleRing K → mixedEmbedding.mixedSpace K) :=
  (NumberField.InfiniteAdeleRing.isHomeomorph_ringEquiv_mixedSpace K).continuous

end C3Inst

namespace A5RN
open AutomorphicForm

section generic
variable {R : Type*} [CommRing R]

theorem val_mul_apply (x y : GL (Fin 2) R) (i j : Fin 2) :
    ((x * y : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i j =
      (x : Matrix (Fin 2) (Fin 2) R) i 0 * (y : Matrix (Fin 2) (Fin 2) R) 0 j +
        (x : Matrix (Fin 2) (Fin 2) R) i 1 * (y : Matrix (Fin 2) (Fin 2) R) 1 j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

def IsDiag (x : GL (Fin 2) R) : Prop :=
  (x : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 ∧ (x : Matrix (Fin 2) (Fin 2) R) 1 0 = 0

theorem offdiag_eq_zero_of_commute (T t : GL (Fin 2) R)
    (hT01 : (T : Matrix (Fin 2) (Fin 2) R) 0 1 = 0) (hT10 : (T : Matrix (Fin 2) (Fin 2) R) 1 0 = 0)
    (hreg : IsUnit ((T : Matrix (Fin 2) (Fin 2) R) 0 0 - (T : Matrix (Fin 2) (Fin 2) R) 1 1))
    (hc : T * t = t * T) : IsDiag t := by
  have hv := congrArg (fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R)) hc
  have e01 := congrFun (congrFun hv 0) 1
  have e10 := congrFun (congrFun hv 1) 0
  beta_reduce at e01 e10
  rw [val_mul_apply, val_mul_apply, hT01, zero_mul, add_zero, mul_zero, zero_add] at e01
  rw [val_mul_apply, val_mul_apply, hT10, zero_mul, zero_add, mul_zero, add_zero] at e10
  constructor
  · have h : ((T : Matrix (Fin 2) (Fin 2) R) 0 0 - (T : Matrix (Fin 2) (Fin 2) R) 1 1) *
        (t : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 := by
      rw [sub_mul, e01, mul_comm, sub_self]
    exact (hreg.mul_right_eq_zero).mp h
  · have h : ((T : Matrix (Fin 2) (Fin 2) R) 0 0 - (T : Matrix (Fin 2) (Fin 2) R) 1 1) *
        (t : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := by
      rw [sub_mul, e10, mul_comm, sub_self]
    exact (hreg.mul_right_eq_zero).mp h

theorem isUnit_sub_of_isRegularSemisimple (T : GL (Fin 2) R)
    (hT01 : (T : Matrix (Fin 2) (Fin 2) R) 0 1 = 0) (hT10 : (T : Matrix (Fin 2) (Fin 2) R) 1 0 = 0)
    (hreg : IsRegularSemisimple T) :
    IsUnit ((T : Matrix (Fin 2) (Fin 2) R) 0 0 - (T : Matrix (Fin 2) (Fin 2) R) 1 1) := by
  have h : Matrix.trace (T : Matrix (Fin 2) (Fin 2) R) ^ 2 - 4 * Matrix.det (T : Matrix (Fin 2) (Fin 2) R) =
      ((T : Matrix (Fin 2) (Fin 2) R) 0 0 - (T : Matrix (Fin 2) (Fin 2) R) 1 1) *
        ((T : Matrix (Fin 2) (Fin 2) R) 0 0 - (T : Matrix (Fin 2) (Fin 2) R) 1 1) := by
    rw [Matrix.trace_fin_two, Matrix.det_fin_two, hT01, hT10]; ring
  have h2 : IsUnit (Matrix.trace (T : Matrix (Fin 2) (Fin 2) R) ^ 2 -
      4 * Matrix.det (T : Matrix (Fin 2) (Fin 2) R)) := hreg
  rw [h] at h2
  exact (IsUnit.mul_iff.mp h2).1

theorem diag_comm {x y : GL (Fin 2) R} (hx : IsDiag x) (hy : IsDiag y) : x * y = y * x := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, val_mul_apply, hx.1, hy.1, hx.2, hy.2, mul_zero, zero_mul, add_zero]
    exact mul_comm _ _
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, val_mul_apply, hx.1, hy.1, mul_zero, zero_mul, add_zero]
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, val_mul_apply, hx.2, hy.2, mul_zero, zero_mul, add_zero]
  · simp only [Fin.isValue, Fin.mk_one, val_mul_apply, hx.1, hy.1, hx.2, hy.2, mul_zero, zero_mul, zero_add]
    exact mul_comm _ _

theorem isDiag_mul {x y : GL (Fin 2) R} (hx : IsDiag x) (hy : IsDiag y) : IsDiag (x * y) := by
  constructor
  · rw [val_mul_apply, hx.1, hy.1, mul_zero, zero_mul, add_zero]
  · rw [val_mul_apply, hx.2, hy.2, mul_zero, zero_mul, add_zero]

theorem isUnit_diag_entries {x : GL (Fin 2) R} (hx : IsDiag x) :
    IsUnit ((x : Matrix (Fin 2) (Fin 2) R) 0 0) ∧ IsUnit ((x : Matrix (Fin 2) (Fin 2) R) 1 1) := by
  have hdet : IsUnit (x : Matrix (Fin 2) (Fin 2) R).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.isUnit _
  rw [Matrix.det_fin_two, hx.1, zero_mul, sub_zero] at hdet
  exact ⟨isUnit_of_mul_isUnit_left hdet, isUnit_of_mul_isUnit_right hdet⟩

theorem isDiag_inv {x : GL (Fin 2) R} (hx : IsDiag x) : IsDiag x⁻¹ := by
  obtain ⟨h00, h11⟩ := isUnit_diag_entries hx
  have hone := congrArg (fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R)) (mul_inv_cancel x)
  have e01 := congrFun (congrFun hone 0) 1
  have e10 := congrFun (congrFun hone 1) 0
  beta_reduce at e01 e10
  rw [val_mul_apply, hx.1, zero_mul, add_zero, Units.val_one, Matrix.one_apply_ne (by decide)] at e01
  rw [val_mul_apply, hx.2, zero_mul, zero_add, Units.val_one, Matrix.one_apply_ne (by decide)] at e10
  exact ⟨(h00.mul_right_eq_zero).mp e01, (h11.mul_right_eq_zero).mp e10⟩

def mkDiag (a b : Rˣ) : GL (Fin 2) R where
  val := !![(a : R), 0; 0, (b : R)]
  inv := !![((a⁻¹ : Rˣ) : R), 0; 0, ((b⁻¹ : Rˣ) : R)]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem mkDiag_apply00 (a b : Rˣ) :
    ((mkDiag a b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0 = a := rfl
@[scoped simp] theorem mkDiag_apply01 (a b : Rˣ) :
    ((mkDiag a b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 := rfl
@[scoped simp] theorem mkDiag_apply10 (a b : Rˣ) :
    ((mkDiag a b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := rfl
@[scoped simp] theorem mkDiag_apply11 (a b : Rˣ) :
    ((mkDiag a b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 1 = b := rfl

theorem coe_mkDiag_inv (a b : Rˣ) :
    (((mkDiag a b)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = !![((a⁻¹ : Rˣ) : R), 0; 0, ((b⁻¹ : Rˣ) : R)] :=
  rfl

theorem mkDiag_inv_apply00 (a b : Rˣ) :
    (((mkDiag a b)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0 = ((a⁻¹ : Rˣ) : R) := rfl
theorem mkDiag_inv_apply11 (a b : Rˣ) :
    (((mkDiag a b)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 1 = ((b⁻¹ : Rˣ) : R) := rfl

theorem isDiag_mkDiag (a b : Rˣ) : IsDiag (mkDiag a b) := ⟨rfl, rfl⟩

end generic

theorem weight_diag_mul {F : Type*} [NormedField F] (d y : GL (Fin 2) F) (hd : IsDiag d) :
    LocalWeight.weight (d * y) = LocalWeight.weight y := by
  have hdet : (d : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
  have hdet' : (d : Matrix (Fin 2) (Fin 2) F).det =
      (d : Matrix (Fin 2) (Fin 2) F) 0 0 * (d : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    rw [Matrix.det_fin_two, hd.1, hd.2, mul_zero, sub_zero]
  rw [hdet'] at hdet
  obtain ⟨h0, h1⟩ := mul_ne_zero_iff.mp hdet
  have n0 : 0 < ‖(d : Matrix (Fin 2) (Fin 2) F) 0 0‖ := norm_pos_iff.mpr h0
  have n1 : 0 < ‖(d : Matrix (Fin 2) (Fin 2) F) 1 1‖ := norm_pos_iff.mpr h1
  unfold LocalWeight.weight AdelicHeight.rowMaxNorm
  simp only [val_mul_apply, hd.1, hd.2, zero_mul, add_zero, zero_add, norm_mul, Units.val_mul, Matrix.det_mul,
    hdet']
  rw [← mul_max_of_nonneg _ _ n0.le, ← mul_max_of_nonneg _ _ n1.le]
  congr 1
  field_simp

theorem continuous_weight {F : Type*} [NormedField F] :
    Continuous (LocalWeight.weight : GL (Fin 2) F → ℝ) := by
  have hc : Continuous fun x : GL (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F) := Units.continuous_val
  have he : ∀ i j : Fin 2, Continuous fun x : GL (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F) i j :=
    fun i j => (continuous_apply j).comp ((continuous_apply i).comp hc)
  have hdet : Continuous fun x : GL (Fin 2) F => ‖(x : Matrix (Fin 2) (Fin 2) F).det‖ := (hc.matrix_det).norm
  have htop : Continuous fun x : GL (Fin 2) F =>
      max ‖(x : Matrix (Fin 2) (Fin 2) F) 0 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) 0 1‖ :=
    ((he 0 0).norm).max ((he 0 1).norm)
  have hbot : Continuous fun x : GL (Fin 2) F =>
      NumberField.AdelicHeight.rowMaxNorm (x : Matrix (Fin 2) (Fin 2) F) :=
    ((he 1 0).norm).max ((he 1 1).norm)
  have hdet0 : ∀ x : GL (Fin 2) F, ‖(x : Matrix (Fin 2) (Fin 2) F).det‖ ≠ 0 := fun x =>
    (norm_pos_iff.mpr (Matrix.isUnits_det_units x).ne_zero).ne'
  have htop0 : ∀ x : GL (Fin 2) F,
      max ‖(x : Matrix (Fin 2) (Fin 2) F) 0 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) 0 1‖ ≠ 0 := by
    intro x h0
    have h00 : (x : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 :=
      norm_eq_zero.mp (le_antisymm (le_trans (le_max_left _ _) h0.le) (norm_nonneg _))
    have h01 : (x : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 :=
      norm_eq_zero.mp (le_antisymm (le_trans (le_max_right _ _) h0.le) (norm_nonneg _))
    have hd : (x : Matrix (Fin 2) (Fin 2) F).det = 0 := by
      rw [Matrix.det_fin_two, h00, h01, zero_mul, zero_mul, sub_zero]
    exact (Matrix.isUnits_det_units x).ne_zero hd
  unfold AutomorphicForm.LocalWeight.weight
  exact continuous_const.mul
    (((htop.mul hbot).div hdet hdet0).log fun x =>
      div_ne_zero (mul_ne_zero (htop0 x) (NumberField.AdelicHeight.rowMaxNorm_pos x).ne') (hdet0 x))

section sigma

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]

theorem sigmaTensor_mul_apply (σ τ : L ≃ₐ[K] L) (x : L ⊗[K] A) :
    sigmaTensor K L A (σ * τ) x = sigmaTensor K L A σ (sigmaTensor K L A τ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l a =>
    change Algebra.TensorProduct.map (σ * τ).toAlgHom (AlgHom.id K A) (l ⊗ₜ a) =
      Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A)
        (Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id K A) (l ⊗ₜ a))
    simp only [Algebra.TensorProduct.map_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem sigmaTensor_one_apply (x : L ⊗[K] A) : sigmaTensor K L A 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l a =>
    change Algebra.TensorProduct.map (1 : L ≃ₐ[K] L).toAlgHom (AlgHom.id K A) (l ⊗ₜ a) = l ⊗ₜ a
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  | add x y hx hy => rw [map_add, hx, hy]

theorem sigmaTensor_iterate (σ : L ≃ₐ[K] L) (n : ℕ) (x : L ⊗[K] A) :
    (⇑(sigmaTensor K L A σ))^[n] x = sigmaTensor K L A (σ ^ n) x := by
  induction n with
  | zero => rw [Function.iterate_zero_apply, pow_zero, sigmaTensor_one_apply]
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ', sigmaTensor_mul_apply]

theorem sigmaTensor_one_tmul (σ : L ≃ₐ[K] L) (a : A) :
    sigmaTensor K L A σ ((1 : L) ⊗ₜ[K] a) = (1 : L) ⊗ₜ[K] a := by
  change Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A) ((1 : L) ⊗ₜ a) = (1 : L) ⊗ₜ a
  rw [Algebra.TensorProduct.map_tmul]
  simp

theorem sigmaGL_apply (σ : L ≃ₐ[K] L) (x : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2) :
    ((sigmaGL K L A σ x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      sigmaTensor K L A σ ((x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) := rfl

theorem sigmaGL_iterate_apply (σ : L ≃ₐ[K] L) (n : ℕ) (x : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2) :
    (((⇑(sigmaGL K L A σ))^[n] x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      (⇑(sigmaTensor K L A σ))^[n] ((x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    rfl

theorem toTensorGL_apply (γ : GL (Fin 2) A) (i j : Fin 2) :
    ((toTensorGL K L A γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      (1 : L) ⊗ₜ[K] ((γ : Matrix (Fin 2) (Fin 2) A) i j) := rfl

theorem sigmaGL_toTensorGL (σ : L ≃ₐ[K] L) (γ : GL (Fin 2) A) :
    sigmaGL K L A σ (toTensorGL K L A γ) = toTensorGL K L A γ := by
  apply Units.ext
  ext i j
  rw [sigmaGL_apply, toTensorGL_apply, sigmaTensor_one_tmul]

theorem isDiag_sigmaGL (σ : L ≃ₐ[K] L) {x : GL (Fin 2) (L ⊗[K] A)} (hx : IsDiag x) :
    IsDiag (sigmaGL K L A σ x) := by
  constructor
  · rw [sigmaGL_apply, hx.1, map_zero]
  · rw [sigmaGL_apply, hx.2, map_zero]

theorem sigmaGL_iterate_finrank [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (x : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(sigmaGL K L A σ))^[Module.finrank K L] x = x := by
  have hdvd : orderOf σ ∣ Module.finrank K L := by
    have h1 : Module.finrank (IntermediateField.fixedField (Subgroup.zpowers σ)) L =
        Nat.card (Subgroup.zpowers σ) :=
      IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers σ)
    rw [Nat.card_zpowers] at h1
    rw [← h1]
    exact Dvd.intro_left _ (Module.finrank_mul_finrank K (IntermediateField.fixedField (Subgroup.zpowers σ)) L)
  have hpow : σ ^ Module.finrank K L = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
  apply Units.ext
  ext i j
  rw [sigmaGL_iterate_apply, sigmaTensor_iterate, hpow, sigmaTensor_one_apply]

theorem sigma_pow_finrank [FiniteDimensional K L] (σ : L ≃ₐ[K] L) : σ ^ Module.finrank K L = 1 := by
  have hdvd : orderOf σ ∣ Module.finrank K L := by
    have h1 : Module.finrank (IntermediateField.fixedField (Subgroup.zpowers σ)) L =
        Nat.card (Subgroup.zpowers σ) :=
      IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers σ)
    rw [Nat.card_zpowers] at h1
    rw [← h1]
    exact Dvd.intro_left _ (Module.finrank_mul_finrank K (IntermediateField.fixedField (Subgroup.zpowers σ)) L)
  exact orderOf_dvd_iff_pow_eq_one.mp hdvd

def P (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) (n : ℕ) : GL (Fin 2) (L ⊗[K] A) :=
  ((List.range n).map fun i => (⇑(sigmaGL K L A σ))^[i] δ).prod

theorem P_succ (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) (n : ℕ) :
    P K L A σ δ (n + 1) = P K L A σ δ n * (⇑(sigmaGL K L A σ))^[n] δ := by
  simp only [P, List.range_succ, List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]

theorem normString_eq_P [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) :
    normString K L A σ δ = P K L A σ δ (Module.finrank K L) := rfl

theorem iterate_map_mul' (σ : L ≃ₐ[K] L) (k : ℕ) (x y : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(sigmaGL K L A σ))^[k] (x * y) = (⇑(sigmaGL K L A σ))^[k] x * (⇑(sigmaGL K L A σ))^[k] y := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, map_mul]

theorem P_succ' (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) (n : ℕ) :
    P K L A σ δ (n + 1) = δ * sigmaGL K L A σ (P K L A σ δ n) := by
  induction n with
  | zero => simp [P]
  | succ n ih =>
    calc P K L A σ δ (n + 1 + 1) = P K L A σ δ (n + 1) * (⇑(sigmaGL K L A σ))^[n + 1] δ := P_succ K L A σ δ (n + 1)
      _ = δ * sigmaGL K L A σ (P K L A σ δ n) * sigmaGL K L A σ ((⇑(sigmaGL K L A σ))^[n] δ) := by
          rw [ih, Function.iterate_succ_apply']
      _ = δ * sigmaGL K L A σ (P K L A σ δ n * (⇑(sigmaGL K L A σ))^[n] δ) := by rw [map_mul, mul_assoc]
      _ = δ * sigmaGL K L A σ (P K L A σ δ (n + 1)) := by rw [← P_succ]

def Nm (σ : L ≃ₐ[K] L) (n : ℕ) (x : L ⊗[K] A) : L ⊗[K] A :=
  ((List.range n).map fun i => (⇑(sigmaTensor K L A σ))^[i] x).prod

theorem Nm_succ (σ : L ≃ₐ[K] L) (n : ℕ) (x : L ⊗[K] A) :
    Nm K L A σ (n + 1) x = Nm K L A σ n x * (⇑(sigmaTensor K L A σ))^[n] x := by
  simp only [Nm, List.range_succ, List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]

theorem sigmaTensor_iterate_mul (σ : L ≃ₐ[K] L) (k : ℕ) (x y : L ⊗[K] A) :
    (⇑(sigmaTensor K L A σ))^[k] (x * y) = (⇑(sigmaTensor K L A σ))^[k] x * (⇑(sigmaTensor K L A σ))^[k] y := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, map_mul]

theorem sigmaTensor_iterate_one (σ : L ≃ₐ[K] L) (k : ℕ) :
    (⇑(sigmaTensor K L A σ))^[k] (1 : L ⊗[K] A) = 1 :=
  Function.iterate_fixed (map_one _) k

theorem sigmaTensor_iterate_zero (σ : L ≃ₐ[K] L) (k : ℕ) :
    (⇑(sigmaTensor K L A σ))^[k] (0 : L ⊗[K] A) = 0 :=
  Function.iterate_fixed (map_zero _) k

theorem Nm_mul (σ : L ≃ₐ[K] L) (n : ℕ) (x y : L ⊗[K] A) :
    Nm K L A σ n (x * y) = Nm K L A σ n x * Nm K L A σ n y := by
  induction n with
  | zero => simp [Nm]
  | succ n ih => rw [Nm_succ, Nm_succ, Nm_succ, ih, sigmaTensor_iterate_mul]; ring

theorem Nm_one (σ : L ≃ₐ[K] L) (n : ℕ) : Nm K L A σ n (1 : L ⊗[K] A) = 1 := by
  induction n with
  | zero => simp [Nm]
  | succ n ih => rw [Nm_succ, ih, sigmaTensor_iterate_one, one_mul]

theorem isUnit_Nm (σ : L ≃ₐ[K] L) (n : ℕ) {x : L ⊗[K] A} (hx : IsUnit x) : IsUnit (Nm K L A σ n x) := by
  obtain ⟨u, rfl⟩ := hx
  have h : Nm K L A σ n (u : L ⊗[K] A) * Nm K L A σ n ((u⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) = 1 := by
    rw [← Nm_mul, Units.mul_inv, Nm_one]
  exact isUnit_iff_exists_inv.mpr ⟨_, h⟩

theorem P_entries (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) (hδ : IsDiag δ) (n : ℕ) :
    IsDiag (P K L A σ δ n) ∧
    ((P K L A σ δ n : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 =
      Nm K L A σ n ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0) ∧
    ((P K L A σ δ n : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1 =
      Nm K L A σ n ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1) := by
  induction n with
  | zero =>
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · simp [P]
    · simp [P]
    · simp [P, Nm]
    · simp [P, Nm]
  | succ n ih =>
    obtain ⟨⟨ih01, ih10⟩, ih00, ih11⟩ := ih
    have e01 : (((⇑(sigmaGL K L A σ))^[n] δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0 := by
      rw [sigmaGL_iterate_apply, hδ.1, sigmaTensor_iterate_zero]
    have e10 : (((⇑(sigmaGL K L A σ))^[n] δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0 := by
      rw [sigmaGL_iterate_apply, hδ.2, sigmaTensor_iterate_zero]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [P_succ, val_mul_apply, ih01, e01, mul_zero, zero_mul, add_zero]
    · rw [P_succ, val_mul_apply, ih10, e10, mul_zero, zero_mul, add_zero]
    · rw [P_succ, val_mul_apply, ih00, e10, mul_zero, add_zero, sigmaGL_iterate_apply, Nm_succ]
    · rw [P_succ, val_mul_apply, ih11, e01, mul_zero, zero_add, sigmaGL_iterate_apply, Nm_succ]

theorem commute_of_normString_eq [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A))
    (γ : GL (Fin 2) A) (h : normString K L A σ δ = toTensorGL K L A γ) :
    toTensorGL K L A γ * δ = δ * toTensorGL K L A γ := by
  have h1 : P K L A σ δ (Module.finrank K L + 1) = toTensorGL K L A γ * δ := by
    rw [P_succ, sigmaGL_iterate_finrank, ← normString_eq_P, h]
  have h2 : P K L A σ δ (Module.finrank K L + 1) = δ * toTensorGL K L A γ := by
    rw [P_succ', ← normString_eq_P, h, sigmaGL_toTensorGL]
  rw [← h1, h2]

theorem mul_normString_comm [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (δ t : GL (Fin 2) (L ⊗[K] A))
    (ht : t ∈ twistedCentralizer K L A σ δ) :
    normString K L A σ δ * t = t * normString K L A σ δ := by
  set s := sigmaGL K L A σ with hs
  have ht' : t * δ * (s t)⁻¹ = δ := mem_sigmaCentralizer_iff.mp ht
  have htδ : t * δ = δ * s t := by
    calc t * δ = t * δ * (s t)⁻¹ * s t := by group
      _ = δ * s t := by rw [ht']
  have hP : ∀ k : ℕ, t * P K L A σ δ k = P K L A σ δ k * s^[k] t := by
    intro k
    induction k with
    | zero => simp [P]
    | succ k ih =>
        rw [P_succ, ← mul_assoc, ih, mul_assoc, mul_assoc]
        congr 1
        rw [← iterate_map_mul', htδ, iterate_map_mul', ← Function.iterate_succ_apply s k t]
  have h := hP (Module.finrank K L)
  rw [hs, sigmaGL_iterate_finrank, ← normString_eq_P] at h
  exact h.symm

variable {K L A}

theorem mem_twistedCentralizer_conj [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
    (δ g t : GL (Fin 2) (L ⊗[K] A)) (hg : IsDiag g) (hg' : IsDiag g⁻¹) (htd : IsDiag t)
    (ht : t ∈ twistedCentralizer K L A σ δ) :
    t ∈ twistedCentralizer K L A σ (g⁻¹ * δ * sigmaGL K L A σ g) := by
  rw [mem_sigmaCentralizer_iff] at ht ⊢
  have h1 : t * g⁻¹ = g⁻¹ * t := diag_comm htd hg'
  have h2 : sigmaGL K L A σ g * (sigmaGL K L A σ t)⁻¹ = (sigmaGL K L A σ t)⁻¹ * sigmaGL K L A σ g :=
    diag_comm (isDiag_sigmaGL K L A σ hg) (isDiag_inv (isDiag_sigmaGL K L A σ htd))
  calc t * (g⁻¹ * δ * sigmaGL K L A σ g) * (sigmaGL K L A σ t)⁻¹
      = (t * g⁻¹) * δ * (sigmaGL K L A σ g * (sigmaGL K L A σ t)⁻¹) := by group
    _ = (g⁻¹ * t) * δ * ((sigmaGL K L A σ t)⁻¹ * sigmaGL K L A σ g) := by rw [h1, h2]
    _ = g⁻¹ * (t * δ * (sigmaGL K L A σ t)⁻¹) * sigmaGL K L A σ g := by group
    _ = g⁻¹ * δ * sigmaGL K L A σ g := by rw [ht]

end sigma

section NormProd

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]

theorem Nm_eq_prod_range (σ : L ≃ₐ[K] L) (n : ℕ) (x : L ⊗[K] A) :
    Nm K L A σ n x = ∏ i ∈ Finset.range n, (⇑(sigmaTensor K L A σ))^[i] x := by
  induction n with
  | zero => simp [Nm]
  | succ n ih => rw [Nm_succ, ih, Finset.prod_range_succ]

theorem comm_sigmaTensor (σ : L ≃ₐ[K] L) (x : L ⊗[K] A) :
    Algebra.TensorProduct.comm K L A (sigmaTensor K L A σ x) =
      Algebra.TensorProduct.map (AlgHom.id K A) (σ : L →ₐ[K] L) (Algebra.TensorProduct.comm K L A x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l a =>
    change Algebra.TensorProduct.comm K L A (Algebra.TensorProduct.map (σ : L →ₐ[K] L) (AlgHom.id K A) (l ⊗ₜ a)) = _
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.comm_tmul,
      Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

theorem comm_sigmaTensor_pow (σ : L ≃ₐ[K] L) (i : ℕ) (x : L ⊗[K] A) :
    Algebra.TensorProduct.comm K L A ((⇑(sigmaTensor K L A σ))^[i] x) =
      Algebra.TensorProduct.map (AlgHom.id K A) ((σ ^ i : L ≃ₐ[K] L) : L →ₐ[K] L) (Algebra.TensorProduct.comm K L A x) := by
  induction i generalizing x with
  | zero =>
    simp only [Function.iterate_zero, id_eq, pow_zero]
    induction (Algebra.TensorProduct.comm K L A x) using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a l => rw [Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => rw [map_add, ← hx, ← hy]
  | succ i ih =>
    rw [Function.iterate_succ_apply', comm_sigmaTensor, ih, pow_succ']
    induction (Algebra.TensorProduct.comm K L A x) using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a l => rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

noncomputable def commA : (L ⊗[K] A) ≃ₐ[A] (A ⊗[K] L) :=
  AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm K L A).toRingEquiv) (fun a => by
    change Algebra.TensorProduct.comm K L A (algebraMap A (L ⊗[K] A) a) = algebraMap A (A ⊗[K] L) a
    rw [show algebraMap A (L ⊗[K] A) a = (1 : L) ⊗ₜ a from rfl, Algebra.TensorProduct.comm_tmul]
    rfl)

theorem commA_apply (x : L ⊗[K] A) : commA K L A x = Algebra.TensorProduct.comm K L A x := rfl

end NormProd

section NormProdGalois

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  (A : Type) [CommRing A] [Algebra K A]

theorem algebraMap_norm_eq_Nm (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (x : L ⊗[K] A) :
    algebraMap A (L ⊗[K] A) (Algebra.norm A x) = Nm K L A σ (Module.finrank K L) x := by
  classical

  have h54 := Algebra.TensorProduct.algebraMap_norm_eq_prod_map_algEquiv K L A (commA K L A x)

  have hN : Algebra.norm A (commA K L A x) = Algebra.norm A x := Algebra.norm_eq_of_algEquiv (commA K L A) x
  rw [hN] at h54

  apply (Algebra.TensorProduct.comm K L A).injective
  have lhs : Algebra.TensorProduct.comm K L A (algebraMap A (L ⊗[K] A) (Algebra.norm A x)) =
      algebraMap A (A ⊗[K] L) (Algebra.norm A x) := by
    rw [show algebraMap A (L ⊗[K] A) (Algebra.norm A x) = (1 : L) ⊗ₜ Algebra.norm A x from rfl,
      Algebra.TensorProduct.comm_tmul]; rfl
  rw [lhs, h54, Nm_eq_prod_range, map_prod]
  simp_rw [comm_sigmaTensor_pow]

  have hcard : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  have hcardF : Fintype.card (L ≃ₐ[K] L) = Module.finrank K L := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have htop : Subgroup.zpowers σ = ⊤ := (Subgroup.eq_top_iff' _).mpr hgen
  have horder : orderOf σ = Module.finrank K L := by
    rw [← Nat.card_zpowers, htop, Subgroup.card_top, hcard]
  have hinj : ∀ i ∈ Finset.range (Module.finrank K L), ∀ j ∈ Finset.range (Module.finrank K L), σ ^ i = σ ^ j → i = j := by
    intro i hi j hj h
    exact pow_injOn_Iio_orderOf (by simpa [horder] using hi) (by simpa [horder] using hj) h
  have himage : (Finset.range (Module.finrank K L)).image (fun i => σ ^ i) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn (fun i hi j hj h => hinj i hi j hj h), Finset.card_range, hcardF]
  rw [← Finset.prod_image (s := Finset.range (Module.finrank K L)) (g := fun i => σ ^ i)
    (f := fun g : L ≃ₐ[K] L => Algebra.TensorProduct.map (AlgHom.id K A) (g : L →ₐ[K] L) (Algebra.TensorProduct.comm K L A x))
    hinj, himage]
  rfl

end NormProdGalois

end A5RN
p2m_reactivate "P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_prod_norm_pow_mul_integral_ker_norm_integral_twistedLogWeight_eq_add_norm_sq_mul_log_mul_of_isComplex.A5RN"

namespace A5RN
open AutomorphicForm

section Arch
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

theorem diagUnits2_isDiag {A : Type} [CommRing A] (α β : Aˣ) :
    ((diagUnits2 α β : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 ∧
    ((diagUnits2 α β : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 ∧
    ((diagUnits2 α β : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 = α ∧
    ((diagUnits2 α β : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1 = β := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [diagUnits2]

theorem norm_eq_of_normString_diagUnits2 (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (α β : (L ⊗[K] InfiniteAdeleRing K)ˣ) (a b : (InfiniteAdeleRing K)ˣ)
    (hN : normString K L (InfiniteAdeleRing K) σ (diagUnits2 α β) =
      toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 a b)) :
    Algebra.norm (InfiniteAdeleRing K) ((α : (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K) = a ∧
    Algebra.norm (InfiniteAdeleRing K) ((β : (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K) = b := by
  obtain ⟨h01, h10, h00, h11⟩ := diagUnits2_isDiag α β
  obtain ⟨k01, k10, k00, k11⟩ := diagUnits2_isDiag a b
  obtain ⟨-, hP00, hP11⟩ := P_entries K L (InfiniteAdeleRing K) σ (diagUnits2 α β) ⟨h01, h10⟩ (Module.finrank K L)
  rw [← normString_eq_P, hN, toTensorGL_apply, h00] at hP00
  rw [← normString_eq_P, hN, toTensorGL_apply, h11] at hP11
  rw [k00] at hP00
  rw [k11] at hP11
  have hinj : Function.Injective (algebraMap (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)) := fun x y h =>
    Algebra.TensorProduct.includeRight_injective (R := K) (A := L) (B := InfiniteAdeleRing K)
      (algebraMap K L).injective h
  refine ⟨hinj ?_, hinj ?_⟩
  · rw [algebraMap_norm_eq_Nm K L (InfiniteAdeleRing K) σ hgen, ← hP00]; rfl
  · rw [algebraMap_norm_eq_Nm K L (InfiniteAdeleRing K) σ hgen, ← hP11]; rfl

theorem norm_inv_mul_eq (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (α β : (L ⊗[K] InfiniteAdeleRing K)ˣ) (a t : (InfiniteAdeleRing K)ˣ)
    (hN : normString K L (InfiniteAdeleRing K) σ (diagUnits2 α β) =
      toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 a (a * t)))
    (u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
      ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) :
    Algebra.norm (InfiniteAdeleRing K)
        (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) :
          (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) = (t : InfiniteAdeleRing K) := by
  obtain ⟨hα, hβ⟩ := norm_eq_of_normString_diagUnits2 K L σ hgen α β a (a * t) hN
  have hu : ∀ v : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker,
      Algebra.norm (InfiniteAdeleRing K) (((v : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : L ⊗[K] InfiniteAdeleRing K) = 1 := by
    intro v
    have h := congrArg Units.val (v.2 : Units.map (Algebra.norm (InfiniteAdeleRing K) :
      (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K) (v : (L ⊗[K] InfiniteAdeleRing K)ˣ) = 1)
    simpa [Units.coe_map] using h
  have hαu : Algebra.norm (InfiniteAdeleRing K) (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) :
      L ⊗[K] InfiniteAdeleRing K) = a := by
    rw [Units.val_mul, map_mul, hα, hu, mul_one]
  have hβu : Algebra.norm (InfiniteAdeleRing K) (((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) :
      L ⊗[K] InfiniteAdeleRing K) = a * t := by
    rw [Units.val_mul, map_mul, hβ, hu, mul_one, Units.val_mul]
  have hinv : Algebra.norm (InfiniteAdeleRing K) ((((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ :
      (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K)) = ((a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) := by
    have h1 : Algebra.norm (InfiniteAdeleRing K) ((((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ :
        (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K)) * (a : InfiniteAdeleRing K) = 1 := by
      rw [← hαu, ← map_mul, Units.inv_mul, map_one]
    have h2 : (a : InfiniteAdeleRing K) * ((a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) = 1 := Units.mul_inv a
    exact left_inv_eq_right_inv h1 h2
  rw [Units.val_mul, map_mul, hinv, hβu, ← mul_assoc, Units.inv_mul, one_mul]

end Arch
p2m_reactivate "P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_prod_norm_pow_mul_integral_ker_norm_integral_twistedLogWeight_eq_add_norm_sq_mul_log_mul_of_isComplex.A5RN"
end A5RN
p2m_reactivate "P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_prod_norm_pow_mul_integral_ker_norm_integral_twistedLogWeight_eq_add_norm_sq_mul_log_mul_of_isComplex.A5RN"

namespace A5RC

theorem isUnit_infiniteAdeleRing_iff (K : Type) [Field K] [NumberField K] (x : InfiniteAdeleRing K) :
    IsUnit x ↔ ∀ v : InfinitePlace K, x v ≠ 0 := by
  rw [show IsUnit x ↔ ∀ v : InfinitePlace K, IsUnit (x v) from Pi.isUnit_iff]
  exact forall_congr' fun v => isUnit_iff_ne_zero

end A5RC
p2m_reactivate "P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_prod_norm_pow_mul_integral_ker_norm_integral_twistedLogWeight_eq_add_norm_sq_mul_log_mul_of_isComplex.A5RN"

set_option maxHeartbeats 4000000 in
open scoped Classical in
open A5RC in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)ˣ] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)ˣ]
    (θ : Measure ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) [θ.IsHaarMeasure]
    (Φ : (Fin 3 → NumberField.mixedEmbedding.mixedSpace L) → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hΦc : HasCompactSupport Φ)
    (hΦu : ∃ C : Set ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ), IsCompact C ∧
        ∀ p ∈ tsupport Φ, ∃ q ∈ C,
          p 0 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((q.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) ∧
          p 1 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((q.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))))
    (w : NumberField.InfinitePlace K) (hw : w.IsComplex) :
    ∃ A B : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) A ∧ ContDiff ℝ (⊤ : ℕ∞) B ∧ HasCompactSupport A ∧ HasCompactSupport B ∧
      (∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport A ∪ tsupport B, ∃ q ∈ Ca,
          p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) ∧
      ∀ (a t : (InfiniteAdeleRing K)ˣ), (∀ v : NumberField.InfinitePlace K, (t : InfiniteAdeleRing K) v ≠ 1) →
      ∀ (α β : (L ⊗[K] InfiniteAdeleRing K)ˣ),
        AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (diagUnits2 α β) =
          AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 a (a * t)) →
        (∀ u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker,
            Integrable (fun y : (L ⊗[K] InfiniteAdeleRing K) => Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
                 NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * y))] * (((∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
                    (w'.mult : ℝ) * Real.log (1 + ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L y)‖ ^ 2)) : ℝ) : ℂ)) lam) ∧
        Integrable (fun u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker =>
            ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
                 NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * y))] * (((∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
                    (w'.mult : ℝ) * Real.log (1 + ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L y)‖ ^ 2)) : ℝ) : ℂ) ∂lam) (θ.prod θ) ∧
        (∀ u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker, Integrable (fun y : (L ⊗[K] InfiniteAdeleRing K) => Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)]) lam) ∧
        Integrable (fun u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker => ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)] ∂lam) (θ.prod θ) ∧
        ((∏ v : NumberField.InfinitePlace K,
            ‖NumberField.AdelicLevel.archEval K v ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ v.mult : ℝ) : ℂ) *
          ∫ u, ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
                 NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * y))] * (((∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
                    (w'.mult : ℝ) * Real.log (1 + ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L y)‖ ^ 2)) : ℝ) : ℂ) ∂lam ∂(θ.prod θ) =
        -2 * (Module.finrank K L : ℂ) * (((w.mult : ℝ) * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
            ∫ u, ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)] ∂lam ∂(θ.prod θ) +
          A ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] +
          ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) * B ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] := by
  classical
  haveI hTR := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  haveI := AutomorphicForm.t2Space_tensor K L (InfiniteAdeleRing K)
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L (InfiniteAdeleRing K)
  haveI := C3Inst.secondCountableTopology_E K L
  haveI := C3Inst.secondCountableTopology_unitsE K L
  haveI := C3Inst.locallyCompactSpace_unitsE K L
  haveI : IsTopologicalGroup (L ⊗[K] InfiniteAdeleRing K)ˣ := inferInstance
  have hNc : Continuous (Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)) :=
    Continuous.units_map _ (C3Inst.continuous_algebraNorm K L)
  have hU1closed : IsClosed ((Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker : Set (L ⊗[K] InfiniteAdeleRing K)ˣ) := by
    rw [MonoidHom.coe_ker]; exact isClosed_singleton.preimage hNc
  haveI : SecondCountableTopology ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker := hU1closed.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SigmaCompactSpace ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : BorelSpace ((↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker)) := Prod.borelSpace
  haveI : SigmaFinite θ := Measure.IsHaarMeasure.sigmaFinite θ
  haveI : (θ.prod θ).IsHaarMeasure := inferInstance
  set S : Finset (NumberField.InfinitePlace L) := Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w) with hS

  have hL : ∀ w' : NumberField.InfinitePlace L, ∃ A B : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ,
      w'.comap (algebraMap K L) = w →
        ContDiff ℝ (⊤ : ℕ∞) A ∧ ContDiff ℝ (⊤ : ℕ∞) B ∧ HasCompactSupport A ∧ HasCompactSupport B ∧
        (∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
          ∀ p ∈ tsupport A ∪ tsupport B, ∃ q ∈ Ca,
            p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                  NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) ∧
        ∀ (a t : (InfiniteAdeleRing K)ˣ), (∀ v : NumberField.InfinitePlace K, (t : InfiniteAdeleRing K) v ≠ 1) →
        ∀ (α β : (L ⊗[K] InfiniteAdeleRing K)ˣ),
          AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (diagUnits2 α β) =
            AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 a (a * t)) →
        ∀ (Mu : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) → ((L ⊗[K] InfiniteAdeleRing K) →ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K))),
          (∀ u, (∀ y, AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (Mu u y) - (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * Mu u y =
                ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K)) • y) ∧
            (∀ y, Mu u (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * y) =
                ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K)) • y)) →
          Integrable (fun u : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) =>
            ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)] *
              (Real.log (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 +
                ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (Mu u y))‖ ^ 2) : ℂ) ∂lam) (θ.prod θ) ∧
          ∫ u, ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)] *
              (Real.log (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 +
                ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (Mu u y))‖ ^ 2) : ℂ) ∂lam ∂(θ.prod θ) =
            A ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] +
            ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 *
                Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
              B ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] := by
    intro w'
    by_cases hww : w'.comap (algebraMap K L) = w
    · have hw'c : w'.IsComplex := by
        rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex]
        intro hr
        have h1 : (w'.comap (algebraMap K L)).IsReal := hr.comap (algebraMap K L)
        rw [hww] at h1
        exact (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hw) h1
      obtain ⟨A, B, h⟩ :=
        AutomorphicForm.exists_contDiff_hasCompactSupport_integral_ker_norm_integral_mul_log_sq_add_norm_resolvent_sq_eq_add_norm_sq_mul_log_mul_of_isComplex_isComplex
          K L σ hgen hdeg lam θ Φ hΦ hΦc hΦu w w' hww hw hw'c
      exact ⟨A, B, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hww⟩
  choose Aw Bw hLw using hL
  have hmemS : ∀ w' ∈ S, w'.comap (algebraMap K L) = w := fun w' hw' => by simpa [hS] using hw'
  set A : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ := fun p => ∑ w' ∈ S, (w'.mult : ℂ) * Aw w' p with hA
  set B : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ := fun p => ∑ w' ∈ S, (w'.mult : ℂ) * Bw w' p with hB
  have hAs : ContDiff ℝ (⊤ : ℕ∞) A := by
    simp only [hA]
    exact ContDiff.sum fun w' hw' => contDiff_const.mul (hLw w' (hmemS w' hw')).1
  have hBs : ContDiff ℝ (⊤ : ℕ∞) B := by
    simp only [hB]
    exact ContDiff.sum fun w' hw' => contDiff_const.mul (hLw w' (hmemS w' hw')).2.1

  set Ksupp : Set (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) :=
    ⋃ w' ∈ S, (tsupport (Aw w') ∪ tsupport (Bw w')) with hKsupp
  have hKc : IsCompact Ksupp :=
    S.isCompact_biUnion fun w' hw' => ((hLw w' (hmemS w' hw')).2.2.1.isCompact.union (hLw w' (hmemS w' hw')).2.2.2.1.isCompact)
  have hA0 : ∀ p, p ∉ Ksupp → A p = 0 := by
    intro p hp
    simp only [hA]
    refine Finset.sum_eq_zero fun w' hw' => ?_
    have : p ∉ tsupport (Aw w') := fun h => hp (by simp only [hKsupp, Set.mem_iUnion, Set.mem_union]; exact ⟨w', hw', Or.inl h⟩)
    rw [image_eq_zero_of_notMem_tsupport this, mul_zero]
  have hB0 : ∀ p, p ∉ Ksupp → B p = 0 := by
    intro p hp
    simp only [hB]
    refine Finset.sum_eq_zero fun w' hw' => ?_
    have : p ∉ tsupport (Bw w') := fun h => hp (by simp only [hKsupp, Set.mem_iUnion, Set.mem_union]; exact ⟨w', hw', Or.inr h⟩)
    rw [image_eq_zero_of_notMem_tsupport this, mul_zero]
  have hAc : HasCompactSupport A := HasCompactSupport.intro hKc hA0
  have hBc : HasCompactSupport B := HasCompactSupport.intro hKc hB0
  have hCa : ∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
      ∀ p ∈ tsupport A ∪ tsupport B, ∃ q ∈ Ca,
        p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
              NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)] := by
    have hCaw : ∀ w' : NumberField.InfinitePlace L, ∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ),
        w'.comap (algebraMap K L) = w → (IsCompact Ca ∧ ∀ p ∈ tsupport (Aw w') ∪ tsupport (Bw w'), ∃ q ∈ Ca,
          p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) := by
      intro w'
      by_cases h : w'.comap (algebraMap K L) = w
      · obtain ⟨Ca, hCa, hmem⟩ := (hLw w' h).2.2.2.2.1
        exact ⟨Ca, fun _ => ⟨hCa, hmem⟩⟩
      · exact ⟨∅, fun h' => absurd h' h⟩
    choose Ca hCa using hCaw
    refine ⟨⋃ w' ∈ S, Ca w', S.isCompact_biUnion fun w' hw' => (hCa w' (hmemS w' hw')).1, ?_⟩
    intro p hp
    have hpK : p ∈ Ksupp := by
      have hsubA : tsupport A ⊆ Ksupp := closure_minimal (fun x hx => by by_contra h; exact hx (hA0 x h)) hKc.isClosed
      have hsubB : tsupport B ⊆ Ksupp := closure_minimal (fun x hx => by by_contra h; exact hx (hB0 x h)) hKc.isClosed
      exact hp.elim (fun h => hsubA h) (fun h => hsubB h)
    simp only [hKsupp, Set.mem_iUnion] at hpK
    obtain ⟨w', hw', hp'⟩ := hpK
    obtain ⟨q, hq, hpq⟩ := (hCa w' (hmemS w' hw')).2 p hp'
    exact ⟨q, Set.mem_biUnion hw' hq, hpq⟩
  refine ⟨A, B, hAs, hBs, hAc, hBc, hCa, ?_⟩
  intro a t ht α β hN

  have hcU : IsUnit ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K)) := by
    rw [isUnit_infiniteAdeleRing_iff]
    intro v
    have hv : ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K)) v = 1 - (t : InfiniteAdeleRing K) v := rfl
    rw [hv, sub_ne_zero]
    exact fun h => ht v h.symm
  set c : (InfiniteAdeleRing K)ˣ := hcU.unit with hc
  have hcval : (c : InfiniteAdeleRing K) = 1 - (t : InfiniteAdeleRing K) := hcU.unit_spec

  have hNr : ∀ u : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker), (c : InfiniteAdeleRing K) = 1 - Algebra.norm (InfiniteAdeleRing K) (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) := by
    intro u; rw [hcval, A5RN.norm_inv_mul_eq K L σ hgen α β a t hN u]
  have hslice : ∀ u : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker), HasCompactSupport (fun m : NumberField.mixedEmbedding.mixedSpace L => Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), m]) := by
    intro u
    refine HasCompactSupport.intro (hΦc.image (continuous_apply 2)) fun m hm => ?_
    by_contra hne
    exact hm ⟨_, subset_tsupport Φ hne, by simp⟩
  have hA_u := fun u : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) =>
    AutomorphicForm.exists_linearMap_prod_norm_pow_mul_integral_comp_sigmaTensor_sub_mul_twistedLogWeight_eq_add_sum
      K L σ hgen hdeg lam w _ c (hNr u)
      (fun m : NumberField.mixedEmbedding.mixedSpace L => Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), m])
      (hΦ.continuous.comp (Continuous.matrixVecCons continuous_const (Continuous.matrixVecCons continuous_const
        (Continuous.matrixVecCons continuous_id continuous_const))))
      (hslice u)
  choose Mu hMuc hMu1 hMu2 hItw hIpl hIpot hId using hA_u

  obtain ⟨C, hCc, hCG⟩ := hΦu
  have hιh : IsHomeomorph (fun z : (L ⊗[K] InfiniteAdeleRing K) => NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L z)) :=
    (NumberField.InfiniteAdeleRing.isHomeomorph_ringEquiv_mixedSpace L).comp (AutomorphicForm.archIdentHomeomorph K L).isHomeomorph
  have hιc : Continuous (fun z : (L ⊗[K] InfiniteAdeleRing K) => NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L z)) :=
    hιh.continuous
  have hιinj : Function.Injective (fun z : (L ⊗[K] InfiniteAdeleRing K) => NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L z)) :=
    (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L).injective.comp (AutomorphicForm.archIdentEquiv K L).injective

  set Ky : Set (L ⊗[K] InfiniteAdeleRing K) := (fun z : (L ⊗[K] InfiniteAdeleRing K) => NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L z)) ⁻¹'
    ((fun p : Fin 3 → NumberField.mixedEmbedding.mixedSpace L => p 2) '' tsupport Φ) with hKy
  have hKyc : IsCompact Ky := hιh.isClosedEmbedding.isCompact_preimage (hΦc.image (continuous_apply 2))

  have hF0 : ∀ (u : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker)) (y : (L ⊗[K] InfiniteAdeleRing K)), y ∉ Ky → Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y))] = 0 := by
    intro u y hy
    by_contra hne
    exact hy ⟨_, subset_tsupport Φ hne, by simp⟩
  have hFc : Continuous (fun q : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) × (L ⊗[K] InfiniteAdeleRing K) => Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (q.1.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (q.1.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L q.2)]) := by
    have h0 : Continuous fun q : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) × (L ⊗[K] InfiniteAdeleRing K) => NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (q.1.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) :=
      hιc.comp (Units.continuous_val.comp (continuous_const.mul (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))))
    have h1 : Continuous fun q : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) × (L ⊗[K] InfiniteAdeleRing K) => NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (q.1.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) :=
      hιc.comp (Units.continuous_val.comp (continuous_const.mul (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))))
    have h2 : Continuous fun q : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) × (L ⊗[K] InfiniteAdeleRing K) => NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L q.2) :=
      hιc.comp continuous_snd
    exact hΦ.continuous.comp (Continuous.matrixVecCons h0 (Continuous.matrixVecCons h1 (Continuous.matrixVecCons h2 continuous_const)))
  have hIpl_cont : Continuous fun u : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) => ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y))] ∂lam := by
    have heq : (fun u : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) => ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y))] ∂lam) = fun u : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) => ∫ y in Ky, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y))] ∂lam := by
      funext u
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => hF0 u y hy)]
    rw [heq]
    exact continuous_parametric_integral_of_continuous hFc hKyc

  have hce : Topology.IsClosedEmbedding (fun u : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) => ((u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ), (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ))) :=
    hU1closed.isClosedEmbedding_subtypeVal.prodMap hU1closed.isClosedEmbedding_subtypeVal
  set Ku : Set (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) := (fun u : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) => ((u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ), (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ))) ⁻¹'
    ((fun p : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ => (α * p.1, β * p.2)) ⁻¹' C) with hKu
  have hKuc : IsCompact Ku := hce.isCompact_preimage ((Homeomorph.mulLeft (α, β)).isClosedEmbedding.isCompact_preimage hCc)
  have hu0 : ∀ (u : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker)) (y : (L ⊗[K] InfiniteAdeleRing K)), u ∉ Ku → Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y))] = 0 := by
    intro u y hu
    by_contra hne
    obtain ⟨q, hqC, hq0, hq1⟩ := hCG _ (subset_tsupport Φ hne)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hq0 hq1
    have e0 : α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) = q.1 := Units.ext (hιinj hq0)
    have e1 : β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) = q.2 := Units.ext (hιinj hq1)
    exact hu (by show (α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ), β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) ∈ C; rw [e0, e1]; exact hqC)
  have hIpl_supp : HasCompactSupport fun u : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) => ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y))] ∂lam := by
    refine HasCompactSupport.intro hKuc fun u hu => ?_
    simp only [hu0 u _ hu, integral_zero]
  have hIplInt : Integrable (fun u : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) => ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y))] ∂lam) (θ.prod θ) :=
    hIpl_cont.integrable_of_hasCompactSupport hIpl_supp

  have hLay : ∀ w' ∈ S,
      Integrable (fun u : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) => ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y))] *
          (Real.log (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 +
            ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (Mu u y))‖ ^ 2) : ℂ) ∂lam) (θ.prod θ) ∧
      ∫ u, ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y))] *
          (Real.log (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 +
            ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (Mu u y))‖ ^ 2) : ℂ) ∂lam ∂(θ.prod θ) =
        Aw w' ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] +
        ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 *
              Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
          Bw w' ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] := by
    intro w' hw'
    have h := (hLw w' (hmemS w' hw')).2.2.2.2.2 a t ht α β hN Mu (fun u => ⟨fun y => ?_, fun y => ?_⟩)
    · exact h
    · rw [hMu1 u y, hcval]
    · rw [hMu2 u y, hcval]

  have hK0 : ((∏ v : NumberField.InfinitePlace K,
      ‖NumberField.AdelicLevel.archEval K v (c : InfiniteAdeleRing K)‖ ^ v.mult : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    refine Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ (norm_ne_zero_iff.mpr ?_)
    rw [hcval]
    show ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K)) v ≠ 0
    have hv : ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K)) v = 1 - (t : InfiniteAdeleRing K) v := rfl
    rw [hv, sub_ne_zero]
    exact fun h => ht v h.symm

  simp only [hcval] at hId hIpot hK0
  have hRHSint : Integrable (fun u : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) =>
      -2 * (Module.finrank K L : ℂ) *
          (((w.mult : ℝ) * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
          ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y))] ∂lam +
        ∑ w' ∈ S, (w'.mult : ℂ) * ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y))] *
            (Real.log (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 +
              ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (Mu u y))‖ ^ 2) : ℂ) ∂lam) (θ.prod θ) := by
    refine (hIplInt.const_mul _).add ?_
    refine integrable_finsetSum _ fun w' hw' => ?_
    exact (hLay w' hw').1.const_mul _
  have hItwInt : Integrable (fun u : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) => ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * y))] * (((∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
            (w'.mult : ℝ) * Real.log (1 + ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L y)‖ ^ 2)) : ℝ) : ℂ) ∂lam) (θ.prod θ) := by
    have heq : (fun u : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) => ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * y))] * (((∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
            (w'.mult : ℝ) * Real.log (1 + ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L y)‖ ^ 2)) : ℝ) : ℂ) ∂lam) =
        fun u : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) => ((∏ v : NumberField.InfinitePlace K,
            ‖NumberField.AdelicLevel.archEval K v ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ v.mult : ℝ) : ℂ)⁻¹ *
          (-2 * (Module.finrank K L : ℂ) *
            (((w.mult : ℝ) * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
            ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y))] ∂lam +
          ∑ w' ∈ S, (w'.mult : ℂ) * ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y))] *
              (Real.log (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 +
                ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (Mu u y))‖ ^ 2) : ℂ) ∂lam) := by
      funext u
      rw [eq_inv_mul_iff_mul_eq₀ hK0]
      exact hId u
    rw [heq]
    exact hRHSint.const_mul _
  refine ⟨fun u => hItw u, hItwInt, fun u => hIpl u, hIplInt, ?_⟩

  rw [← integral_const_mul, show (fun u : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) => ((∏ v : NumberField.InfinitePlace K,
      ‖NumberField.AdelicLevel.archEval K v ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ v.mult : ℝ) : ℂ) *
      ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * y))] * (((∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
            (w'.mult : ℝ) * Real.log (1 + ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L y)‖ ^ 2)) : ℝ) : ℂ) ∂lam) =
      fun u : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) => -2 * (Module.finrank K L : ℂ) *
          (((w.mult : ℝ) * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
          ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y))] ∂lam +
        ∑ w' ∈ S, (w'.mult : ℂ) * ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y))] *
            (Real.log (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 +
              ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (Mu u y))‖ ^ 2) : ℂ) ∂lam from funext hId]
  rw [integral_add (hIplInt.const_mul _) (integrable_finsetSum _ fun w' hw' => (hLay w' hw').1.const_mul _),
    integral_const_mul, integral_finsetSum _ fun w' hw' => (hLay w' hw').1.const_mul _]
  simp_rw [integral_const_mul]
  rw [Finset.sum_congr rfl fun w' hw' => by rw [(hLay w' hw').2]]
  simp only [hA, hB, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  have hcomm : ∀ x ∈ S, ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 *
              Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
      ((x.mult : ℂ) * Bw x ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)]) =
      (x.mult : ℂ) * (((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 *
              Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
        Bw x ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)]) := fun x _ => by ring
  rw [Finset.sum_congr rfl hcomm, add_assoc]

end S_AutomorphicForm_exists_contDiff_hasCompactSupport_prod_norm_pow_mul_integral_ker_norm_integral_twistedLogWeight_eq_add_norm_sq_mul_log_mul_of_isComplex
end P2MW
export P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_prod_norm_pow_mul_integral_ker_norm_integral_twistedLogWeight_eq_add_norm_sq_mul_log_mul_of_isComplex (solution)
