-- Prove2me | solution 1 for AutomorphicForm.exists_nhds_forall_pow_eq_and_continuousOn_and_eq_of_isTwistedWeightedOrbitalIntegralOn_comp_toTensorGL_scalar_mul_infiniteAdeleRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/e1bf884d-ae70-5ba8-8e15-c272aefb8814

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_AutomorphicForm_IsTwistedWeightedOrbitalIntegralOn_unique_of_isRegularSemisimple_normString_of_forall_twistedCentralizer_mul_eq
import Theorems.Thm_AutomorphicForm_exists_isTwistedSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_normString_of_hasCompactSupport
import Theorems.Thm_NumberField_InfiniteAdeleRing_isHomeomorph_ringEquiv_mixedSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_nhds_forall_pow_eq_and_continuousOn_and_eq_of_isTwistedWeightedOrbitalIntegralOn_comp_toTensorGL_scalar_mul_infiniteAdeleRing

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField IsDedekindDomain TopologicalSpace

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace S5C25

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

section Topology

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

theorem t2Space_GL [T2Space A] : T2Space (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  exact Units.isEmbedding_embedProduct.t2Space

theorem secondCountableTopology_GL [SecondCountableTopology A] :
    SecondCountableTopology (GL (Fin 2) A) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem locallyCompactSpace_GL [T2Space A] [LocallyCompactSpace A] :
    LocallyCompactSpace (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → A))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

end Topology

section TensorTopology

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

theorem secondCountableTopology_tensor [SecondCountableTopology A] :
    SecondCountableTopology (L ⊗[K] A) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  let ι := Module.Free.ChooseBasisIndex A (L ⊗[K] A)
  haveI : Fintype ι := Module.Free.ChooseBasisIndex.fintype A (L ⊗[K] A)
  let b : Module.Basis ι A (L ⊗[K] A) := Module.Free.chooseBasis A (L ⊗[K] A)
  let e : (L ⊗[K] A) ≃ₗ[A] (ι → A) := b.equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let eh : (L ⊗[K] A) ≃ₜ (ι → A) :=
    { toEquiv := e.toEquiv, continuous_toFun := h1, continuous_invFun := h2 }
  exact eh.isInducing.secondCountableTopology

theorem continuous_sigmaTensor (σ : L ≃ₐ[K] L) : Continuous (AutomorphicForm.sigmaTensor K L A σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  have h := IsModuleTopology.continuous_of_linearMap
    (TensorProduct.RightActions.AlgebraMap.baseChange K L L A σ.toAlgHom).toLinearMap
  exact h

theorem continuous_sigmaGL (σ : L ≃ₐ[K] L) : Continuous (AutomorphicForm.sigmaGL K L A σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  refine Continuous.units_map _ ?_
  exact continuous_id.matrix_map (continuous_sigmaTensor K L A σ)

end TensorTopology

section LiftA
variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A]

theorem lift_factsA (σ : L ≃ₐ[K] L)
    (γ : GL (Fin 2) A) (hγ : IsRegularSemisimple γ)
    (hγ₀₁ : (γ : Matrix (Fin 2) (Fin 2) A) 0 1 = 0)
    (hγ₁₀ : (γ : Matrix (Fin 2) (Fin 2) A) 1 0 = 0)
    (δ : GL (Fin 2) (L ⊗[K] A))
    (hδ : normString K L A σ δ = toTensorGL K L A γ) :
    IsDiag δ ∧ (∀ t ∈ twistedCentralizer K L A σ δ, IsDiag t) ∧
      IsRegularSemisimple (normString K L A σ δ) := by
  obtain ⟨γ', hγ'⟩ : ∃ γ' : GL (Fin 2) (L ⊗[K] A), γ' = toTensorGL K L A γ := ⟨_, rfl⟩
  have hδ' : normString K L A σ δ = γ' := hδ.trans hγ'.symm
  have hγ'01 : (γ' : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0 := by
    rw [hγ', toTensorGL_apply, hγ₀₁, TensorProduct.tmul_zero]
  have hγ'10 : (γ' : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0 := by
    rw [hγ', toTensorGL_apply, hγ₁₀, TensorProduct.tmul_zero]
  have hγ'u : IsUnit ((γ' : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 -
      (γ' : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1) := by
    have h := (isUnit_sub_of_isRegularSemisimple γ hγ₀₁ hγ₁₀ hγ).map
      (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)
    rw [map_sub, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeRight_apply] at h
    rw [hγ', toTensorGL_apply, toTensorGL_apply]
    exact h
  refine ⟨?_, ?_, ?_⟩
  · exact offdiag_eq_zero_of_commute γ' δ hγ'01 hγ'10 hγ'u
      (by rw [hγ']; exact commute_of_normString_eq K L A σ δ γ hδ)
  · intro t ht
    exact offdiag_eq_zero_of_commute γ' t hγ'01 hγ'10 hγ'u
      (by rw [← hδ']; exact mul_normString_comm K L A σ δ t ht)
  · rw [hδ']
    show IsUnit _
    have e : Matrix.trace (γ' : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) ^ 2 -
        4 * Matrix.det (γ' : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
        ((γ' : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 - (γ' : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1) ^ 2 := by
      rw [Matrix.trace_fin_two, Matrix.det_fin_two, hγ'01, hγ'10]; ring
    rw [e]
    exact hγ'u.pow 2

end LiftA

section ArchHelpers
variable (K : Type) [Field K] [NumberField K]

omit [NumberField K] in
theorem secondCountableTopology_completion (v : InfinitePlace K) : SecondCountableTopology v.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology

theorem secondCountableTopology_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI := secondCountableTopology_completion K
  exact inferInstanceAs (SecondCountableTopology ((v : InfinitePlace K) → v.Completion))

theorem continuous_scalar (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous fun ε : Rˣ => (Matrix.GeneralLinearGroup.scalar (Fin 2) ε : GL (Fin 2) R) := by
  rw [Units.continuous_iff]
  constructor
  · refine ((continuous_pi fun _ : Fin 2 => Units.continuous_val).matrix_diagonal).congr fun ε => ?_
    rfl
  · refine ((continuous_pi fun _ : Fin 2 => (Units.continuous_coe_inv : Continuous fun u : Rˣ => ((u⁻¹ : Rˣ) : R))).matrix_diagonal).congr fun ε => ?_
    show Matrix.diagonal (fun _ : Fin 2 => ((ε⁻¹ : Rˣ) : R)) =
      (((Matrix.GeneralLinearGroup.scalar (Fin 2) ε)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
    rw [← map_inv]
    rfl

variable (L : Type) [Field L] [NumberField L] [Algebra K L]

theorem continuous_toTensorGL_scalar :
    Continuous fun ε : (InfiniteAdeleRing K)ˣ =>
      toTensorGL K L (InfiniteAdeleRing K) (Matrix.GeneralLinearGroup.scalar (Fin 2) ε) := by
  haveI := isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  set f : InfiniteAdeleRing K →+* L ⊗[K] InfiniteAdeleRing K :=
    (Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom with hf
  have hfc : Continuous f := by
    have h := IsModuleTopology.continuous_of_linearMap
      (Algebra.linearMap (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K))
    exact h
  have h1 : Continuous (toTensorGL K L (InfiniteAdeleRing K)) := by
    refine Continuous.units_map _ ?_
    exact continuous_id.matrix_map hfc
  exact h1.comp (continuous_scalar (InfiniteAdeleRing K))

end ArchHelpers

section Roots
variable (K : Type) [Field K] [NumberField K]

noncomputable def mroot (n : ℕ) (p : mixedEmbedding.mixedSpace K) : mixedEmbedding.mixedSpace K :=
  (fun w => (p.1 w) ^ ((n : ℝ)⁻¹), fun w => (p.2 w) ^ ((n : ℂ)⁻¹))

noncomputable def mrootInv (n : ℕ) (p : mixedEmbedding.mixedSpace K) : mixedEmbedding.mixedSpace K :=
  (fun w => (p.1 w) ^ (-(n : ℝ)⁻¹), fun w => (p.2 w) ^ (-(n : ℂ)⁻¹))

def good : Set (mixedEmbedding.mixedSpace K) :=
  {p | (∀ w, 0 < p.1 w) ∧ ∀ w, p.2 w ∈ Complex.slitPlane}

theorem isOpen_good : IsOpen (good K) := by
  have h1 : IsOpen {p : mixedEmbedding.mixedSpace K | ∀ w, 0 < p.1 w} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun w => isOpen_lt continuous_const ((continuous_apply w).comp continuous_fst)
  have h2 : IsOpen {p : mixedEmbedding.mixedSpace K | ∀ w, p.2 w ∈ Complex.slitPlane} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun w =>
      Complex.isOpen_slitPlane.preimage ((continuous_apply w).comp continuous_snd)
  exact h1.inter h2

theorem one_mem_good : (1 : mixedEmbedding.mixedSpace K) ∈ good K :=
  ⟨fun _ => by simp, fun _ => by simp [Complex.slitPlane, Complex.one_re]⟩

theorem mroot_pow {n : ℕ} (hn : n ≠ 0) {p : mixedEmbedding.mixedSpace K} (hp : p ∈ good K) :
    mroot K n p ^ n = p := by
  ext w
  · simp only [mroot, Prod.pow_fst, Pi.pow_apply]
    exact Real.rpow_inv_natCast_pow (hp.1 w).le hn
  · simp only [mroot, Prod.pow_snd, Pi.pow_apply]
    exact Complex.cpow_nat_inv_pow _ hn

theorem mroot_one (n : ℕ) : mroot K n 1 = 1 := by
  ext w
  · simp [mroot]
  · simp [mroot]

theorem mroot_mul_mrootInv {n : ℕ} {p : mixedEmbedding.mixedSpace K} (hp : p ∈ good K) :
    mroot K n p * mrootInv K n p = 1 := by
  ext w
  · simp only [mroot, mrootInv, Prod.fst_mul, Pi.mul_apply, Prod.fst_one, Pi.one_apply]
    rw [Real.rpow_neg (hp.1 w).le, mul_inv_cancel₀]
    exact (Real.rpow_pos_of_pos (hp.1 w) _).ne'
  · simp only [mroot, mrootInv, Prod.snd_mul, Pi.mul_apply, Prod.snd_one, Pi.one_apply]
    rw [Complex.cpow_neg, mul_inv_cancel₀]
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.slitPlane_ne_zero (hp.2 w)))

theorem continuousOn_mroot (n : ℕ) : ContinuousOn (mroot K n) (good K) := by
  refine ContinuousOn.prodMk ?_ ?_
  · refine continuousOn_pi.2 fun w => ?_
    exact ((Real.continuous_rpow_const (by positivity)).comp
      ((continuous_apply w).comp continuous_fst)).continuousOn
  · refine continuousOn_pi.2 fun w => ?_
    intro p hp
    have hc : Continuous fun q : mixedEmbedding.mixedSpace K => q.2 w := (continuous_apply w).comp continuous_snd
    exact (hc.continuousAt.cpow continuousAt_const (hp.2 w)).continuousWithinAt

theorem continuousOn_mrootInv (n : ℕ) : ContinuousOn (mrootInv K n) (good K) := by
  refine ContinuousOn.prodMk ?_ ?_
  · refine continuousOn_pi.2 fun w => ?_
    intro p hp
    have hc : Continuous fun q : mixedEmbedding.mixedSpace K => q.1 w := (continuous_apply w).comp continuous_fst
    exact (hc.continuousAt.rpow_const (Or.inl (hp.1 w).ne')).continuousWithinAt
  · refine continuousOn_pi.2 fun w => ?_
    intro p hp
    have hc : Continuous fun q : mixedEmbedding.mixedSpace K => q.2 w := (continuous_apply w).comp continuous_snd
    exact (hc.continuousAt.cpow continuousAt_const (hp.2 w)).continuousWithinAt

end Roots

end S5C25
p2m_reactivate "P2MW.S_AutomorphicForm_exists_nhds_forall_pow_eq_and_continuousOn_and_eq_of_isTwistedWeightedOrbitalIntegralOn_comp_toTensorGL_scalar_mul_infiniteAdeleRing.S5C25"

open S5C25 in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (μ : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) _ _
      (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)) μ)
    (wt : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ) (hwtc : Continuous wt)
    (hwt : ∀ t x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
      (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 1 = 0 →
      (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 1 0 = 0 → wt (t * x) = wt x)
    (γ : GL (Fin 2) (InfiniteAdeleRing K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (hγ₀₁ : (γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 1 = 0)
    (hγ₁₀ : (γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0 = 0)
    (δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hδ : AutomorphicForm.normString K L (InfiniteAdeleRing K) σ δ = AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) γ)
    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ)) (hτ' : τ'.IsHaarMeasure)
    (φ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) :
    ∃ W ∈ nhds (1 : InfiniteAdeleRing K), ∃ ρ : InfiniteAdeleRing K → (InfiniteAdeleRing K)ˣ, ∃ g : InfiniteAdeleRing K → ℂ,
      ((ρ 1 : InfiniteAdeleRing K) = 1) ∧
      (∀ ε ∈ W, ((ρ ε : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) ^ Module.finrank K L = ε) ∧
      ContinuousOn (fun ε => ((ρ ε : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) W ∧
      ContinuousOn g W ∧
      ∀ ε ∈ W, ∀ J : ℂ,
        AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ μ wt δ τ'
          (fun y => φ (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K)
            (Matrix.GeneralLinearGroup.scalar (Fin 2) (ρ ε)) * y)) J →
        J = g ε := by
  classical

  haveI := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  haveI := AutomorphicForm.t2Space_tensor K L (InfiniteAdeleRing K)
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L (InfiniteAdeleRing K)
  haveI := S5C25.secondCountableTopology_infiniteAdeleRing K
  haveI := S5C25.secondCountableTopology_tensor K L (InfiniteAdeleRing K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (InfiniteAdeleRing K)
  haveI := S5C25.t2Space_GL (L ⊗[K] InfiniteAdeleRing K)
  haveI := S5C25.secondCountableTopology_GL (L ⊗[K] InfiniteAdeleRing K)
  haveI := S5C25.locallyCompactSpace_GL (L ⊗[K] InfiniteAdeleRing K)
  letI mGL : MeasurableSpace (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :=
    AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := AutomorphicForm.borelSpace_glBorelOf _
  haveI := hμ
  haveI := hτ'
  have hℓ0 : Module.finrank K L ≠ 0 := Module.finrank_pos.ne'
  have hσ : σ ^ Module.finrank K L = 1 := S5C25.sigma_pow_finrank K L σ
  obtain ⟨hδd, hTd, hreg⟩ := S5C25.lift_factsA K L (InfiniteAdeleRing K) σ γ hγ hγ₀₁ hγ₁₀ δ hδ

  set ι := InfiniteAdeleRing.ringEquiv_mixedSpace K with hι
  have hιh := NumberField.InfiniteAdeleRing.isHomeomorph_ringEquiv_mixedSpace K
  have hιc : Continuous ι := hιh.continuous
  have hιsc : Continuous ι.symm := by
    have h1 : (ι.symm : mixedEmbedding.mixedSpace K → InfiniteAdeleRing K) = (hιh.homeomorph ι).symm := by
      funext y
      apply ι.injective
      rw [RingEquiv.apply_symm_apply]
      exact ((hιh.homeomorph ι).apply_symm_apply y).symm
    rw [h1]
    exact (hιh.homeomorph ι).symm.continuous
  set W₀ : Set (InfiniteAdeleRing K) := ι ⁻¹' S5C25.good K with hW₀
  have hW₀o : IsOpen W₀ := (S5C25.isOpen_good K).preimage hιc
  have h1W₀ : (1 : InfiniteAdeleRing K) ∈ W₀ := by
    show ι 1 ∈ S5C25.good K
    rw [map_one]; exact S5C25.one_mem_good K
  set ρ₀ : InfiniteAdeleRing K → InfiniteAdeleRing K := fun ε => ι.symm (S5C25.mroot K (Module.finrank K L) (ι ε)) with hρ₀
  set ρ₁ : InfiniteAdeleRing K → InfiniteAdeleRing K := fun ε => ι.symm (S5C25.mrootInv K (Module.finrank K L) (ι ε)) with hρ₁
  have hρ01 : ∀ ε ∈ W₀, ρ₀ ε * ρ₁ ε = 1 := by
    intro ε hε
    simp only [hρ₀, hρ₁]
    rw [← map_mul, S5C25.mroot_mul_mrootInv K hε, map_one]
  set ρ : InfiniteAdeleRing K → (InfiniteAdeleRing K)ˣ := fun ε =>
    if h : ε ∈ W₀ then ⟨ρ₀ ε, ρ₁ ε, hρ01 ε h, by rw [mul_comm]; exact hρ01 ε h⟩ else 1 with hρ
  have hρval : ∀ ε ∈ W₀, ((ρ ε : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) = ρ₀ ε := by
    intro ε hε; simp only [hρ, dif_pos hε]
  have hρinv : ∀ ε ∈ W₀, (((ρ ε)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) = ρ₁ ε := by
    intro ε hε; simp only [hρ, dif_pos hε]; rfl
  have hρ1 : ((ρ 1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) = 1 := by
    rw [hρval 1 h1W₀]
    simp only [hρ₀, map_one, S5C25.mroot_one, map_one]
  have hρpow : ∀ ε ∈ W₀, ((ρ ε : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) ^ Module.finrank K L = ε := by
    intro ε hε
    rw [hρval ε hε]
    simp only [hρ₀]
    rw [← map_pow, S5C25.mroot_pow K hℓ0 hε, RingEquiv.symm_apply_apply]
  have hmaps : Set.MapsTo ι W₀ (S5C25.good K) := fun ε hε => hε
  have hρc : ContinuousOn (fun ε => ((ρ ε : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) W₀ := by
    have h : ContinuousOn ρ₀ W₀ :=
      hιsc.comp_continuousOn (((S5C25.continuousOn_mroot K (Module.finrank K L)).comp hιc.continuousOn hmaps))
    exact h.congr (fun ε hε => hρval ε hε)
  have hρc' : ContinuousOn (fun ε => (((ρ ε)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) W₀ := by
    have h : ContinuousOn ρ₁ W₀ :=
      hιsc.comp_continuousOn (((S5C25.continuousOn_mrootInv K (Module.finrank K L)).comp hιc.continuousOn hmaps))
    exact h.congr (fun ε hε => hρinv ε hε)
  have hρU : ContinuousOn ρ W₀ := by
    rw [Units.isInducing_embedProduct.continuousOn_iff]
    exact hρc.prodMk (MulOpposite.continuous_op.comp_continuousOn hρc')

  set s : InfiniteAdeleRing K → GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) := fun ε =>
    AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (Matrix.GeneralLinearGroup.scalar (Fin 2) (ρ ε)) with hs
  have hsc : ContinuousOn s W₀ := (S5C25.continuous_toTensorGL_scalar K L).comp_continuousOn hρU

  obtain ⟨W, hWn, hWsub, hWc⟩ := local_compact_nhds (hW₀o.mem_nhds h1W₀)
  set C : Set (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :=
    (fun q : InfiniteAdeleRing K × GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) => (s q.1)⁻¹ * q.2) '' (W ×ˢ tsupport φ) with hC
  have hCc : IsCompact C := by
    refine (hWc.prod hφs.isCompact).image_of_continuousOn ?_
    refine ContinuousOn.mul ?_ continuous_snd.continuousOn
    exact ((hsc.mono hWsub).comp continuous_fst.continuousOn (fun q hq => hq.1)).inv
  set Φ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ := C.indicator (fun _ => (1 : ℂ)) with hΦ
  have hΦs : HasCompactSupport Φ :=
    HasCompactSupport.intro hCc (fun x hx => by simp only [hΦ, Set.indicator_of_notMem hx])
  obtain ⟨w, ⟨hw0, hwm, hws, hw1⟩, hwc⟩ :=
    AutomorphicForm.exists_isTwistedSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_normString_of_hasCompactSupport
      K L σ δ hreg τ' Φ hΦs

  set F : InfiniteAdeleRing K → GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ := fun ε x =>
    φ (s ε * (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ x)) * (wt x : ℂ) * (w x : ℂ) with hF
  obtain ⟨M, hM⟩ := hφc.bounded_above_of_compact_support hφs
  have hwt' : ∀ t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ,
      ∀ x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K), wt ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) * x) = wt x :=
    fun t x => hwt t x (hTd t t.2).1 (hTd t t.2).2
  refine ⟨W, hWn, ρ, fun ε => ∫ x, F ε x ∂μ, hρ1, fun ε hε => hρpow ε (hWsub hε), hρc.mono hWsub, ?_, ?_⟩
  ·

    have hconj : Continuous fun x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
        x⁻¹ * δ * AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ x :=
      (continuous_inv.mul continuous_const).mul (S5C25.continuous_sigmaGL K L (InfiniteAdeleRing K) σ)
    refine continuousOn_of_dominated (bound := fun x => M * (|wt x| * w x)) ?_ ?_ ?_ ?_
    · intro ε hε
      refine Continuous.aestronglyMeasurable ?_
      simp only [hF]
      exact ((hφc.comp (continuous_const.mul hconj)).mul
        (Complex.continuous_ofReal.comp hwtc)).mul (Complex.continuous_ofReal.comp hwc)
    · intro ε hε
      refine Filter.Eventually.of_forall fun x => ?_
      simp only [hF]
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (hw0 x), mul_assoc]
      exact mul_le_mul_of_nonneg_right (hM _) (mul_nonneg (abs_nonneg _) (hw0 x))
    · refine Continuous.integrable_of_hasCompactSupport (continuous_const.mul ((continuous_abs.comp hwtc).mul hwc)) ?_
      exact (hws.mul_left).mul_left
    · refine Filter.Eventually.of_forall fun x => ?_
      simp only [hF]
      refine ContinuousOn.mul (ContinuousOn.mul ?_ continuousOn_const) continuousOn_const
      exact hφc.comp_continuousOn (((hsc.mono hWsub).mul continuousOn_const))
  ·

    intro ε hε J hJ
    have hsec : AutomorphicForm.IsTwistedSectionFnOn K L (InfiniteAdeleRing K) σ δ τ'
        (fun y => φ (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) (ρ ε)) * y)) w := by
      refine ⟨hw0, hwm, hws, fun x hx => hw1 x ?_⟩
      have hmem : x⁻¹ * δ * AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ x ∈ C := by
        refine ⟨(ε, s ε * (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ x)), ⟨hε, subset_tsupport φ hx⟩, ?_⟩
        simp only [hs, inv_mul_cancel_left]
      simp only [hΦ, Set.indicator_of_mem hmem]
      exact one_ne_zero
    have hφm : Measurable fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
        φ (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (Matrix.GeneralLinearGroup.scalar (Fin 2) (ρ ε)) * y) :=
      (hφc.comp (continuous_mul_left _)).measurable
    have hφb : ∃ C' : ℝ, ∀ y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
        ‖φ (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (Matrix.GeneralLinearGroup.scalar (Fin 2) (ρ ε)) * y)‖ ≤ C' :=
      ⟨M, fun y => hM _⟩
    exact AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString_of_forall_twistedCentralizer_mul_eq
      K L (InfiniteAdeleRing K) σ hσ μ hμ δ hreg τ' hτ' wt hwtc hwt' _ hφm hφb hJ ⟨w, hsec, rfl⟩

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_nhds_forall_pow_eq_and_continuousOn_and_eq_of_isTwistedWeightedOrbitalIntegralOn_comp_toTensorGL_scalar_mul_infiniteAdeleRing.S5C25"

end S_AutomorphicForm_exists_nhds_forall_pow_eq_and_continuousOn_and_eq_of_isTwistedWeightedOrbitalIntegralOn_comp_toTensorGL_scalar_mul_infiniteAdeleRing
end P2MW
export P2MW.S_AutomorphicForm_exists_nhds_forall_pow_eq_and_continuousOn_and_eq_of_isTwistedWeightedOrbitalIntegralOn_comp_toTensorGL_scalar_mul_infiniteAdeleRing (solution)
