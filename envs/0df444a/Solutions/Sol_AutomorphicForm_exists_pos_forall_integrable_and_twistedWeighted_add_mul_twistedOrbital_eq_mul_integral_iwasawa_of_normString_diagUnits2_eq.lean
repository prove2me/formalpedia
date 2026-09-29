-- Prove2me | solution 1 for AutomorphicForm.exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/0a2e33f4-57c7-5c72-9675-ee39c48a409d

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_AutomorphicForm_exists_pos_forall_integral_semiLocalHaar_eq_mul_integral_integral_setIntegral_iwasawa
import Theorems.Thm_AutomorphicForm_exists_forall_lintegral_semiLocalHaar_eq_mul_lintegral_torus_unipotentGL2_setLIntegral_semiLocalIntegralSet
import Theorems.Thm_AutomorphicForm_semiLocalWeight_diagUnits2_mul_mul_eq_of_mem_semiLocalIntegralSet
import Theorems.Thm_AutomorphicForm_lintegral_norm_inv_mul_torusSection_mul_eq_of_forall_mul_eq
import Theorems.Thm_AutomorphicForm_inv_mul_diagUnits2_mul_sigmaGL_of_diagUnits2_mul_unipotentGL2_mul
import Theorems.Thm_AutomorphicForm_IsTwistedOrbitalIntegralOn_unique_of_isRegularSemisimple_normString
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 320000

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace TensorProduct
open scoped TensorProduct.RightActions

p2m_attr_erase "instance" "LanglandsTunnell.CubicInduction.countable_GL2 LanglandsTunnell.CubicInduction.countable_mirabolicIndex"

noncomputable section

namespace A1TwIwasawa
namespace C3

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
  try simp only [] at e01 e10
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
  try simp only [] at e01 e10
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

theorem isInvInvariant_of_comm [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A]
    (T : Subgroup (GL (Fin 2) A)) (hT : IsClosed (T : Set (GL (Fin 2) A)))
    (hcomm : ∀ s t : T, s * t = t * s) [MeasurableSpace T] [BorelSpace T]
    (τ : Measure T) [τ.IsHaarMeasure] : τ.IsInvInvariant := by
  haveI := t2Space_GL A
  haveI := secondCountableTopology_GL A
  haveI := locallyCompactSpace_GL A
  letI : CommGroup T := { mul_comm := hcomm }
  haveI : LocallyCompactSpace T := hT.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology T :=
    (Topology.IsInducing.subtypeVal : Topology.IsInducing (Subtype.val : T → GL (Fin 2) A)).secondCountableTopology
  haveI : PseudoMetrizableSpace T := PseudoMetrizableSpace.of_regularSpace_secondCountableTopology T
  haveI : SigmaCompactSpace T := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : τ.InnerRegular := inferInstance
  exact Measure.IsHaarMeasure.isInvInvariant_of_innerRegular τ

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

theorem isClosed_twistedCentralizer [T2Space A] (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed ((AutomorphicForm.twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) := by
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  haveI := AutomorphicForm.t2Space_tensorGL K L A
  have hc : Continuous fun t : GL (Fin 2) (L ⊗[K] A) =>
      t * δ * (AutomorphicForm.sigmaGL K L A σ t)⁻¹ :=
    (continuous_id.mul continuous_const).mul (continuous_sigmaGL K L A σ).inv
  have : ((AutomorphicForm.twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) =
      (fun t : GL (Fin 2) (L ⊗[K] A) => t * δ * (AutomorphicForm.sigmaGL K L A σ t)⁻¹) ⁻¹' {δ} := by
    ext t
    exact AutomorphicForm.mem_sigmaCentralizer_iff
  rw [this]
  exact (isClosed_singleton).preimage hc

end TensorTopology

section SemiLocalWeight

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

theorem continuous_semiLocalPlaceComponent (w : v.Extension (𝓞 L)) :
    Continuous (semiLocalPlaceComponent K L v w) := by
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  refine Continuous.units_map _ ?_
  refine continuous_id.matrix_map ?_
  exact (continuous_apply w).comp
    (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v).continuous

theorem continuous_semiLocalWeight : Continuous (semiLocalWeight K L v) := by
  haveI := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
  haveI : Fintype (v.Extension (𝓞 L)) := Fintype.ofFinite _
  have h : semiLocalWeight K L v =
      fun x => ∑ w : v.Extension (𝓞 L), LocalWeight.weight (semiLocalPlaceComponent K L v w x) := by
    funext x
    unfold semiLocalWeight
    exact finsum_eq_sum_of_fintype _
  rw [h]
  exact continuous_finset_sum _ fun w _ => continuous_weight.comp (continuous_semiLocalPlaceComponent K L v w)

theorem semiLocalWeight_diag_mul (d x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (hd : IsDiag d) :
    semiLocalWeight K L v (d * x) = semiLocalWeight K L v x := by
  unfold semiLocalWeight
  congr 1
  funext w
  rw [map_mul]
  refine weight_diag_mul _ _ ⟨?_, ?_⟩
  · change ((Pi.evalRingHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w).comp
        (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v).toAlgEquiv.toRingEquiv.toRingHom)
        (((d : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1) = 0
    rw [hd.1, map_zero]
  · change ((Pi.evalRingHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w).comp
        (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v).toAlgEquiv.toRingEquiv.toRingHom)
        (((d : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0) = 0
    rw [hd.2, map_zero]

end SemiLocalWeight

section LiftFacts

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem sigmaTensor_apply_eq {A : Type} [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L) (x : L ⊗[K] A) :
    sigmaTensor K L A σ x = Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A) x := rfl

theorem lift_facts (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : IsRegularSemisimple γ)
    (hγ₀₁ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0)
    (hγ₁₀ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : normString K L (v.adicCompletion K) σ δ = toTensorGL K L (v.adicCompletion K) γ) :
    IsDiag δ ∧ (∀ t ∈ twistedCentralizer K L (v.adicCompletion K) σ δ, IsDiag t) ∧
      IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ) := by
  obtain ⟨γ', hγ'⟩ : ∃ γ' : GL (Fin 2) (L ⊗[K] v.adicCompletion K), γ' = toTensorGL K L (v.adicCompletion K) γ :=
    ⟨_, rfl⟩
  have hδ' : normString K L (v.adicCompletion K) σ δ = γ' := hδ.trans hγ'.symm
  have hγ'01 : (γ' : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0 := by
    rw [hγ', toTensorGL_apply, hγ₀₁, TensorProduct.tmul_zero]
  have hγ'10 : (γ' : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0 := by
    rw [hγ', toTensorGL_apply, hγ₁₀, TensorProduct.tmul_zero]
  have hγ'u : IsUnit ((γ' : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0 -
      (γ' : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1) := by
    have h := (isUnit_sub_of_isRegularSemisimple γ hγ₀₁ hγ₁₀ hγ).map
      (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K)
    rw [map_sub, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeRight_apply] at h
    rw [hγ', toTensorGL_apply, toTensorGL_apply]
    exact h
  refine ⟨?_, ?_, ?_⟩
  · exact offdiag_eq_zero_of_commute γ' δ hγ'01 hγ'10 hγ'u
      (by rw [hγ']; exact commute_of_normString_eq K L (v.adicCompletion K) σ δ γ hδ)
  · intro t ht
    exact offdiag_eq_zero_of_commute γ' t hγ'01 hγ'10 hγ'u
      (by rw [← hδ']; exact mul_normString_comm K L (v.adicCompletion K) σ δ t ht)
  · rw [hδ']
    show IsUnit _
    have e : Matrix.trace (γ' : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ^ 2 -
        4 * Matrix.det (γ' : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
        ((γ' : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0 -
          (γ' : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1) ^ 2 := by
      rw [Matrix.trace_fin_two, Matrix.det_fin_two, hγ'01, hγ'10]; ring
    rw [e]
    exact hγ'u.pow 2

end LiftFacts

end C3
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa.C3"
end A1TwIwasawa
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa.C3 P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa"

section P2
open MeasureTheory TopologicalSpace Filter Set
open scoped ENNReal NNReal Topology

namespace P2mSectionIntegral

section Setup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  (T : Subgroup G) [MeasurableSpace T] [BorelSpace T]

theorem measurable_subgroup_mul [SecondCountableTopology G] :
    Measurable fun p : G × T => ((p.2 : G) * p.1) := by
  have hc : Continuous fun p : G × T => ((p.2 : G) * p.1) :=
    (continuous_subtype_val.comp continuous_snd).mul continuous_fst
  exact hc.measurable

theorem measurable_comp_subgroup_mul [SecondCountableTopology G] {w : G → ℝ} (hw : Measurable w) :
    Measurable fun p : G × T => w ((p.2 : G) * p.1) :=
  hw.comp (measurable_subgroup_mul T)

theorem measurable_fibre {w : G → ℝ} (hw : Measurable w) (x : G) :
    Measurable fun t : T => w ((t : G) * x) :=
  hw.comp ((continuous_subtype_val.mul continuous_const).measurable)

end Setup
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa.C3 P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa"

section Main

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (T : Subgroup G) [MeasurableSpace T] [BorelSpace T]
  (μ : Measure G) (τ : Measure T)

theorem lintegral_fibre_eq_one {w : G → ℝ} (hw0 : ∀ x, 0 ≤ w x) (hw : Measurable w) {x : G}
    (h : ∫ t : T, w ((t : G) * x) ∂τ = 1) :
    ∫⁻ t : T, ENNReal.ofReal (w ((t : G) * x)) ∂τ = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun t => hw0 _)
    (measurable_fibre T hw x).aestronglyMeasurable] at h
  exact (ENNReal.toReal_eq_one_iff _).1 h

variable [μ.IsHaarMeasure] [τ.IsHaarMeasure] [τ.IsInvInvariant] (hT : IsClosed (T : Set G))
include hT

theorem sigmaCompactSpace_subgroup : SigmaCompactSpace T :=
  hT.isClosedEmbedding_subtypeVal.sigmaCompactSpace

theorem sFinite_tau : SFinite τ := by
  haveI := sigmaCompactSpace_subgroup T hT
  infer_instance

theorem lintegral_enorm_mul_lt_top (F : G → ℂ) (hFm : Measurable F) {C : ℝ} (hFb : ∀ x, ‖F x‖ ≤ C)
    (hFT : ∀ (t : T) (x : G), F ((t : G) * x) = F x)
    (w : G → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hwm : Measurable w) (hwc : HasCompactSupport w)
    (hw1 : ∀ x, F x ≠ 0 → ∫ t : T, w ((t : G) * x) ∂τ = 1) :
    ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) ∂μ < ∞ := by
  haveI := sFinite_tau T τ hT

  obtain ⟨U, hUo, hCU, hUc⟩ := exists_isOpen_superset_and_isCompact_closure hwc.isCompact
  obtain ⟨V₀, hV₀, hV₀U⟩ := compact_open_separated_mul_left hwc.isCompact hUo hCU
  obtain ⟨V, hVV₀, hVo, h1V⟩ := mem_nhds_iff.1 hV₀

  set m : ℝ≥0∞ := min (τ ((Subtype.val : T → G) ⁻¹' V)) 1 with hm
  have hm_pos : m ≠ 0 := by
    have h1 : (τ ((Subtype.val : T → G) ⁻¹' V)) ≠ 0 :=
      ((hVo.preimage continuous_subtype_val).measure_pos τ ⟨⟨1, T.one_mem⟩, h1V⟩).ne'
    simp [hm, h1]
  have hm_top : m ≠ ∞ := by simp [hm]
  have hm_le_one : m ≤ 1 := min_le_right _ _

  let Φ₀ : G → ℝ≥0∞ := fun x => ∫⁻ t : T, U.indicator 1 ((t : G) * x) ∂τ
  have hΦ₀ : ∀ x ∈ tsupport w, m ≤ Φ₀ x := by
    intro x hx
    have hsub : (Subtype.val : T → G) ⁻¹' V ⊆ (fun t : T => (t : G) * x) ⁻¹' U := by
      intro t ht
      exact hV₀U (Set.mul_mem_mul (hVV₀ ht) hx)
    calc m ≤ τ ((Subtype.val : T → G) ⁻¹' V) := min_le_left _ _
      _ ≤ τ ((fun t : T => (t : G) * x) ⁻¹' U) := measure_mono hsub
      _ = Φ₀ x := by
        have hUx : MeasurableSet ((fun t : T => (t : G) * x) ⁻¹' U) :=
          measurableSet_preimage ((continuous_subtype_val.mul continuous_const).measurable)
            hUo.measurableSet
        simp only [Φ₀]
        rw [← lintegral_indicator_one hUx]
        rfl

  have hUind : Measurable (U.indicator (1 : G → ℝ≥0∞)) :=
    (measurable_one.indicator hUo.measurableSet)
  have hint2 : Measurable fun p : G × T =>
      ‖F p.1‖ₑ * ENNReal.ofReal (w p.1) * U.indicator 1 ((p.2 : G) * p.1) :=
    ((hFm.comp measurable_fst).enorm.mul
      (ENNReal.measurable_ofReal.comp (hwm.comp measurable_fst))).mul
      (hUind.comp (measurable_subgroup_mul T))

  have step1 : ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) ∂μ ≤
      m⁻¹ * ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) * Φ₀ x ∂μ := by
    rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hm_pos)]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ tsupport w
    · have h1 : (1 : ℝ≥0∞) ≤ m⁻¹ * Φ₀ x := by
        calc (1 : ℝ≥0∞) = m⁻¹ * m := (ENNReal.inv_mul_cancel hm_pos hm_top).symm
          _ ≤ m⁻¹ * Φ₀ x := mul_le_mul_right (hΦ₀ x hx) _
      calc ‖F x‖ₑ * ENNReal.ofReal (w x) = ‖F x‖ₑ * ENNReal.ofReal (w x) * 1 := (mul_one _).symm
        _ ≤ ‖F x‖ₑ * ENNReal.ofReal (w x) * (m⁻¹ * Φ₀ x) := mul_le_mul_right h1 _
        _ = m⁻¹ * (‖F x‖ₑ * ENNReal.ofReal (w x) * Φ₀ x) := by ring
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp

  have step2 : ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) * Φ₀ x ∂μ =
      ∫⁻ x, ‖F x‖ₑ * U.indicator 1 x * ∫⁻ t : T, ENNReal.ofReal (w ((t : G) * x)) ∂τ ∂μ := by
    calc ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) * Φ₀ x ∂μ
        = ∫⁻ x, ∫⁻ t : T, ‖F x‖ₑ * ENNReal.ofReal (w x) * U.indicator 1 ((t : G) * x) ∂τ ∂μ := by
          refine lintegral_congr fun x => ?_
          rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top enorm_ne_top ENNReal.ofReal_ne_top)]
      _ = ∫⁻ t : T, ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) * U.indicator 1 ((t : G) * x) ∂μ ∂τ :=
          lintegral_lintegral_swap hint2.aemeasurable
      _ = ∫⁻ t : T, ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w ((t : G)⁻¹ * x)) * U.indicator 1 x ∂μ ∂τ := by
          refine lintegral_congr fun t => ?_
          have := lintegral_mul_left_eq_self (μ := μ)
            (fun x => ‖F ((t : G)⁻¹ * x)‖ₑ * ENNReal.ofReal (w ((t : G)⁻¹ * x)) * U.indicator 1 x) (t : G)
          simp only [inv_mul_cancel_left] at this
          rw [this]
          refine lintegral_congr fun x => ?_
          have hF : F ((t : G)⁻¹ * x) = F x := by
            have := hFT t⁻¹ x
            simpa using this
          rw [hF]
      _ = ∫⁻ t : T, ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w ((t : G) * x)) * U.indicator 1 x ∂μ ∂τ := by
          rw [← lintegral_inv_eq_self]
          simp
      _ = ∫⁻ x, ∫⁻ t : T, ‖F x‖ₑ * ENNReal.ofReal (w ((t : G) * x)) * U.indicator 1 x ∂τ ∂μ := by
          refine (lintegral_lintegral_swap ?_).symm
          exact (((hFm.comp measurable_fst).enorm.mul
            (ENNReal.measurable_ofReal.comp (hwm.comp (measurable_subgroup_mul T)))).mul
            (hUind.comp measurable_fst)).aemeasurable
      _ = ∫⁻ x, ‖F x‖ₑ * U.indicator 1 x * ∫⁻ t : T, ENNReal.ofReal (w ((t : G) * x)) ∂τ ∂μ := by
          refine lintegral_congr fun x => ?_
          rw [← lintegral_const_mul' _ _
            (ENNReal.mul_ne_top enorm_ne_top (by by_cases hxU : x ∈ U <;> simp [hxU]))]
          refine lintegral_congr fun t => ?_
          ring

  have step3 : ∫⁻ x, ‖F x‖ₑ * U.indicator 1 x * ∫⁻ t : T, ENNReal.ofReal (w ((t : G) * x)) ∂τ ∂μ ≤
      ∫⁻ x, U.indicator (fun _ => (‖C‖₊ : ℝ≥0∞)) x ∂μ := by
    refine lintegral_mono fun x => ?_
    by_cases hF : F x = 0
    · simp [hF]
    · rw [lintegral_fibre_eq_one T τ hw0 hwm (hw1 x hF), mul_one]
      by_cases hxU : x ∈ U
      · rw [Set.indicator_of_mem hxU, Set.indicator_of_mem hxU, Pi.one_apply, mul_one]
        have h : ‖F x‖₊ ≤ ‖C‖₊ := by
          rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
          exact (hFb x).trans (Real.le_norm_self C)
        exact enorm_le_coe.2 h
      · simp [hxU]
  have step4 : ∫⁻ x, U.indicator (fun _ => (‖C‖₊ : ℝ≥0∞)) x ∂μ < ∞ := by
    rw [lintegral_indicator_const hUo.measurableSet]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top
      ((measure_mono subset_closure).trans_lt hUc.measure_lt_top)
  calc ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) ∂μ
      ≤ m⁻¹ * ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) * Φ₀ x ∂μ := step1
    _ ≤ m⁻¹ * ∫⁻ x, U.indicator (fun _ => (‖C‖₊ : ℝ≥0∞)) x ∂μ := by
        rw [step2]; exact mul_le_mul_right step3 _
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hm_pos)) step4

end Main
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa.C3 P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa"

end P2mSectionIntegral
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa.C3 P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa"
end P2
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa.C3 P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa"

section P3
open NumberField IsDedekindDomain MeasureTheory Set Function
open scoped ENNReal NNReal TensorProduct TensorProduct.RightActions Pointwise

namespace KcSemiLocalIwasawaHaar

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => v.adicCompletion K
local notation "E" => L ⊗[K] v.adicCompletion K
local notation "Q" => (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K)
local notation "G" => GL (Fin 2) (L ⊗[K] v.adicCompletion K)

attribute [local instance 9999] Algebra.toModule

theorem isTopologicalRing_E : IsTopologicalRing E := AutomorphicForm.isTopologicalRing_tensor K L F
theorem t2Space_E : T2Space E := AutomorphicForm.t2Space_tensor K L F
theorem locallyCompactSpace_E : LocallyCompactSpace E := AutomorphicForm.locallyCompactSpace_tensor K L F
theorem continuousSMul_E : ContinuousSMul F E := IsModuleTopology.toContinuousSMul F E
theorem isScalarTower_FEE : IsScalarTower F E E :=
  @IsScalarTower.right F E _ _ (TensorProduct.RightActions.instAlgebra_definitions K (v.adicCompletion K) L)
theorem smulCommClass_FEE : SMulCommClass F E E :=
  @Algebra.to_smulCommClass F E _ _ (TensorProduct.RightActions.instAlgebra_definitions K (v.adicCompletion K) L)
theorem finite_KL : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L

attribute [local instance] isTopologicalRing_E t2Space_E locallyCompactSpace_E continuousSMul_E
  isScalarTower_FEE smulCommClass_FEE finite_KL

def triv : E ≃L[F] (Fin (Module.finrank F E) → F) :=
  let e : E ≃ₗ[F] (Fin (Module.finrank F E) → F) := (Module.finBasis F E).equivFun
  { e with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }

theorem secondCountableTopology_E : SecondCountableTopology E :=
  (triv (K := K) (L := L) (v := v)).toHomeomorph.secondCountableTopology

attribute [local instance] secondCountableTopology_E

theorem continuous_algebraNorm : Continuous (Algebra.norm F : E → F) := by
  classical
  let b := Module.finBasis F E
  have h1 : Continuous fun x : E => Algebra.leftMulMatrix b x :=
    IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap
  have h2 : (Algebra.norm F : E → F) = fun x => (Algebra.leftMulMatrix b x).det := by
    funext x; exact Algebra.norm_eq_matrix_det b x
  rw [h2]
  exact h1.matrix_det

theorem isUnit_iff_norm_ne_zero (x : E) : IsUnit x ↔ Algebra.norm F x ≠ 0 := by
  constructor
  · intro hx h0
    obtain ⟨u, rfl⟩ := hx
    have h1 : Algebra.norm F ((u : E)) * Algebra.norm F ((u⁻¹ : Eˣ) : E) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  · intro h
    have hdet : LinearMap.det (Algebra.lmul F E x) ≠ 0 := by
      rwa [← Algebra.norm_apply]
    have hbij : Function.Bijective (Algebra.lmul F E x) := by
      have hu : IsUnit (Algebra.lmul F E x) :=
        (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
      exact (Module.End.isUnit_iff _).1 hu
    obtain ⟨y, hy⟩ := hbij.2 1
    have hy' : x * y = 1 := by
      rw [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply'] at hy; exact hy
    exact IsUnit.of_mul_eq_one y hy'

theorem isClosed_nonunits : IsClosed {x : E | ¬ IsUnit x} := by
  have : {x : E | ¬ IsUnit x} = (Algebra.norm F : E → F) ⁻¹' {0} := by
    ext x
    simp only [mem_setOf_eq, mem_preimage, mem_singleton_iff, isUnit_iff_norm_ne_zero, not_not]
  rw [this]
  exact isClosed_singleton.preimage continuous_algebraNorm

theorem isOpen_units : IsOpen {x : E | IsUnit x} := by
  have : {x : E | IsUnit x} = {x : E | ¬ IsUnit x}ᶜ := by ext; simp
  rw [this]; exact isClosed_nonunits.isOpen_compl

section Inverse

open scoped Classical in

def adjLin : Matrix (Fin (Module.finrank F E)) (Fin (Module.finrank F E)) F →ₗ[F] E :=
  (LinearMap.applyₗ (1 : E)) ∘ₗ
    (Matrix.toLin (Module.finBasis F E) (Module.finBasis F E)).toLinearMap

open scoped Classical in

def adjE (y : E) : E := adjLin (K := K) (L := L) (v := v) (Algebra.leftMulMatrix (Module.finBasis F E) y).adjugate

theorem adjE_eq (y : E) :
    adjE y = Matrix.toLin (Module.finBasis F E) (Module.finBasis F E)
      (Algebra.leftMulMatrix (Module.finBasis F E) y).adjugate 1 := rfl

theorem mul_adjE (y : E) : y * adjE y = algebraMap F E (Algebra.norm F y) := by
  classical
  set b := Module.finBasis F E with hb
  have h1 : Matrix.toLin b b (Algebra.leftMulMatrix b y) = Algebra.lmul F E y := by
    rw [Algebra.leftMulMatrix_apply, Matrix.toLin_toMatrix]
  have h2 : Matrix.toLin b b (Algebra.leftMulMatrix b y * (Algebra.leftMulMatrix b y).adjugate) =
      (Algebra.lmul F E y) ∘ₗ Matrix.toLin b b (Algebra.leftMulMatrix b y).adjugate := by
    rw [Matrix.toLin_mul b b b, h1]
  have h3 : y * adjE y = Matrix.toLin b b
      (Algebra.leftMulMatrix b y * (Algebra.leftMulMatrix b y).adjugate) 1 := by
    rw [h2, LinearMap.comp_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', adjE_eq]
  rw [h3, Matrix.mul_adjugate, map_smul, Matrix.toLin_one, LinearMap.smul_apply, LinearMap.id_apply,
    Algebra.norm_eq_matrix_det b, Algebra.algebraMap_eq_smul_one]

theorem continuous_adjE : Continuous (adjE : E → E) := by
  classical
  have h1 : Continuous fun y : E => Algebra.leftMulMatrix (Module.finBasis F E) y :=
    IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix (Module.finBasis F E)).toLinearMap
  haveI : IsModuleTopology F (Matrix (Fin (Module.finrank F E)) (Fin (Module.finrank F E)) F) :=
    inferInstanceAs (IsModuleTopology F (Fin (Module.finrank F E) → Fin (Module.finrank F E) → F))
  have h2 : Continuous (adjLin (K := K) (L := L) (v := v)) := IsModuleTopology.continuous_of_linearMap _
  exact h2.comp h1.matrix_adjugate

theorem ringInverse_eq {y : E} (hy : IsUnit y) :
    Ring.inverse y = (Algebra.norm F y)⁻¹ • adjE y := by
  have hN : Algebra.norm F y ≠ 0 := (isUnit_iff_norm_ne_zero y).1 hy
  have hmul := mul_adjE (K := K) (L := L) (v := v) y
  have h1 : Ring.inverse y * (y * adjE y) = adjE y := by
    rw [← mul_assoc, Ring.inverse_mul_cancel _ hy, one_mul]
  rw [hmul, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one] at h1
  rw [← h1, smul_smul, inv_mul_cancel₀ hN, one_smul]

theorem continuous_ringInverse_comp {X : Type*} [TopologicalSpace X] {f : X → E}
    (hf : Continuous f) (hu : ∀ x, IsUnit (f x)) :
    Continuous fun x => Ring.inverse (f x) := by
  have : (fun x => Ring.inverse (f x)) = fun x => (Algebra.norm F (f x))⁻¹ • adjE (f x) := by
    funext x; exact ringInverse_eq (hu x)
  rw [this]
  refine Continuous.fun_smul ?_ (continuous_adjE.comp hf)
  refine Continuous.inv₀ (continuous_algebraNorm.comp hf) fun x => ?_
  exact (isUnit_iff_norm_ne_zero _).1 (hu x)

end Inverse
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa.C3 P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa"

theorem t2Space_GL : T2Space G := AutomorphicForm.t2Space_tensorGL K L F

theorem secondCountableTopology_GL : SecondCountableTopology G := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) E) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → E))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) E)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem locallyCompactSpace_GL : LocallyCompactSpace G := AutomorphicForm.locallyCompactSpace_tensorGL K L F

theorem isTopologicalGroup_GL : IsTopologicalGroup G := AutomorphicForm.isTopologicalGroup_tensorGL K L F

@[reducible] def measurableSpace_GL : MeasurableSpace G := AutomorphicForm.glBorelOf E

attribute [local instance] t2Space_GL secondCountableTopology_GL locallyCompactSpace_GL
  isTopologicalGroup_GL measurableSpace_GL

theorem borelSpace_GL : BorelSpace G := AutomorphicForm.borelSpace_glBorelOf E

private theorem _root_.KcSemiLocalIwasawaHaar.isHaarMeasure_semiLocalHaar : (AutomorphicForm.semiLocalHaar K L v).IsHaarMeasure :=
  AutomorphicForm.isHaarMeasure_semiLocalHaar K L v

p2m_export "KcSemiLocalIwasawaHaar" "isHaarMeasure_semiLocalHaar"
attribute [local instance] borelSpace_GL isHaarMeasure_semiLocalHaar

theorem measurableMul_GL : MeasurableMul₂ G := inferInstance
theorem measurableInv_GL : MeasurableInv G := inferInstance

attribute [local instance] measurableMul_GL measurableInv_GL

theorem continuous_GL_of {X : Type*} [TopologicalSpace X] {f : X → G}
    (hval : ∀ i j, Continuous fun x => ((f x : G) : Matrix (Fin 2) (Fin 2) E) i j)
    (hinv : ∀ i j, Continuous fun x => (((f x)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) i j) :
    Continuous f := by
  rw [Units.continuous_iff]
  exact ⟨continuous_matrix fun i j => hval i j, continuous_matrix fun i j => hinv i j⟩

local notation "μG" => AutomorphicForm.semiLocalHaar K L v
local notation "𝒦" => AutomorphicForm.semiLocalIntegralSet K L v
local notation "𝒪" => AutomorphicForm.semiLocalIntegers K L v

section Charts

open scoped Classical

def tm (p : Q) : Matrix (Fin 2) (Fin 2) E := !![p.1, 0; 0, p.2]

theorem det_tm (p : Q) : (tm p).det = p.1 * p.2 := by
  simp [tm, Matrix.det_fin_two_of]

theorem continuous_tm : Continuous (tm : Q → Matrix (Fin 2) (Fin 2) E) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact continuous_fst
  · exact continuous_const
  · exact continuous_const
  · exact continuous_snd

theorem continuous_det_tm : Continuous fun p : Q => (tm p).det := continuous_tm.matrix_det

def goodT : Set Q := {p | IsUnit (tm p).det}

theorem mem_goodT_iff (p : Q) : p ∈ goodT ↔ IsUnit p.1 ∧ IsUnit p.2 := by
  simp only [goodT, mem_setOf_eq, det_tm, IsUnit.mul_iff]

theorem isOpen_goodT : IsOpen (goodT : Set Q) :=
  (isOpen_units (K := K) (L := L) (v := v)).preimage continuous_det_tm

theorem one_mem_goodT : ((1, 1) : Q) ∈ goodT := by
  rw [mem_goodT_iff]; exact ⟨isUnit_one, isUnit_one⟩

def uGL (p : Q) : G := if h : IsUnit (tm p).det then Matrix.GeneralLinearGroup.mk'' (tm p) h else 1

theorem uGL_of_mem {p : Q} (h : IsUnit (tm p).det) : uGL p = Matrix.GeneralLinearGroup.mk'' (tm p) h := by
  simp [uGL, h]

theorem coe_uGL_of_mem {p : Q} (h : IsUnit (tm p).det) : ((uGL p : G) : Matrix (Fin 2) (Fin 2) E) = tm p := by
  rw [uGL_of_mem h]; rfl

theorem uGL_of_not {p : Q} (h : ¬ IsUnit (tm p).det) : uGL p = 1 := by
  simp [uGL, h]

theorem coe_uGL_inv_of_mem {p : Q} (h : IsUnit (tm p).det) :
    (((uGL p)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) = Ring.inverse (tm p).det • (tm p).adjugate := by
  rw [Matrix.coe_units_inv, coe_uGL_of_mem h, Matrix.inv_def]

theorem continuous_uGL_restrict : Continuous ((goodT : Set Q).domRestrict (uGL : Q → G)) := by
  have hent : ∀ i j, Continuous fun x : (goodT : Set Q) => tm (x : Q) i j := fun i j =>
    (continuous_tm.matrix_elem i j).comp continuous_subtype_val
  refine continuous_GL_of (fun i j => ?_) (fun i j => ?_)
  · have : (fun x : (goodT : Set Q) => (((goodT : Set Q).domRestrict uGL x : G) : Matrix (Fin 2) (Fin 2) E) i j)
        = fun x : (goodT : Set Q) => tm (x : Q) i j := by
      funext x; rw [Set.domRestrict_apply, coe_uGL_of_mem x.2]
    rw [this]; exact hent i j
  · have : (fun x : (goodT : Set Q) =>
        ((((goodT : Set Q).domRestrict uGL x)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) i j)
        = fun x : (goodT : Set Q) => Ring.inverse (tm (x : Q)).det * (tm (x : Q)).adjugate i j := by
      funext x
      rw [Set.domRestrict_apply, coe_uGL_inv_of_mem x.2, Matrix.smul_apply, smul_eq_mul]
    rw [this]
    have hdet : Continuous fun x : (goodT : Set Q) => (tm (x : Q)).det :=
      continuous_det_tm.comp continuous_subtype_val
    have hri : Continuous fun x : (goodT : Set Q) => Ring.inverse (tm (x : Q)).det :=
      continuous_ringInverse_comp hdet fun x => x.2
    refine hri.mul ?_
    have hadj : Continuous fun x : (goodT : Set Q) => (tm (x : Q)).adjugate :=
      (continuous_tm.comp continuous_subtype_val).matrix_adjugate
    exact hadj.matrix_elem i j

theorem uGL_mul_uGL {a q : Q} (ha : a ∈ goodT) (hq : q ∈ goodT) :
    uGL a * uGL q = uGL (a.1 * q.1, a.2 * q.2) := by
  have haq : ((a.1 * q.1, a.2 * q.2) : Q) ∈ goodT := by
    rw [mem_goodT_iff] at ha hq ⊢
    exact ⟨ha.1.mul hq.1, ha.2.mul hq.2⟩
  apply Units.ext
  rw [Units.val_mul, coe_uGL_of_mem (show IsUnit (tm a).det from ha),
    coe_uGL_of_mem (show IsUnit (tm q).det from hq),
    coe_uGL_of_mem (show IsUnit (tm ((a.1 * q.1, a.2 * q.2) : Q)).det from haq)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tm, Matrix.mul_apply, Fin.sum_univ_two]

def nGL (x : E) : G := AutomorphicForm.unipotentGL2 x

theorem coe_nGL (x : E) : ((nGL x : G) : Matrix (Fin 2) (Fin 2) E) = !![1, x; 0, 1] := rfl

theorem nGL_add (x y : E) : nGL (x + y) = nGL x * nGL y := AutomorphicForm.unipotentGL2_add x y

theorem nGL_zero : nGL (0 : E) = 1 := AutomorphicForm.unipotentGL2_zero

theorem nGL_neg (x : E) : nGL (-x) = (nGL x)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← nGL_add, neg_add_cancel, nGL_zero]

theorem coe_nGL_inv (x : E) : (((nGL x)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) = !![1, -x; 0, 1] := by
  rw [← nGL_neg]; rfl

theorem continuous_nGL : Continuous (nGL : E → G) := by
  refine continuous_GL_of (fun i j => ?_) (fun i j => ?_)
  · simp only [coe_nGL]
    fin_cases i <;> fin_cases j
    · exact continuous_const
    · exact continuous_id
    · exact continuous_const
    · exact continuous_const
  · simp only [coe_nGL_inv]
    fin_cases i <;> fin_cases j
    · exact continuous_const
    · exact continuous_neg
    · exact continuous_const
    · exact continuous_const

theorem nGL_mul_uGL {q : Q} (hq : q ∈ goodT) (c : E) :
    nGL c * uGL q = uGL q * nGL (Ring.inverse q.1 * c * q.2) := by
  have h1 : IsUnit q.1 := ((mem_goodT_iff q).1 hq).1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_uGL_of_mem (show IsUnit (tm q).det from hq), coe_nGL, coe_nGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tm, Matrix.mul_apply, Fin.sum_univ_two]
  rw [← mul_assoc, ← mul_assoc, Ring.mul_inverse_cancel _ h1, one_mul]

def ι (z : Q × E) : G := uGL z.1 * nGL z.2

theorem ι_apply (p : Q) (x : E) : ι (p, x) = uGL p * nGL x := rfl

theorem coe_ι_of_mem {p : Q} (hp : p ∈ goodT) (x : E) :
    ((ι (p, x) : G) : Matrix (Fin 2) (Fin 2) E) = !![p.1, p.1 * x; 0, p.2] := by
  rw [ι_apply, Units.val_mul, coe_uGL_of_mem (show IsUnit (tm p).det from hp), coe_nGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tm, Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_ι_inv_of_mem {p : Q} (hp : p ∈ goodT) (x : E) :
    (((ι (p, x))⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) =
      !![Ring.inverse p.1, -x * Ring.inverse p.2; 0, Ring.inverse p.2] := by
  have h1 : IsUnit p.1 := ((mem_goodT_iff p).1 hp).1
  have h2 : IsUnit p.2 := ((mem_goodT_iff p).1 hp).2

  have hmul : ((ι (p, x) : G) : Matrix (Fin 2) (Fin 2) E) *
      !![Ring.inverse p.1, -x * Ring.inverse p.2; 0, Ring.inverse p.2] = 1 := by
    rw [coe_ι_of_mem hp]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Ring.mul_inverse_cancel _ h1, Ring.mul_inverse_cancel _ h2]
    ring_nf
  have hinv : (((ι (p, x))⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) * ((ι (p, x) : G) : Matrix (Fin 2) (Fin 2) E) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc (((ι (p, x))⁻¹ : G) : Matrix (Fin 2) (Fin 2) E)
      = (((ι (p, x))⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) *
          (((ι (p, x) : G) : Matrix (Fin 2) (Fin 2) E) *
            !![Ring.inverse p.1, -x * Ring.inverse p.2; 0, Ring.inverse p.2]) := by rw [hmul, mul_one]
    _ = !![Ring.inverse p.1, -x * Ring.inverse p.2; 0, Ring.inverse p.2] := by
          rw [← mul_assoc, hinv, one_mul]

section Meas

variable [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]

theorem borelSpace_Q : BorelSpace Q := inferInstance

theorem measurableSet_goodT : MeasurableSet (goodT : Set Q) := isOpen_goodT.measurableSet

theorem measurable_uGL : Measurable (uGL : Q → G) := by
  refine measurable_of_restrict_of_restrict_compl measurableSet_goodT ?_ ?_
  · exact continuous_uGL_restrict.measurable
  · have : (goodTᶜ : Set Q).domRestrict (uGL : Q → G) = fun _ => 1 := by
      funext x
      have hx : ¬ IsUnit (tm (x : Q)).det := x.2
      simp [Set.domRestrict_apply, uGL, hx]
    rw [this]; exact measurable_const

theorem measurable_nGL : Measurable (nGL : E → G) := continuous_nGL.measurable

theorem measurable_ι : Measurable (ι : Q × E → G) :=
  (measurable_uGL.comp measurable_fst).mul (measurable_nGL.comp measurable_snd)

end Meas
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa.C3 P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa"

end Charts
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa.C3 P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa"

section Kgroup

theorem intg_zero_mem : (0 : E) ∈ 𝒪 := AutomorphicForm.zero_mem_semiLocalIntegers K L v
theorem intg_one_mem : (1 : E) ∈ 𝒪 := AutomorphicForm.one_mem_semiLocalIntegers K L v

theorem intg_add_mem {a b : E} (ha : a ∈ 𝒪) (hb : b ∈ 𝒪) : a + b ∈ 𝒪 := by
  obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb; exact ⟨x + y, map_add _ _ _⟩

theorem intg_mul_mem {a b : E} (ha : a ∈ 𝒪) (hb : b ∈ 𝒪) : a * b ∈ 𝒪 := by
  obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb; exact ⟨x * y, map_mul _ _ _⟩

theorem intg_neg_mem {a : E} (ha : a ∈ 𝒪) : -a ∈ 𝒪 := by
  obtain ⟨x, rfl⟩ := ha; exact ⟨-x, map_neg _ _⟩

theorem isCompact_intg : IsCompact (𝒪 : Set E) := AutomorphicForm.isCompact_semiLocalIntegers K L v
theorem isOpen_intg : IsOpen (𝒪 : Set E) := AutomorphicForm.isOpen_semiLocalIntegers K L v

theorem mem_K_iff (g : G) : g ∈ 𝒦 ↔ (∀ i j, (g : Matrix (Fin 2) (Fin 2) E) i j ∈ 𝒪) ∧
    ∀ i j, ((g⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) i j ∈ 𝒪 := Iff.rfl

theorem matrix_mul_mem {A B : Matrix (Fin 2) (Fin 2) E} (hA : ∀ i j, A i j ∈ 𝒪) (hB : ∀ i j, B i j ∈ 𝒪)
    (i j : Fin 2) : (A * B) i j ∈ 𝒪 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact intg_add_mem (intg_mul_mem (hA _ _) (hB _ _)) (intg_mul_mem (hA _ _) (hB _ _))

theorem K_mul_mem {g h : G} (hg : g ∈ 𝒦) (hh : h ∈ 𝒦) : g * h ∈ 𝒦 := by
  rw [mem_K_iff] at hg hh ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul]; exact matrix_mul_mem hg.1 hh.1 i j
  · rw [mul_inv_rev, Units.val_mul]; exact matrix_mul_mem hh.2 hg.2 i j

theorem K_inv_mem {g : G} (hg : g ∈ 𝒦) : g⁻¹ ∈ 𝒦 := by
  rw [mem_K_iff] at hg ⊢
  refine ⟨hg.2, fun i j => ?_⟩
  rw [inv_inv]; exact hg.1 i j

theorem K_one_mem : (1 : G) ∈ 𝒦 := AutomorphicForm.one_mem_semiLocalIntegralSet K L v

def Kgrp : Subgroup G where
  carrier := 𝒦
  mul_mem' := K_mul_mem
  one_mem' := K_one_mem
  inv_mem' := K_inv_mem

theorem mem_Kgrp {g : G} : g ∈ (Kgrp : Subgroup G) ↔ g ∈ 𝒦 := Iff.rfl

theorem K_mul_mem_iff_right {g k : G} (hk : k ∈ 𝒦) : g * k ∈ 𝒦 ↔ g ∈ 𝒦 :=
  (Kgrp (K := K) (L := L) (v := v)).mul_mem_cancel_right (mem_Kgrp.2 hk)

theorem K_mul_mem_iff_left {g k : G} (hk : k ∈ 𝒦) : k * g ∈ 𝒦 ↔ g ∈ 𝒦 :=
  (Kgrp (K := K) (L := L) (v := v)).mul_mem_cancel_left (mem_Kgrp.2 hk)

theorem K_inv_mem_iff {g : G} : g⁻¹ ∈ 𝒦 ↔ g ∈ 𝒦 := (Kgrp (K := K) (L := L) (v := v)).inv_mem_iff

theorem isOpen_K : IsOpen (𝒦 : Set G) := AutomorphicForm.isOpen_semiLocalIntegralSet K L v
theorem isCompact_K : IsCompact (𝒦 : Set G) := AutomorphicForm.isCompact_semiLocalIntegralSet K L v

variable [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]

theorem measurableSet_K : MeasurableSet (𝒦 : Set G) := isOpen_K.measurableSet

theorem muK : μG 𝒦 = 1 := AutomorphicForm.semiLocalHaar_semiLocalIntegralSet K L v

theorem isLocallyFiniteMeasure_μ : IsLocallyFiniteMeasure μG := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
theorem sigmaFinite_μ : SigmaFinite μG := by
  haveI := isLocallyFiniteMeasure_μ (K := K) (L := L) (v := v)
  exact MeasureTheory.sigmaFinite_of_locallyFinite
theorem sFinite_μ : SFinite μG := by haveI := sigmaFinite_μ (K := K) (L := L) (v := v); infer_instance

attribute [local instance] sigmaFinite_μ sFinite_μ

theorem map_mul_right_K {k : G} (hk : k ∈ 𝒦) : Measure.map (fun g : G => g * k) μG = μG := by
  have h := Measure.isMulLeftInvariant_eq_smul (Measure.map (fun g : G => g * k) μG) μG
  set c := Measure.haarScalarFactor (Measure.map (fun g : G => g * k) μG) μG with hc
  have hpre : (fun g : G => g * k) ⁻¹' (𝒦 : Set G) = 𝒦 := by
    ext g; exact K_mul_mem_iff_right hk
  have h1 : (Measure.map (fun g : G => g * k) μG) 𝒦 = (c : ℝ≥0∞) * μG 𝒦 := by
    conv_lhs => rw [h]
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [Measure.map_apply (measurable_mul_const k) measurableSet_K, hpre, muK, mul_one] at h1
  have hc1 : c = 1 := ENNReal.coe_eq_one.1 h1.symm
  rw [h, hc1, one_smul]

theorem lintegral_mul_right_K (f : G → ℝ≥0∞) (hf : Measurable f) {k : G} (hk : k ∈ 𝒦) :
    ∫⁻ g, f (g * k) ∂μG = ∫⁻ g, f g ∂μG := by
  rw [← lintegral_map hf (measurable_mul_const k), map_mul_right_K hk]

end Kgroup
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa.C3 P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa"

section A1extra

theorem uGL_eq_diagUnits2 {a : Q} (ha : a ∈ goodT) :
    uGL a = LanglandsTunnell.CubicInduction.diagUnits2 ((mem_goodT_iff a).1 ha).1.unit ((mem_goodT_iff a).1 ha).2.unit := by
  apply Units.ext
  rw [coe_uGL_of_mem ha, LanglandsTunnell.CubicInduction.coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tm, IsUnit.unit_spec]

end A1extra
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa.C3 P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa"

end KcSemiLocalIwasawaHaar
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa.C3 P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa"
end P3
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa.C3 P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa.C3 P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa"

section P4
open MeasureTheory
open scoped ENNReal

namespace A1MT

variable {X : Type*} [MeasurableSpace X] (m : Measure X)

theorem enorm_real_of_nonneg {w : ℝ} (hw : 0 ≤ w) : ‖(w : ℂ)‖ₑ = ENNReal.ofReal w := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hw]

theorem ofReal_mul_nonneg (a : ℝ) {b : ℝ} (hb : 0 ≤ b) :
    ENNReal.ofReal (a * b) = ENNReal.ofReal a * ENNReal.ofReal b := by
  rcases le_or_gt 0 a with ha | ha
  · exact ENNReal.ofReal_mul ha
  · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg ha.le hb),
      ENNReal.ofReal_of_nonpos ha.le, zero_mul]

theorem integrable_mul_real {θ : X → ℂ} {w : X → ℝ} (hθ : Measurable θ) (hw : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) (hf : ∫⁻ x, ‖θ x‖ₑ * ENNReal.ofReal (w x) ∂m < ∞) :
    Integrable (fun x => θ x * (w x : ℂ)) m := by
  refine ⟨(hθ.mul (Complex.measurable_ofReal.comp hw)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc ∫⁻ x, ‖θ x * (w x : ℂ)‖ₑ ∂m = ∫⁻ x, ‖θ x‖ₑ * ENNReal.ofReal (w x) ∂m := by
        refine lintegral_congr fun x => ?_
        rw [enorm_mul, enorm_real_of_nonneg (hw0 x)]
    _ < ∞ := hf

theorem integral_mul_eq_integral_mul_of_forall_lintegral_eq
    (θ : X → ℂ) (w₁ w₂ : X → ℝ) (hθ : Measurable θ) (hw₁ : Measurable w₁) (hw₂ : Measurable w₂)
    (hw₁0 : ∀ x, 0 ≤ w₁ x) (hw₂0 : ∀ x, 0 ≤ w₂ x)
    (hswap : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ → ψ 0 = 0 →
      ∫⁻ x, ψ (θ x) * ENNReal.ofReal (w₁ x) ∂m = ∫⁻ x, ψ (θ x) * ENNReal.ofReal (w₂ x) ∂m)
    (hfin : ∫⁻ x, ‖θ x‖ₑ * ENNReal.ofReal (w₁ x) ∂m < ∞) :
    Integrable (fun x => θ x * (w₁ x : ℂ)) m ∧ Integrable (fun x => θ x * (w₂ x : ℂ)) m ∧
      ∫ x, θ x * (w₁ x : ℂ) ∂m = ∫ x, θ x * (w₂ x : ℂ) ∂m := by
  have hfin₂ : ∫⁻ x, ‖θ x‖ₑ * ENNReal.ofReal (w₂ x) ∂m < ∞ := by
    have h := hswap (fun z => ‖z‖ₑ) measurable_enorm enorm_zero
    beta_reduce at h
    rw [← h]; exact hfin
  have h₁ := integrable_mul_real m hθ hw₁ hw₁0 hfin
  have h₂ := integrable_mul_real m hθ hw₂ hw₂0 hfin₂
  refine ⟨h₁, h₂, ?_⟩
  have key : ∀ ℓ : ℂ →L[ℝ] ℝ, ∫ x, ℓ (θ x * (w₁ x : ℂ)) ∂m = ∫ x, ℓ (θ x * (w₂ x : ℂ)) ∂m := by
    intro ℓ
    have hℓ : ∀ (w : X → ℝ) (x : X), ℓ (θ x * (w x : ℂ)) = ℓ (θ x) * w x := by
      intro w x
      rw [mul_comm (θ x), ← Complex.real_smul, ℓ.map_smul, smul_eq_mul, mul_comm]
    have hgi : ∀ (w : X → ℝ), Integrable (fun x => θ x * (w x : ℂ)) m →
        Integrable (fun x => ℓ (θ x) * w x) m := by
      intro w hw
      have h := ℓ.integrable_comp hw
      have e : (fun x => ℓ (θ x * (w x : ℂ))) = fun x => ℓ (θ x) * w x := funext (hℓ w)
      rw [e] at h; exact h
    have e₁ : (fun x => ℓ (θ x * (w₁ x : ℂ))) = fun x => ℓ (θ x) * w₁ x := funext (hℓ w₁)
    have e₂ : (fun x => ℓ (θ x * (w₂ x : ℂ))) = fun x => ℓ (θ x) * w₂ x := funext (hℓ w₂)
    rw [e₁, e₂, integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hgi w₁ h₁),
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hgi w₂ h₂)]
    have hm1 : Measurable fun z : ℂ => ENNReal.ofReal (ℓ z) :=
      ENNReal.measurable_ofReal.comp ℓ.continuous.measurable
    have hm2 : Measurable fun z : ℂ => ENNReal.ofReal (-ℓ z) :=
      ENNReal.measurable_ofReal.comp ℓ.continuous.neg.measurable
    have s1 := hswap (fun z => ENNReal.ofReal (ℓ z)) hm1 (by simp)
    have s2 := hswap (fun z => ENNReal.ofReal (-ℓ z)) hm2 (by simp)
    beta_reduce at s1 s2
    have p1 : ∀ (w : X → ℝ), (∀ x, 0 ≤ w x) →
        ∫⁻ x, ENNReal.ofReal (ℓ (θ x) * w x) ∂m = ∫⁻ x, ENNReal.ofReal (ℓ (θ x)) * ENNReal.ofReal (w x) ∂m :=
      fun w hw0 => lintegral_congr fun x => ofReal_mul_nonneg _ (hw0 x)
    have p2 : ∀ (w : X → ℝ), (∀ x, 0 ≤ w x) →
        ∫⁻ x, ENNReal.ofReal (-(ℓ (θ x) * w x)) ∂m = ∫⁻ x, ENNReal.ofReal (-ℓ (θ x)) * ENNReal.ofReal (w x) ∂m :=
      fun w hw0 => lintegral_congr fun x => by rw [← neg_mul]; exact ofReal_mul_nonneg _ (hw0 x)
    rw [p1 w₁ hw₁0, p1 w₂ hw₂0, p2 w₁ hw₁0, p2 w₂ hw₂0, s1, s2]
  apply Complex.ext
  · have a₁ := (Complex.reCLM.integral_comp_comm h₁)
    have a₂ := (Complex.reCLM.integral_comp_comm h₂)
    simp only [Complex.reCLM_apply] at a₁ a₂
    have k := key Complex.reCLM
    simp only [Complex.reCLM_apply] at k
    rw [← a₁, ← a₂, k]
  · have a₁ := (Complex.imCLM.integral_comp_comm h₁)
    have a₂ := (Complex.imCLM.integral_comp_comm h₂)
    simp only [Complex.imCLM_apply] at a₁ a₂
    have k := key Complex.imCLM
    simp only [Complex.imCLM_apply] at k
    rw [← a₁, ← a₂, k]

end A1MT
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa.C3 P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa"

end P4
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa.C3 P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 320000

open NumberField IsDedekindDomain MeasureTheory Set Function
open scoped ENNReal NNReal TensorProduct TensorProduct.RightActions Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

noncomputable section

namespace KcSemiLocalIwasawaHaar

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => v.adicCompletion K
local notation "E" => L ⊗[K] v.adicCompletion K
local notation "Q" => (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K)
local notation "G" => GL (Fin 2) (L ⊗[K] v.adicCompletion K)

attribute [local instance 9999] Algebra.toModule
attribute [local instance] isTopologicalRing_E t2Space_E locallyCompactSpace_E continuousSMul_E
  isScalarTower_FEE smulCommClass_FEE finite_KL
attribute [local instance] secondCountableTopology_E
attribute [local instance] t2Space_GL secondCountableTopology_GL locallyCompactSpace_GL
  isTopologicalGroup_GL measurableSpace_GL
attribute [local instance] borelSpace_GL isHaarMeasure_semiLocalHaar
attribute [local instance] measurableMul_GL measurableInv_GL

local notation "μG" => AutomorphicForm.semiLocalHaar K L v
local notation "𝒦" => AutomorphicForm.semiLocalIntegralSet K L v
local notation "μK" => Measure.restrict (AutomorphicForm.semiLocalHaar K L v) (AutomorphicForm.semiLocalIntegralSet K L v)

section A1Main

variable [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]

open scoped Classical

attribute [local instance] borelSpace_Q sigmaFinite_μ sFinite_μ

variable (σ : L ≃ₐ[K] L)

local notation "σG" => AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ
local notation "Wt" => AutomorphicForm.semiLocalWeight K L v

def Dr (p : Q) : ℝ := if p ∈ goodT then ‖Algebra.norm F (p.1 * p.2)‖⁻¹ else 0

theorem Dr_of_mem {p : Q} (hp : p ∈ goodT) : Dr (K := K) (L := L) (v := v) p = ‖Algebra.norm F (p.1 * p.2)‖⁻¹ := by
  simp [Dr, hp]

theorem Dr_of_not {p : Q} (hp : p ∉ goodT) : Dr (K := K) (L := L) (v := v) p = 0 := by
  simp [Dr, hp]

theorem Dr_nonneg (p : Q) : 0 ≤ Dr (K := K) (L := L) (v := v) p := by
  by_cases hp : p ∈ goodT
  · rw [Dr_of_mem hp]; exact inv_nonneg.2 (norm_nonneg _)
  · rw [Dr_of_not hp]

theorem measurable_Dr : Measurable (Dr : Q → ℝ) := by
  refine Measurable.ite measurableSet_goodT ?_ measurable_const
  exact ((continuous_algebraNorm.comp (continuous_fst.mul continuous_snd)).norm).measurable.inv

def Fδ (φ : G → ℂ) (δ : G) (x : G) : ℂ := φ (x⁻¹ * δ * σG x)

theorem Fδ_apply (φ : G → ℂ) (δ x : G) : Fδ σ φ δ x = φ (x⁻¹ * δ * σG x) := rfl

theorem measurable_Fδ [FiniteDimensional K L] {φ : G → ℂ} (hφ : Measurable φ) (δ : G) :
    Measurable (Fδ σ φ δ) :=
  hφ.comp ((continuous_inv.mul continuous_const).mul
    (A1TwIwasawa.C3.continuous_sigmaGL K L F σ)).measurable

theorem Fδ_mul_of_mem (φ : G → ℂ) (δ : G) {t : G}
    (ht : t ∈ AutomorphicForm.twistedCentralizer K L F σ δ) (x : G) :
    Fδ σ φ δ (t * x) = Fδ σ φ δ x := by
  have key : t⁻¹ * δ * σG t = δ := (AutomorphicForm.mem_sigmaCentralizer_iff_inv).1 ht
  simp only [Fδ]
  congr 1
  calc (t * x)⁻¹ * δ * σG (t * x) = x⁻¹ * (t⁻¹ * δ * σG t) * σG x := by
        simp only [mul_inv_rev, map_mul, mul_assoc]
    _ = x⁻¹ * δ * σG x := by rw [key]

def ιK (z : Q × (E × G)) : G := uGL z.1 * nGL z.2.1 * z.2.2

theorem ιK_apply (p : Q) (ξ : E) (k : G) : ιK ((p, (ξ, k)) : Q × (E × G)) = uGL p * nGL ξ * k := rfl

theorem measurable_ιK : Measurable (ιK : Q × (E × G) → G) :=
  ((measurable_uGL.comp measurable_fst).mul
    (measurable_nGL.comp (measurable_fst.comp measurable_snd))).mul (measurable_snd.comp measurable_snd)

def θc (φ : G → ℂ) (δ : G) (c : ℝ) (z : Q × (E × G)) : ℂ :=
  Fδ σ φ δ (ιK z) * ((Wt (nGL z.2.1) + c : ℝ) : ℂ)

theorem measurable_θc [FiniteDimensional K L] {φ : G → ℂ} (hφ : Measurable φ) (δ : G) (c : ℝ) :
    Measurable (θc σ φ δ c) := by
  have hW : Continuous (AutomorphicForm.semiLocalWeight K L v) := A1TwIwasawa.C3.continuous_semiLocalWeight K L v
  exact ((measurable_Fδ σ hφ δ).comp measurable_ιK).mul
    (Complex.measurable_ofReal.comp
      ((hW.measurable.comp (measurable_nGL.comp (measurable_fst.comp measurable_snd))).add_const c))

def tQ (t : G) (p : Q) : Q :=
  ((t : Matrix (Fin 2) (Fin 2) E) 0 0 * p.1, (t : Matrix (Fin 2) (Fin 2) E) 1 1 * p.2)

theorem tQ_mem_goodT_iff {t : G} (ht : A1TwIwasawa.C3.IsDiag t) (p : Q) : tQ t p ∈ goodT ↔ p ∈ goodT := by
  obtain ⟨h0, h1⟩ := A1TwIwasawa.C3.isUnit_diag_entries ht
  obtain ⟨u0, hu0⟩ := h0
  obtain ⟨u1, hu1⟩ := h1
  rw [mem_goodT_iff, mem_goodT_iff, tQ, ← hu0, ← hu1]
  simp only [Units.isUnit_units_mul]

theorem uGL_tQ {t : G} (ht : A1TwIwasawa.C3.IsDiag t) {p : Q} (hp : p ∈ goodT) :
    uGL (tQ t p) = t * uGL p := by
  have htp : tQ t p ∈ goodT := (tQ_mem_goodT_iff ht p).2 hp
  apply Units.ext
  rw [coe_uGL_of_mem (show IsUnit (tm (tQ t p)).det from htp), Units.val_mul,
    coe_uGL_of_mem (show IsUnit (tm p).det from hp)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tm, tQ, Matrix.mul_apply, Fin.sum_univ_two, ht.1, ht.2]

theorem ιK_tQ {t : G} (ht : A1TwIwasawa.C3.IsDiag t) {p : Q} (hp : p ∈ goodT) (y : E × G) :
    ιK ((tQ t p, y) : Q × (E × G)) = t * ιK (p, y) := by
  simp only [ιK, uGL_tQ ht hp, mul_assoc]

theorem uGL_tQ_of_not {t : G} (ht : A1TwIwasawa.C3.IsDiag t) {p : Q} (hp : p ∉ goodT) :
    uGL (tQ t p) = uGL p := by
  have htp : tQ t p ∉ goodT := fun h => hp ((tQ_mem_goodT_iff ht p).1 h)
  rw [uGL_of_not (show ¬ IsUnit (tm (tQ t p)).det from htp), uGL_of_not (show ¬ IsUnit (tm p).det from hp)]

theorem θc_tQ (φ : G → ℂ) (δ : G) (c : ℝ) {t : G}
    (ht : t ∈ AutomorphicForm.twistedCentralizer K L F σ δ) (htd : A1TwIwasawa.C3.IsDiag t)
    (p : Q) (y : E × G) :
    θc σ φ δ c (tQ t p, y) = θc σ φ δ c (p, y) := by
  unfold θc
  by_cases hp : p ∈ goodT
  · rw [ιK_tQ htd hp, Fδ_mul_of_mem σ φ δ ht]
  · have e : ιK ((tQ t p, y) : Q × (E × G)) = ιK (p, y) := by
      change uGL (tQ t p) * nGL y.1 * y.2 = uGL p * nGL y.1 * y.2
      rw [uGL_tQ_of_not htd hp]
    rw [e]

theorem Fδ_ιK_eq (φ : G → ℂ) (α β : Eˣ) {p : Q} (h : IsUnit p.1 ∧ IsUnit p.2) (ξ : E) (k : G) :
    Fδ σ φ (diagUnits2 α β) (ιK (p, (ξ, k))) =
      φ (k⁻¹ * (diagUnits2 (α * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.1.unit * h.1.unit⁻¹) (β * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.2.unit * h.2.unit⁻¹) *
        AutomorphicForm.unipotentGL2 (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ ξ -
          (((β * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.2.unit * h.2.unit⁻¹) * (α * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.1.unit * h.1.unit⁻¹)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K)) * ξ)) *
        AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ k) := by
  have hp : p ∈ goodT := (mem_goodT_iff p).2 h
  rw [Fδ_apply, ιK_apply, uGL_eq_diagUnits2 hp]
  exact congrArg φ (AutomorphicForm.inv_mul_diagUnits2_mul_sigmaGL_of_diagUnits2_mul_unipotentGL2_mul K L F σ α β
    h.1.unit h.2.unit ξ k)

theorem Wt_uGL_nGL_mul {p : Q} (hp : p ∈ goodT) (ξ : E) {k : G} (hk : k ∈ 𝒦) :
    Wt (uGL p * nGL ξ * k) = Wt (nGL ξ) := by
  rw [uGL_eq_diagUnits2 hp]
  exact AutomorphicForm.semiLocalWeight_diagUnits2_mul_mul_eq_of_mem_semiLocalIntegralSet K L v _ _ (nGL ξ) k hk

set_option maxHeartbeats 6400000 in

theorem mainA [FiniteDimensional K L] [IsGalois K L]
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ (α β : (L ⊗[K] v.adicCompletion K)ˣ) (a b : (v.adicCompletion K)ˣ), a ≠ b →
        AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
          AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a b) →
        ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
            (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β))),
          @Measure.IsHaarMeasure _ _ _
            (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ' →
          τ' {x | (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 →
        ∀ βs : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) → ℝ, Measurable βs → (∀ p, 0 ≤ βs p) →
          (∀ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K), IsUnit p.1 → IsUnit p.2 →
            @integral _ ℝ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ'
              (fun t => βs ((((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) * p.1,
                (((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1) * p.2)) = 1) →
        ∀ c : ℝ, ∀ J' I' : ℂ,
          AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ J' →
          AutomorphicForm.IsTwistedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ I' →
          Integrable (fun p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) =>
              (if h : IsUnit p.1 ∧ IsUnit p.2 then
                ((‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ : ℝ) : ℂ) * (βs p : ℂ) *
                  ∫ ξ : (L ⊗[K] v.adicCompletion K),
                    (∫ k in AutomorphicForm.semiLocalIntegralSet K L v, φ (k⁻¹ * (diagUnits2 (α * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.1.unit * h.1.unit⁻¹) (β * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.2.unit * h.2.unit⁻¹) *
                      AutomorphicForm.unipotentGL2 (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ ξ -
                        (((β * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.2.unit * h.2.unit⁻¹) * (α * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.1.unit * h.1.unit⁻¹)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K)) * ξ)) *
                    AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ k)
                      ∂(AutomorphicForm.semiLocalHaar K L v)) *
                    ((AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.unipotentGL2 ξ) + c : ℝ) : ℂ) ∂ν
               else 0)) (ν.prod ν) ∧
          J' + (c : ℂ) * I' = (κ : ℂ) * ∫ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K),
              (if h : IsUnit p.1 ∧ IsUnit p.2 then
                ((‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ : ℝ) : ℂ) * (βs p : ℂ) *
                  ∫ ξ : (L ⊗[K] v.adicCompletion K),
                    (∫ k in AutomorphicForm.semiLocalIntegralSet K L v, φ (k⁻¹ * (diagUnits2 (α * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.1.unit * h.1.unit⁻¹) (β * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.2.unit * h.2.unit⁻¹) *
                      AutomorphicForm.unipotentGL2 (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ ξ -
                        (((β * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.2.unit * h.2.unit⁻¹) * (α * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.1.unit * h.1.unit⁻¹)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K)) * ξ)) *
                    AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ k)
                      ∂(AutomorphicForm.semiLocalHaar K L v)) *
                    ((AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.unipotentGL2 ξ) + c : ℝ) : ℂ) ∂ν
               else 0) ∂(ν.prod ν) := by

  obtain ⟨κ, hκ0, hAb⟩ :=
    AutomorphicForm.exists_pos_forall_integral_semiLocalHaar_eq_mul_integral_integral_setIntegral_iwasawa K L v ν
  obtain ⟨κ', hκ'0, hκ'top, hIw, -⟩ :=
    AutomorphicForm.exists_forall_lintegral_semiLocalHaar_eq_mul_lintegral_torus_unipotentGL2_setLIntegral_semiLocalIntegralSet
      K L v ν
  refine ⟨κ, hκ0, ?_⟩
  intro α β a b hab hN τ' hτ' hτ'1 βs hβm hβ0 hβ1 c J' I' hJ' hI'

  letI : MeasurableSpace (AutomorphicForm.twistedCentralizer K L F σ (diagUnits2 α β)) :=
    AutomorphicForm.twistedCentralizerBorel K L F σ (diagUnits2 α β)
  haveI : BorelSpace (AutomorphicForm.twistedCentralizer K L F σ (diagUnits2 α β)) := ⟨rfl⟩
  haveI := hτ'

  have hφc : Continuous φ := hφ.1.continuous
  have hφm : Measurable φ := hφc.measurable
  obtain ⟨Cφ, hCφ⟩ : ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C := hφc.bounded_above_of_compact_support hφ.2
  have hWc : Continuous (AutomorphicForm.semiLocalWeight K L v) := A1TwIwasawa.C3.continuous_semiLocalWeight K L v

  have hab' : (a : F) ≠ (b : F) := fun h => hab (Units.ext h)
  have hreg : AutomorphicForm.IsRegularSemisimple (diagUnits2 a b) := by
    show IsUnit _
    have e : Matrix.trace ((diagUnits2 a b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ^ 2 -
        4 * Matrix.det ((diagUnits2 a b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = ((a : F) - (b : F)) ^ 2 := by
      rw [LanglandsTunnell.CubicInduction.coe_diagUnits2, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]; ring
    rw [e]
    exact (IsUnit.pow 2 (sub_ne_zero.2 hab').isUnit)
  obtain ⟨-, hTdiag, hregN⟩ := A1TwIwasawa.C3.lift_facts K L σ v (diagUnits2 a b) hreg
    (by simp [LanglandsTunnell.CubicInduction.coe_diagUnits2])
    (by simp [LanglandsTunnell.CubicInduction.coe_diagUnits2]) (diagUnits2 α β) hN
  have hTc : IsClosed ((AutomorphicForm.twistedCentralizer K L F σ (diagUnits2 α β) : Subgroup G) : Set G) :=
    A1TwIwasawa.C3.isClosed_twistedCentralizer K L F σ (diagUnits2 α β)
  have hcomm : ∀ s t : AutomorphicForm.twistedCentralizer K L F σ (diagUnits2 α β), s * t = t * s :=
    fun s t => Subtype.ext (A1TwIwasawa.C3.diag_comm (hTdiag _ s.2) (hTdiag _ t.2))
  haveI : τ'.IsInvInvariant := A1TwIwasawa.C3.isInvInvariant_of_comm E _ hTc hcomm τ'

  obtain ⟨s, ⟨hs0, hsm, hsc, hs1⟩, hJ'eq⟩ := hJ'

  have hI'eq : I' = ∫ x, Fδ σ φ (diagUnits2 α β) x * (s x : ℂ) ∂μG := by
    have h2 : AutomorphicForm.IsTwistedOrbitalIntegralOn K L F σ μG (diagUnits2 α β) τ' φ
        (∫ x, Fδ σ φ (diagUnits2 α β) x * (s x : ℂ) ∂μG) := ⟨s, ⟨hs0, hsm, hsc, hs1⟩, rfl⟩
    exact AutomorphicForm.IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString K L F σ
      (A1TwIwasawa.C3.sigma_pow_finrank K L σ) μG isHaarMeasure_semiLocalHaar (diagUnits2 α β) hregN τ' hτ' φ
      hφm ⟨Cφ, hCφ⟩ hI' h2

  have hFm : Measurable (Fδ σ φ (diagUnits2 α β)) := measurable_Fδ σ hφm _
  have hFb : ∀ x, ‖Fδ σ φ (diagUnits2 α β) x‖ ≤ Cφ := fun x => hCφ _
  have hFT : ∀ (t : AutomorphicForm.twistedCentralizer K L F σ (diagUnits2 α β)) (x : G),
      Fδ σ φ (diagUnits2 α β) ((t : G) * x) = Fδ σ φ (diagUnits2 α β) x :=
    fun t x => Fδ_mul_of_mem σ φ _ t.2 x
  have hanchor : ∫⁻ x, ‖Fδ σ φ (diagUnits2 α β) x‖ₑ * ENNReal.ofReal (s x) ∂μG < ∞ :=
    P2mSectionIntegral.lintegral_enorm_mul_lt_top (AutomorphicForm.twistedCentralizer K L F σ (diagUnits2 α β))
      μG τ' hTc (Fδ σ φ (diagUnits2 α β)) hFm hFb hFT s hs0 hsm hsc hs1

  obtain ⟨CW, hCW⟩ : ∃ C : ℝ, ∀ x ∈ tsupport s, ‖AutomorphicForm.semiLocalWeight K L v x‖ ≤ C :=
    hsc.isCompact.exists_bound_of_continuousOn hWc.continuousOn

  have hdom : ∀ (g : G → ℂ), Measurable g → (∃ C : ℝ, ∀ x,
      ‖g x‖ₑ ≤ ENNReal.ofReal C * (‖Fδ σ φ (diagUnits2 α β) x‖ₑ * ENNReal.ofReal (s x))) → Integrable g μG := by
    intro g hgm hgb
    obtain ⟨C, hC⟩ := hgb
    refine ⟨hgm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    calc ∫⁻ x, ‖g x‖ₑ ∂μG
        ≤ ∫⁻ x, ENNReal.ofReal C * (‖Fδ σ φ (diagUnits2 α β) x‖ₑ * ENNReal.ofReal (s x)) ∂μG := lintegral_mono hC
      _ = ENNReal.ofReal C * ∫⁻ x, ‖Fδ σ φ (diagUnits2 α β) x‖ₑ * ENNReal.ofReal (s x) ∂μG :=
          lintegral_const_mul _ (hFm.enorm.mul (ENNReal.measurable_ofReal.comp hsm))
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hanchor

  set Φ : G → ℂ := fun x => Fδ σ φ (diagUnits2 α β) x * ((Wt x + c : ℝ) : ℂ) * (s x : ℂ) with hΦ
  have hΦm : Measurable Φ :=
    (hFm.mul (Complex.measurable_ofReal.comp (hWc.measurable.add_const c))).mul (Complex.measurable_ofReal.comp hsm)
  have hΦJm : Measurable fun x => Fδ σ φ (diagUnits2 α β) x * ((Wt x : ℝ) : ℂ) * (s x : ℂ) :=
    (hFm.mul (Complex.measurable_ofReal.comp hWc.measurable)).mul (Complex.measurable_ofReal.comp hsm)
  have hΦIm : Measurable fun x => Fδ σ φ (diagUnits2 α β) x * (s x : ℂ) :=
    hFm.mul (Complex.measurable_ofReal.comp hsm)
  have hbd : ∀ (w : G → ℝ) (C : ℝ), (∀ x ∈ tsupport s, ‖w x‖ ≤ C) → ∀ x,
      ‖Fδ σ φ (diagUnits2 α β) x * ((w x : ℝ) : ℂ) * (s x : ℂ)‖ₑ ≤
        ENNReal.ofReal C * (‖Fδ σ φ (diagUnits2 α β) x‖ₑ * ENNReal.ofReal (s x)) := by
    intro w C hC x
    by_cases hx : x ∈ tsupport s
    · rw [enorm_mul, enorm_mul, A1MT.enorm_real_of_nonneg (hs0 x)]
      have h1 : ‖((w x : ℝ) : ℂ)‖ₑ ≤ ENNReal.ofReal C := by
        rw [← ofReal_norm, Complex.norm_real]
        exact ENNReal.ofReal_le_ofReal (hC x hx)
      calc ‖Fδ σ φ (diagUnits2 α β) x‖ₑ * ‖((w x : ℝ) : ℂ)‖ₑ * ENNReal.ofReal (s x)
          ≤ ‖Fδ σ φ (diagUnits2 α β) x‖ₑ * ENNReal.ofReal C * ENNReal.ofReal (s x) := by gcongr
        _ = ENNReal.ofReal C * (‖Fδ σ φ (diagUnits2 α β) x‖ₑ * ENNReal.ofReal (s x)) := by ring
    · have h0 : s x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [h0]
  have hΦint : Integrable Φ μG := by
    refine hdom Φ hΦm ⟨CW + ‖c‖, hbd (fun x => Wt x + c) (CW + ‖c‖) (fun x hx => ?_)⟩
    exact (norm_add_le _ _).trans (add_le_add (hCW x hx) le_rfl)
  have hΦJint : Integrable (fun x => Fδ σ φ (diagUnits2 α β) x * ((Wt x : ℝ) : ℂ) * (s x : ℂ)) μG :=
    hdom _ hΦJm ⟨CW, hbd _ CW hCW⟩
  have hΦIint : Integrable (fun x => Fδ σ φ (diagUnits2 α β) x * (s x : ℂ)) μG := by
    refine hdom _ hΦIm ⟨1, fun x => ?_⟩
    rw [enorm_mul, A1MT.enorm_real_of_nonneg (hs0 x), ENNReal.ofReal_one, one_mul]

  have hsum : J' + (c : ℂ) * I' = ∫ x, Φ x ∂μG := by
    have eJ : J' = ∫ x, Fδ σ φ (diagUnits2 α β) x * ((Wt x : ℝ) : ℂ) * (s x : ℂ) ∂μG := hJ'eq
    rw [eJ, hI'eq, ← integral_const_mul, ← integral_add hΦJint (hΦIint.const_mul _)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [hΦ]
    push_cast
    ring

  have hB := hAb Φ hΦm hΦint

  set θ : Q × (E × G) → ℂ := θc σ φ (diagUnits2 α β) c with hθ
  set w₁ : Q × (E × G) → ℝ := fun z => Dr z.1 * s (ιK z) with hw₁
  set w₂ : Q × (E × G) → ℝ := fun z => Dr z.1 * βs z.1 with hw₂
  have hθm : Measurable θ := measurable_θc σ hφm _ c
  have hw₁m : Measurable w₁ := (measurable_Dr.comp measurable_fst).mul (hsm.comp measurable_ιK)
  have hw₂m : Measurable w₂ := (measurable_Dr.comp measurable_fst).mul (hβm.comp measurable_fst)
  have hw₁0 : ∀ z, 0 ≤ w₁ z := fun z => mul_nonneg (Dr_nonneg _) (hs0 _)
  have hw₂0 : ∀ z, 0 ≤ w₂ z := fun z => mul_nonneg (Dr_nonneg _) (hβ0 _)

  have hΦchart : ∀ {p : Q}, p ∈ goodT → ∀ (ξ : E) {k : G}, k ∈ 𝒦 →
      Φ (uGL p * nGL ξ * k) = θ (p, (ξ, k)) * (s (ιK (p, (ξ, k))) : ℂ) := by
    intro p hp ξ k hk
    simp only [hΦ, hθ, θc, ιK_apply]
    rw [Wt_uGL_nGL_mul hp ξ hk]

  have hfin : ∫⁻ z, ‖θ z‖ₑ * ENNReal.ofReal (w₁ z) ∂((ν.prod ν).prod (ν.prod μK)) < ∞ := by
    have hmeas : Measurable fun z : Q × (E × G) => ‖θ z‖ₑ * ENNReal.ofReal (w₁ z) :=
      hθm.enorm.mul (ENNReal.measurable_ofReal.comp hw₁m)
    rw [lintegral_prod _ hmeas.aemeasurable]
    have hG : ∫⁻ g, ‖Φ g‖ₑ ∂μG < ∞ := by
      have hG' := hΦint.2
      rwa [hasFiniteIntegral_iff_enorm] at hG'
    have hIwΦ := hIw (fun g => ‖Φ g‖ₑ) hΦm.enorm

    have hpt : ∀ p : Q, ∫⁻ y, ‖θ (p, y)‖ₑ * ENNReal.ofReal (w₁ (p, y)) ∂(ν.prod μK) =
        (if h : IsUnit (!![p.1, 0; 0, p.2] : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det then
            ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ *
              ∫⁻ x : L ⊗[K] v.adicCompletion K,
                 ∫⁻ k in AutomorphicForm.semiLocalIntegralSet K L v,
                    ‖Φ (Matrix.GeneralLinearGroup.mk'' _ h * AutomorphicForm.unipotentGL2 x * k)‖ₑ
                      ∂(AutomorphicForm.semiLocalHaar K L v) ∂ν
          else 0) := by
      intro p
      have hmy : Measurable fun y : E × G => ‖θ (p, y)‖ₑ * ENNReal.ofReal (w₁ (p, y)) :=
        hmeas.comp (measurable_const.prodMk measurable_id)
      rw [lintegral_prod _ hmy.aemeasurable]
      by_cases hp : p ∈ goodT
      · have h : IsUnit (!![p.1, 0; 0, p.2] : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det := hp
        rw [dif_pos h, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun ξ => ?_
        beta_reduce
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine setLIntegral_congr_fun measurableSet_K (fun k hk => ?_)
        have e1 : Matrix.GeneralLinearGroup.mk'' _ h * AutomorphicForm.unipotentGL2 ξ * k = uGL p * nGL ξ * k := by
          rw [uGL_of_mem h]; rfl
        rw [e1, hΦchart hp ξ hk, enorm_mul, A1MT.enorm_real_of_nonneg (hs0 _)]
        simp only [hw₁, Dr_of_mem hp, ιK_apply]
        rw [A1MT.ofReal_mul_nonneg _ (hs0 _)]
        ring
      · have h : ¬ IsUnit (!![p.1, 0; 0, p.2] : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det := hp
        rw [dif_neg h]
        have e0 : ∀ (ξ : E) (k : G), ‖θ (p, (ξ, k))‖ₑ * ENNReal.ofReal (w₁ (p, (ξ, k))) = 0 := by
          intro ξ k
          simp only [hw₁, Dr_of_not hp, zero_mul, ENNReal.ofReal_zero, mul_zero]
        simp_rw [e0, lintegral_zero]
    rw [lintegral_congr hpt]
    rw [hIwΦ] at hG
    exact ENNReal.lt_top_of_mul_ne_top_right hG.ne hκ'0

  have hswap : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ → ψ 0 = 0 →
      ∫⁻ z, ψ (θ z) * ENNReal.ofReal (w₁ z) ∂((ν.prod ν).prod (ν.prod μK)) =
        ∫⁻ z, ψ (θ z) * ENNReal.ofReal (w₂ z) ∂((ν.prod ν).prod (ν.prod μK)) := by
    intro ψ hψ hψ0
    have hm₁ : Measurable fun z : Q × (E × G) => ψ (θ z) * ENNReal.ofReal (w₁ z) :=
      (hψ.comp hθm).mul (ENNReal.measurable_ofReal.comp hw₁m)
    have hm₂ : Measurable fun z : Q × (E × G) => ψ (θ z) * ENNReal.ofReal (w₂ z) :=
      (hψ.comp hθm).mul (ENNReal.measurable_ofReal.comp hw₂m)
    rw [lintegral_prod _ hm₁.aemeasurable, lintegral_prod _ hm₂.aemeasurable]
    conv_lhs => rw [lintegral_lintegral_swap hm₁.aemeasurable]
    conv_rhs => rw [lintegral_lintegral_swap hm₂.aemeasurable]
    refine lintegral_congr fun y => ?_

    set β₁ : Q → ℝ := fun p => if Fδ σ φ (diagUnits2 α β) (ιK (p, y)) = 0 then βs p else s (ιK (p, y)) with hβ₁
    have hιy : Measurable fun p : Q => ιK ((p, y) : Q × (E × G)) := measurable_ιK.comp (measurable_id.prodMk measurable_const)
    have hβ₁m : Measurable β₁ :=
      Measurable.ite (hFm.comp hιy (measurableSet_singleton 0)) hβm (hsm.comp hιy)
    have hβ₁0 : ∀ p, 0 ≤ β₁ p := by
      intro p; simp only [hβ₁]; split_ifs; exacts [hβ0 _, hs0 _]
    have hβ₁1 : ∀ p : Q, IsUnit p.1 → IsUnit p.2 →
        ∫ t : AutomorphicForm.twistedCentralizer K L F σ (diagUnits2 α β),
          β₁ ((((t : G) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) * p.1,
              (((t : G) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1) * p.2) ∂τ' = 1 := by
      intro p h1 h2
      have hp : p ∈ goodT := (mem_goodT_iff p).2 ⟨h1, h2⟩
      have htor : ∀ t : AutomorphicForm.twistedCentralizer K L F σ (diagUnits2 α β),
          ιK ((tQ (t : G) p, y) : Q × (E × G)) = (t : G) * ιK (p, y) := fun t => ιK_tQ (hTdiag _ t.2) hp y
      change ∫ t : AutomorphicForm.twistedCentralizer K L F σ (diagUnits2 α β), β₁ (tQ (t : G) p) ∂τ' = 1
      by_cases hF0 : Fδ σ φ (diagUnits2 α β) (ιK (p, y)) = 0
      · have e : ∀ t : AutomorphicForm.twistedCentralizer K L F σ (diagUnits2 α β),
            β₁ (tQ (t : G) p) = βs (tQ (t : G) p) := by
          intro t; simp only [hβ₁]; rw [htor t, hFT, if_pos hF0]
        simp_rw [e]; exact hβ1 p h1 h2
      · have e : ∀ t : AutomorphicForm.twistedCentralizer K L F σ (diagUnits2 α β),
            β₁ (tQ (t : G) p) = s ((t : G) * ιK (p, y)) := by
          intro t; simp only [hβ₁]; rw [htor t, hFT, if_neg hF0]
        simp_rw [e]; exact hs1 (ιK (p, y)) hF0
    have hH : ∀ (t : AutomorphicForm.twistedCentralizer K L F σ (diagUnits2 α β)) (p : Q),
        ψ (θ ((((t : G) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0 * p.1,
               ((t : G) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1 * p.2), y)) = ψ (θ (p, y)) := by
      intro t p
      change ψ (θ (tQ (t : G) p, y)) = ψ (θ (p, y))
      rw [hθ, θc_tQ σ φ _ c t.2 (hTdiag _ t.2)]
    have hHm : Measurable fun p : Q => ψ (θ (p, y)) := hψ.comp (hθm.comp (measurable_id.prodMk measurable_const))
    have hSW := AutomorphicForm.lintegral_norm_inv_mul_torusSection_mul_eq_of_forall_mul_eq K L σ hgen v ν α β a b
      hab hN τ' hτ' β₁ βs hβ₁m hβm hβ₁0 hβ0 hβ₁1 hβ1 (fun p => ψ (θ (p, y))) hHm hH
    have lhs : ∀ p : Q, ψ (θ (p, y)) * ENNReal.ofReal (w₁ (p, y)) =
        (if IsUnit p.1 ∧ IsUnit p.2 then
          ENNReal.ofReal (‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ * β₁ p) * ψ (θ (p, y)) else 0) := by
      intro p
      by_cases hp : p ∈ goodT
      · have h := (mem_goodT_iff p).1 hp
        rw [if_pos h]
        simp only [hw₁, Dr_of_mem hp]
        by_cases hF0 : Fδ σ φ (diagUnits2 α β) (ιK (p, y)) = 0
        · have hz : θ (p, y) = 0 := by
            rw [hθ]
            change Fδ σ φ (diagUnits2 α β) (ιK (p, y)) * _ = 0
            rw [hF0, zero_mul]
          rw [hz, hψ0, zero_mul, mul_zero]
        · simp only [hβ₁, if_neg hF0]; rw [mul_comm]
      · have h : ¬ (IsUnit p.1 ∧ IsUnit p.2) := fun h => hp ((mem_goodT_iff p).2 h)
        rw [if_neg h]
        simp only [hw₁, Dr_of_not hp, zero_mul, ENNReal.ofReal_zero, mul_zero]
    have rhs : ∀ p : Q, ψ (θ (p, y)) * ENNReal.ofReal (w₂ (p, y)) =
        (if IsUnit p.1 ∧ IsUnit p.2 then
          ENNReal.ofReal (‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ * βs p) * ψ (θ (p, y)) else 0) := by
      intro p
      by_cases hp : p ∈ goodT
      · have h := (mem_goodT_iff p).1 hp
        rw [if_pos h]
        simp only [hw₂, Dr_of_mem hp]
        rw [mul_comm]
      · have h : ¬ (IsUnit p.1 ∧ IsUnit p.2) := fun h => hp ((mem_goodT_iff p).2 h)
        rw [if_neg h]
        simp only [hw₂, Dr_of_not hp, zero_mul, ENNReal.ofReal_zero, mul_zero]
    simp_rw [lhs, rhs]
    exact hSW

  obtain ⟨hΘ₁int, hΘ₂int, hΘeq⟩ :=
    A1MT.integral_mul_eq_integral_mul_of_forall_lintegral_eq ((ν.prod ν).prod (ν.prod μK)) θ w₁ w₂ hθm hw₁m hw₂m
      hw₁0 hw₂0 hswap hfin

  have hE1 : ∀ᵐ p ∂(ν.prod ν),
      (if h : IsUnit p.1 ∧ IsUnit p.2 then
          ((‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ : ℝ) : ℂ) *
            ∫ ξ : (L ⊗[K] v.adicCompletion K), ∫ k in AutomorphicForm.semiLocalIntegralSet K L v,
              Φ (diagUnits2 h.1.unit h.2.unit * AutomorphicForm.unipotentGL2 ξ * k)
              ∂(AutomorphicForm.semiLocalHaar K L v) ∂ν
        else 0) = ∫ y, θ (p, y) * (w₁ (p, y) : ℂ) ∂(ν.prod μK) := by
    filter_upwards [hΘ₁int.prod_right_ae] with p hp_int
    have hp_int' : Integrable (fun y : E × G => θ (p, y) * (w₁ (p, y) : ℂ)) (ν.prod μK) := hp_int
    by_cases hp : p ∈ goodT
    · have h : IsUnit p.1 ∧ IsUnit p.2 := (mem_goodT_iff p).1 hp
      rw [dif_pos h, integral_prod _ hp_int', ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
      beta_reduce
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_K (fun k hk => ?_)
      have e1 : diagUnits2 h.1.unit h.2.unit * AutomorphicForm.unipotentGL2 ξ * k = uGL p * nGL ξ * k := by
        rw [uGL_eq_diagUnits2 hp]; rfl
      rw [e1, hΦchart hp ξ hk]
      simp only [hw₁, Dr_of_mem hp, ιK_apply]
      push_cast
      ring
    · have h : ¬ (IsUnit p.1 ∧ IsUnit p.2) := fun h => hp ((mem_goodT_iff p).2 h)
      rw [dif_neg h]
      have e0 : (fun y : E × G => θ (p, y) * (w₁ (p, y) : ℂ)) = fun _ => 0 := by
        funext y
        simp only [hw₁, Dr_of_not hp, zero_mul, Complex.ofReal_zero, mul_zero]
      rw [e0, integral_zero]

  have hE5 : ∀ᵐ p ∂(ν.prod ν), ∫ y, θ (p, y) * (w₂ (p, y) : ℂ) ∂(ν.prod μK) = (fun p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) =>
              (if h : IsUnit p.1 ∧ IsUnit p.2 then
                ((‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ : ℝ) : ℂ) * (βs p : ℂ) *
                  ∫ ξ : (L ⊗[K] v.adicCompletion K),
                    (∫ k in AutomorphicForm.semiLocalIntegralSet K L v, φ (k⁻¹ * (diagUnits2 (α * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.1.unit * h.1.unit⁻¹) (β * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.2.unit * h.2.unit⁻¹) *
                      AutomorphicForm.unipotentGL2 (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ ξ -
                        (((β * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.2.unit * h.2.unit⁻¹) * (α * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.1.unit * h.1.unit⁻¹)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K)) * ξ)) *
                    AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ k)
                      ∂(AutomorphicForm.semiLocalHaar K L v)) *
                    ((AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.unipotentGL2 ξ) + c : ℝ) : ℂ) ∂ν
               else 0)) p := by
    filter_upwards [hΘ₂int.prod_right_ae] with p hp_int
    have hp_int' : Integrable (fun y : E × G => θ (p, y) * (w₂ (p, y) : ℂ)) (ν.prod μK) := hp_int
    by_cases hp : p ∈ goodT
    · have h : IsUnit p.1 ∧ IsUnit p.2 := (mem_goodT_iff p).1 hp
      rw [dif_pos h, integral_prod _ hp_int', ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
      beta_reduce
      rw [← integral_mul_const, ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun k => ?_)
      beta_reduce
      rw [hθ]
      change Fδ σ φ (diagUnits2 α β) (ιK (p, (ξ, k))) * ((Wt (nGL ξ) + c : ℝ) : ℂ) * (w₂ (p, (ξ, k)) : ℂ) = _
      rw [Fδ_ιK_eq σ φ α β h ξ k]
      simp only [hw₂, Dr_of_mem hp, nGL]
      push_cast
      ring
    · have h : ¬ (IsUnit p.1 ∧ IsUnit p.2) := fun h => hp ((mem_goodT_iff p).2 h)
      rw [dif_neg h]
      have e0 : (fun y : E × G => θ (p, y) * (w₂ (p, y) : ℂ)) = fun _ => 0 := by
        funext y
        simp only [hw₂, Dr_of_not hp, zero_mul, Complex.ofReal_zero, mul_zero]
      rw [e0, integral_zero]
  refine ⟨?_, ?_⟩
  · exact (hΘ₂int.integral_prod_left).congr hE5
  · rw [hsum, hB, integral_congr_ae hE1, ← integral_prod _ hΘ₁int, hΘeq, integral_prod _ hΘ₂int,
      integral_congr_ae hE5]

end A1Main
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa.C3 P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa"

end KcSemiLocalIwasawaHaar
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa.C3 P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa.C3 P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.A1TwIwasawa"

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions Classical

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ) :
    letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
    ∃ κ : ℝ, 0 < κ ∧
      ∀ (α β : (L ⊗[K] v.adicCompletion K)ˣ) (a b : (v.adicCompletion K)ˣ), a ≠ b →
        AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
          AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a b) →
        ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
            (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β))),
          @Measure.IsHaarMeasure _ _ _
            (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ' →
          τ' {x | (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 →
        ∀ βs : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) → ℝ, Measurable βs → (∀ p, 0 ≤ βs p) →
          (∀ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K), IsUnit p.1 → IsUnit p.2 →
            @integral _ ℝ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ'
              (fun t => βs ((((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) * p.1,
                (((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1) * p.2)) = 1) →
        ∀ c : ℝ, ∀ J' I' : ℂ,
          AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ J' →
          AutomorphicForm.IsTwistedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ I' →
          Integrable (fun p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) =>
              (if h : IsUnit p.1 ∧ IsUnit p.2 then
                ((‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ : ℝ) : ℂ) * (βs p : ℂ) *
                  ∫ ξ : (L ⊗[K] v.adicCompletion K),
                    (∫ k in AutomorphicForm.semiLocalIntegralSet K L v, φ (k⁻¹ * (diagUnits2 (α * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.1.unit * h.1.unit⁻¹) (β * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.2.unit * h.2.unit⁻¹) *
                      AutomorphicForm.unipotentGL2 (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ ξ -
                        (((β * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.2.unit * h.2.unit⁻¹) * (α * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.1.unit * h.1.unit⁻¹)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K)) * ξ)) *
                    AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ k)
                      ∂(AutomorphicForm.semiLocalHaar K L v)) *
                    ((AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.unipotentGL2 ξ) + c : ℝ) : ℂ) ∂ν
               else 0)) (ν.prod ν) ∧
          J' + (c : ℂ) * I' = (κ : ℂ) * ∫ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K),
              (if h : IsUnit p.1 ∧ IsUnit p.2 then
                ((‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ : ℝ) : ℂ) * (βs p : ℂ) *
                  ∫ ξ : (L ⊗[K] v.adicCompletion K),
                    (∫ k in AutomorphicForm.semiLocalIntegralSet K L v, φ (k⁻¹ * (diagUnits2 (α * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.1.unit * h.1.unit⁻¹) (β * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.2.unit * h.2.unit⁻¹) *
                      AutomorphicForm.unipotentGL2 (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ ξ -
                        (((β * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.2.unit * h.2.unit⁻¹) * (α * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.1.unit * h.1.unit⁻¹)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K)) * ξ)) *
                    AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ k)
                      ∂(AutomorphicForm.semiLocalHaar K L v)) *
                    ((AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.unipotentGL2 ξ) + c : ℝ) : ℂ) ∂ν
               else 0) ∂(ν.prod ν) := by
  exact KcSemiLocalIwasawaHaar.mainA σ hgen ν φ hφ

end S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq
end P2MW
export P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq (solution)
