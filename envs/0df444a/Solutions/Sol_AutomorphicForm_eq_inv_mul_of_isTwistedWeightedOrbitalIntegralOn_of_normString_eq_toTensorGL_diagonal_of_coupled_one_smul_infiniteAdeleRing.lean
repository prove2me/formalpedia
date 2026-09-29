-- Prove2me | solution 1 for AutomorphicForm.eq_inv_mul_of_isTwistedWeightedOrbitalIntegralOn_of_normString_eq_toTensorGL_diagonal_of_coupled_one_smul_infiniteAdeleRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b0fb3e77-fb6e-527c-a43b-360d4bc833ae

import Mathlib
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_AutomorphicForm_IsTwistedWeightedOrbitalIntegralOn_unique_of_isRegularSemisimple_normString_of_forall_twistedCentralizer_mul_eq
import Theorems.Thm_AutomorphicForm_exists_units_eq_sigmaTensor_mul_inv_of_prod_iterate_sigmaTensor_eq_one_infiniteAdeleRing
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_eq_inv_mul_of_isTwistedWeightedOrbitalIntegralOn_of_normString_eq_toTensorGL_diagonal_of_coupled_one_smul_infiniteAdeleRing
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory NumberField TensorProduct
open scoped TensorProduct.RightActions

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

noncomputable section

namespace C3f25

open AutomorphicForm
open LanglandsTunnell.CubicInduction (diagUnits2)

section generic
variable {R : Type*} [CommRing R]

theorem val_mul_apply (x y : GL (Fin 2) R) (i j : Fin 2) :
    ((x * y : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i j =
      (x : Matrix (Fin 2) (Fin 2) R) i 0 * (y : Matrix (Fin 2) (Fin 2) R) 0 j +
        (x : Matrix (Fin 2) (Fin 2) R) i 1 * (y : Matrix (Fin 2) (Fin 2) R) 1 j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem offdiag_eq_zero_of_commute (T t : GL (Fin 2) R)
    (hT01 : (T : Matrix (Fin 2) (Fin 2) R) 0 1 = 0) (hT10 : (T : Matrix (Fin 2) (Fin 2) R) 1 0 = 0)
    (hreg : IsUnit ((T : Matrix (Fin 2) (Fin 2) R) 0 0 - (T : Matrix (Fin 2) (Fin 2) R) 1 1))
    (hc : T * t = t * T) :
    (t : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := by
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
  have h2 : IsUnit (Matrix.trace (T : Matrix (Fin 2) (Fin 2) R) ^ 2 - 4 * Matrix.det (T : Matrix (Fin 2) (Fin 2) R)) := hreg
  rw [h] at h2
  exact (IsUnit.mul_iff.mp h2).1

theorem isRegularSemisimple_of_isUnit_sub (T : GL (Fin 2) R)
    (hT01 : (T : Matrix (Fin 2) (Fin 2) R) 0 1 = 0) (hT10 : (T : Matrix (Fin 2) (Fin 2) R) 1 0 = 0)
    (hu : IsUnit ((T : Matrix (Fin 2) (Fin 2) R) 0 0 - (T : Matrix (Fin 2) (Fin 2) R) 1 1)) :
    IsRegularSemisimple T := by
  have h : Matrix.trace (T : Matrix (Fin 2) (Fin 2) R) ^ 2 - 4 * Matrix.det (T : Matrix (Fin 2) (Fin 2) R) =
      ((T : Matrix (Fin 2) (Fin 2) R) 0 0 - (T : Matrix (Fin 2) (Fin 2) R) 1 1) *
        ((T : Matrix (Fin 2) (Fin 2) R) 0 0 - (T : Matrix (Fin 2) (Fin 2) R) 1 1) := by
    rw [Matrix.trace_fin_two, Matrix.det_fin_two, hT01, hT10]; ring
  show IsUnit _
  rw [h]; exact hu.mul hu

theorem diag_mul_comm (s t : GL (Fin 2) R)
    (hs01 : (s : Matrix (Fin 2) (Fin 2) R) 0 1 = 0) (hs10 : (s : Matrix (Fin 2) (Fin 2) R) 1 0 = 0)
    (ht01 : (t : Matrix (Fin 2) (Fin 2) R) 0 1 = 0) (ht10 : (t : Matrix (Fin 2) (Fin 2) R) 1 0 = 0) :
    s * t = t * s := by
  apply Units.ext
  ext i j
  rw [val_mul_apply, val_mul_apply]
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, hs01, ht10, hs10, ht01, mul_zero, add_zero]; ring
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, hs01, ht01, mul_zero, zero_mul, add_zero]
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, hs10, ht10, mul_zero, zero_mul, add_zero]
  · simp only [Fin.mk_one, Fin.isValue, hs01, ht10, hs10, ht01, zero_mul, zero_add]; ring

theorem isUnit_diag_entries (g : GL (Fin 2) R)
    (h01 : (g : Matrix (Fin 2) (Fin 2) R) 0 1 = 0) (h10 : (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0) :
    IsUnit ((g : Matrix (Fin 2) (Fin 2) R) 0 0) ∧ IsUnit ((g : Matrix (Fin 2) (Fin 2) R) 1 1) := by
  have hdet : IsUnit (g : Matrix (Fin 2) (Fin 2) R).det := (Matrix.isUnits_det_units g)
  rw [Matrix.det_fin_two, h01, h10, mul_zero, sub_zero] at hdet
  exact IsUnit.mul_iff.mp hdet

theorem coe_diagUnits2_inv (x y : Rˣ) :
    (((diagUnits2 x y)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = !![((x⁻¹ : Rˣ) : R), 0; 0, ((y⁻¹ : Rˣ) : R)] :=
  rfl

end generic

section sigma

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]

theorem sigmaTensor_mul_apply (σ τ : L ≃ₐ[K] L) (x : L ⊗[K] A) :
    sigmaTensor K L A (σ * τ) x = sigmaTensor K L A σ (sigmaTensor K L A τ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l a =>
    change Algebra.TensorProduct.map (σ * τ).toAlgHom (AlgHom.id K A) (l ⊗ₜ a) =
      Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A) (Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id K A) (l ⊗ₜ a))
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

theorem sigmaTensor_iterate_mul (σ : L ≃ₐ[K] L) (n : ℕ) (x y : L ⊗[K] A) :
    (⇑(sigmaTensor K L A σ))^[n] (x * y) = (⇑(sigmaTensor K L A σ))^[n] x * (⇑(sigmaTensor K L A σ))^[n] y := by
  rw [sigmaTensor_iterate, sigmaTensor_iterate, sigmaTensor_iterate, map_mul]

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

theorem orderOf_dvd_finrank [FiniteDimensional K L] (σ : L ≃ₐ[K] L) : orderOf σ ∣ Module.finrank K L := by
  have h1 : Module.finrank (IntermediateField.fixedField (Subgroup.zpowers σ)) L = Nat.card (Subgroup.zpowers σ) :=
    IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers σ)
  rw [Nat.card_zpowers] at h1
  rw [← h1]
  exact Dvd.intro_left _ (Module.finrank_mul_finrank K (IntermediateField.fixedField (Subgroup.zpowers σ)) L)

theorem pow_finrank_eq_one [FiniteDimensional K L] (σ : L ≃ₐ[K] L) : σ ^ Module.finrank K L = 1 :=
  orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_finrank K L σ)

theorem sigmaGL_iterate_finrank [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (x : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(sigmaGL K L A σ))^[Module.finrank K L] x = x := by
  apply Units.ext
  ext i j
  rw [sigmaGL_iterate_apply, sigmaTensor_iterate, pow_finrank_eq_one, sigmaTensor_one_apply]

theorem sigmaTensor_includeRight (σ : L ≃ₐ[K] L) (a : A) :
    sigmaTensor K L A σ (Algebra.TensorProduct.includeRight (R := K) (A := L) a) =
      Algebra.TensorProduct.includeRight (R := K) (A := L) a := by
  change Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A) ((1 : L) ⊗ₜ a) = (1 : L) ⊗ₜ a
  rw [Algebra.TensorProduct.map_tmul]
  simp

theorem toTensorGL_apply (γ : GL (Fin 2) A) (i j : Fin 2) :
    ((toTensorGL K L A γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      Algebra.TensorProduct.includeRight (R := K) (A := L) ((γ : Matrix (Fin 2) (Fin 2) A) i j) := rfl

theorem sigmaGL_toTensorGL (σ : L ≃ₐ[K] L) (γ : GL (Fin 2) A) :
    sigmaGL K L A σ (toTensorGL K L A γ) = toTensorGL K L A γ := by
  apply Units.ext
  ext i j
  rw [sigmaGL_apply, toTensorGL_apply, sigmaTensor_includeRight]

def P (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) (n : ℕ) : GL (Fin 2) (L ⊗[K] A) :=
  ((List.range n).map fun i => (⇑(sigmaGL K L A σ))^[i] δ).prod

theorem P_succ (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) (n : ℕ) :
    P K L A σ δ (n + 1) = P K L A σ δ n * (⇑(sigmaGL K L A σ))^[n] δ := by
  simp only [P, List.range_succ, List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]

theorem normString_eq_P (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) :
    normString K L A σ δ = P K L A σ δ (Module.finrank K L) := rfl

theorem iterate_sigmaGL_mul (σ : L ≃ₐ[K] L) (n : ℕ) (x y : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(sigmaGL K L A σ))^[n] (x * y) = (⇑(sigmaGL K L A σ))^[n] x * (⇑(sigmaGL K L A σ))^[n] y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_mul]

theorem mul_sigmaGL_P (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) (n : ℕ) :
    δ * sigmaGL K L A σ (P K L A σ δ n) = P K L A σ δ (n + 1) := by
  induction n with
  | zero => simp [P]
  | succ n ih =>
    show δ * sigmaGL K L A σ (P K L A σ δ (n + 1)) = P K L A σ δ (n + 1 + 1)
    rw [P_succ K L A σ δ (n + 1), Function.iterate_succ_apply', P_succ K L A σ δ n, map_mul, ← mul_assoc, ih,
      ← P_succ]

theorem mul_normString_comm [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A))
    (hN : sigmaGL K L A σ (normString K L A σ δ) = normString K L A σ δ) :
    δ * normString K L A σ δ = normString K L A σ δ * δ := by
  have h := mul_sigmaGL_P K L A σ δ (Module.finrank K L)
  rw [P_succ, sigmaGL_iterate_finrank, ← normString_eq_P, hN] at h
  exact h

theorem mul_normString_comm_of_mem_twistedCentralizer [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
    (δ t : GL (Fin 2) (L ⊗[K] A)) (ht : t ∈ twistedCentralizer K L A σ δ) :
    normString K L A σ δ * t = t * normString K L A σ δ := by
  have htδ : t * δ = δ * sigmaGL K L A σ t := by
    have h : t * δ * (sigmaGL K L A σ t)⁻¹ = δ := mem_sigmaCentralizer_iff.mp ht
    calc t * δ = t * δ * (sigmaGL K L A σ t)⁻¹ * sigmaGL K L A σ t := by group
      _ = δ * sigmaGL K L A σ t := by rw [h]
  have hP : ∀ n : ℕ, t * P K L A σ δ n = P K L A σ δ n * (⇑(sigmaGL K L A σ))^[n] t := by
    intro n
    induction n with
    | zero => simp [P]
    | succ n ih =>
      rw [P_succ, ← mul_assoc, ih, mul_assoc, ← iterate_sigmaGL_mul, htδ, iterate_sigmaGL_mul,
        ← Function.iterate_succ_apply (⇑(sigmaGL K L A σ)) n t, mul_assoc]
  have h := hP (Module.finrank K L)
  rw [sigmaGL_iterate_finrank, ← normString_eq_P] at h
  exact h.symm

theorem P_diag (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A))
    (h01 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0)
    (h10 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0) (n : ℕ) :
    ((P K L A σ δ n : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0 ∧
    ((P K L A σ δ n : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0 ∧
    ((P K L A σ δ n : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 =
      ((List.range n).map fun i => (⇑(sigmaTensor K L A σ))^[i] ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0)).prod ∧
    ((P K L A σ δ n : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1 =
      ((List.range n).map fun i => (⇑(sigmaTensor K L A σ))^[i] ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1)).prod := by
  induction n with
  | zero => simp [P]
  | succ n ih =>
    obtain ⟨ih01, ih10, ih00, ih11⟩ := ih
    have e01 : (((⇑(sigmaGL K L A σ))^[n] δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0 := by
      rw [sigmaGL_iterate_apply, h01]; exact Function.iterate_fixed (map_zero _) n
    have e10 : (((⇑(sigmaGL K L A σ))^[n] δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0 := by
      rw [sigmaGL_iterate_apply, h10]; exact Function.iterate_fixed (map_zero _) n
    rw [P_succ]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [val_mul_apply, ih01, e01, mul_zero, zero_mul, add_zero]
    · rw [val_mul_apply, ih10, e10, mul_zero, zero_mul, add_zero]
    · rw [val_mul_apply, ih01, e10, mul_zero, add_zero, ih00, sigmaGL_iterate_apply,
        List.range_succ, List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]
    · rw [val_mul_apply, ih10, e01, zero_mul, zero_add, ih11, sigmaGL_iterate_apply,
        List.range_succ, List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]

theorem prod_iterate_mul (σ : L ≃ₐ[K] L) (n : ℕ) (a b : L ⊗[K] A) :
    ((List.range n).map fun i => (⇑(sigmaTensor K L A σ))^[i] (a * b)).prod =
      ((List.range n).map fun i => (⇑(sigmaTensor K L A σ))^[i] a).prod *
        ((List.range n).map fun i => (⇑(sigmaTensor K L A σ))^[i] b).prod := by
  rw [← List.prod_map_mul]
  congr 1
  exact List.map_congr_left fun i _ => sigmaTensor_iterate_mul K L A σ i a b

end sigma

section topology

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

theorem secondCountableTopology_GL (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [SecondCountableTopology B] : SecondCountableTopology (GL (Fin 2) B) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) B) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → B))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) B)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

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

end topology

section core

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
  [LocallyCompactSpace A] [SecondCountableTopology A]
  (σ : L ≃ₐ[K] L)

theorem core
    (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A)))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] A)) _ _ (glBorelOf (L ⊗[K] A)) μ)
    (wt : GL (Fin 2) (L ⊗[K] A) → ℝ)
    (hwt : ∀ t x : GL (Fin 2) (L ⊗[K] A),
      (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0 → (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0 →
        wt (t * x) = wt x)
    (δ₁ δ₂ s : GL (Fin 2) (L ⊗[K] A))
    (hs01 : (s : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0) (hs10 : (s : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0)
    (hδ : δ₂ = s⁻¹ * δ₁ * sigmaGL K L A σ s)
    (hT : ∀ t : GL (Fin 2) (L ⊗[K] A), t ∈ twistedCentralizer K L A σ δ₁ →
      (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0)
    (τ'₁ : Measure (twistedCentralizer K L A σ δ₁)) (τ'₂ : Measure (twistedCentralizer K L A σ δ₂))
    (c : ℝ) (hc : 0 < c)
    (hcpl : @Measure.map _ _ _ (glBorelOf (L ⊗[K] A)) (Subtype.val : twistedCentralizer K L A σ δ₂ → GL (Fin 2) (L ⊗[K] A)) τ'₂ =
      ENNReal.ofReal c • @Measure.map _ _ _ (glBorelOf (L ⊗[K] A)) (Subtype.val : twistedCentralizer K L A σ δ₁ → GL (Fin 2) (L ⊗[K] A)) τ'₁)
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (J'₂ : ℂ)
    (hJ'₂ : IsTwistedWeightedOrbitalIntegralOn K L A σ μ wt δ₂ τ'₂ φ J'₂) :
    IsTwistedWeightedOrbitalIntegralOn K L A σ μ wt δ₁ τ'₁ φ ((c : ℂ) * J'₂) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  haveI := AutomorphicForm.t2Space_tensor K L A
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L A
  haveI := secondCountableTopology_tensor K L A
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := glBorelOf (L ⊗[K] A)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A)) := borelSpace_glBorelOf (L ⊗[K] A)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  haveI := AutomorphicForm.t2Space_tensorGL K L A
  haveI := secondCountableTopology_GL (L ⊗[K] A)
  haveI : BorelSpace (twistedCentralizer K L A σ δ₁) := ⟨rfl⟩
  haveI : BorelSpace (twistedCentralizer K L A σ δ₂) := ⟨rfl⟩
  haveI := hμ
  set sG := sigmaGL K L A σ with hsG
  obtain ⟨w₂, ⟨hw0, hwm, hwc, hwint⟩, rfl⟩ := hJ'₂

  have hconj : ∀ x : GL (Fin 2) (L ⊗[K] A), (s * x)⁻¹ * δ₁ * sG (s * x) = x⁻¹ * δ₂ * sG x := by
    intro x
    rw [hδ, map_mul]
    group

  have hcomm : ∀ t : twistedCentralizer K L A σ δ₁,
      s⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) = (t : GL (Fin 2) (L ⊗[K] A)) * s⁻¹ := by
    intro t
    obtain ⟨ht01, ht10⟩ := hT t t.2
    have h := diag_mul_comm s (t : GL (Fin 2) (L ⊗[K] A)) hs01 hs10 ht01 ht10
    calc s⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) = s⁻¹ * ((t : GL (Fin 2) (L ⊗[K] A)) * s) * s⁻¹ := by group
      _ = s⁻¹ * (s * (t : GL (Fin 2) (L ⊗[K] A))) * s⁻¹ := by rw [h]
      _ = (t : GL (Fin 2) (L ⊗[K] A)) * s⁻¹ := by group

  set w₁ : GL (Fin 2) (L ⊗[K] A) → ℝ := fun y => c * w₂ (s⁻¹ * y) with hw₁
  have hmulc : Continuous fun y : GL (Fin 2) (L ⊗[K] A) => s⁻¹ * y := continuous_mul_left s⁻¹
  refine ⟨w₁, ⟨fun y => mul_nonneg hc.le (hw0 _), (hwm.comp hmulc.measurable).const_mul c, ?_, ?_⟩, ?_⟩
  ·
    have h1 : HasCompactSupport (w₂ ∘ Homeomorph.mulLeft s⁻¹) := hwc.comp_homeomorph _
    have h2 : w₁ = fun y => c * (w₂ ∘ Homeomorph.mulLeft s⁻¹) y := by
      funext y; simp [hw₁, Homeomorph.mulLeft]
    rw [h2]
    exact h1.mul_left
  ·
    intro x hx
    have hx' : φ ((s⁻¹ * x)⁻¹ * δ₂ * sG (s⁻¹ * x)) ≠ 0 := by
      rw [← hconj, mul_inv_cancel_left]; exact hx
    have h2 := hwint (s⁻¹ * x) hx'

    have hval₁ : Measurable (Subtype.val : twistedCentralizer K L A σ δ₁ → GL (Fin 2) (L ⊗[K] A)) :=
      continuous_subtype_val.measurable
    have hval₂ : Measurable (Subtype.val : twistedCentralizer K L A σ δ₂ → GL (Fin 2) (L ⊗[K] A)) :=
      continuous_subtype_val.measurable
    have hGm : Measurable fun g : GL (Fin 2) (L ⊗[K] A) => w₂ (g * (s⁻¹ * x)) :=
      hwm.comp (continuous_mul_right (s⁻¹ * x)).measurable
    have e2 : ∫ t : twistedCentralizer K L A σ δ₂, w₂ ((t : GL (Fin 2) (L ⊗[K] A)) * (s⁻¹ * x)) ∂τ'₂ =
        ∫ g, w₂ (g * (s⁻¹ * x)) ∂(Measure.map Subtype.val τ'₂) :=
      (integral_map hval₂.aemeasurable hGm.aestronglyMeasurable).symm
    have e1 : ∫ t : twistedCentralizer K L A σ δ₁, w₂ ((t : GL (Fin 2) (L ⊗[K] A)) * (s⁻¹ * x)) ∂τ'₁ =
        ∫ g, w₂ (g * (s⁻¹ * x)) ∂(Measure.map Subtype.val τ'₁) :=
      (integral_map hval₁.aemeasurable hGm.aestronglyMeasurable).symm
    rw [e2, hcpl, integral_smul_measure, ← e1, ENNReal.toReal_ofReal hc.le, smul_eq_mul] at h2

    have h3 : ∀ t : twistedCentralizer K L A σ δ₁,
        w₁ ((t : GL (Fin 2) (L ⊗[K] A)) * x) = c * w₂ ((t : GL (Fin 2) (L ⊗[K] A)) * (s⁻¹ * x)) := by
      intro t
      simp only [hw₁]
      rw [← mul_assoc, hcomm t, mul_assoc]
    simp_rw [h3]
    rw [integral_const_mul]
    exact h2
  ·
    have hL : ∀ y : GL (Fin 2) (L ⊗[K] A),
        φ (y⁻¹ * δ₁ * sG y) * (wt y : ℂ) * (w₁ y : ℂ) =
          (c : ℂ) * (fun x : GL (Fin 2) (L ⊗[K] A) => φ (x⁻¹ * δ₂ * sG x) * (wt x : ℂ) * (w₂ x : ℂ)) (s⁻¹ * y) := by
      intro y
      simp only [hw₁]
      have h1 : φ (y⁻¹ * δ₁ * sG y) = φ ((s⁻¹ * y)⁻¹ * δ₂ * sG (s⁻¹ * y)) := by
        rw [← hconj, mul_inv_cancel_left]
      have h2 : wt y = wt (s⁻¹ * y) := by
        conv_lhs => rw [show y = s * (s⁻¹ * y) from (mul_inv_cancel_left s y).symm]
        exact hwt s _ hs01 hs10
      rw [h1, h2]
      push_cast
      ring
    show (c : ℂ) * ∫ x, φ (x⁻¹ * δ₂ * sG x) * (wt x : ℂ) * (w₂ x : ℂ) ∂μ =
      ∫ y, φ (y⁻¹ * δ₁ * sG y) * (wt y : ℂ) * (w₁ y : ℂ) ∂μ
    simp_rw [hL]
    rw [integral_const_mul]
    congr 1
    exact (integral_mul_left_eq_self (fun x : GL (Fin 2) (L ⊗[K] A) => φ (x⁻¹ * δ₂ * sG x) * (wt x : ℂ) * (w₂ x : ℂ)) s⁻¹).symm

end core

section arch

variable (K : Type) [Field K] [NumberField K]

open IsDedekindDomain Topology in
theorem secondCountableTopology_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI : SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology K
  exact (isInducing_prodMkLeft (0 : FiniteAdeleRing (𝓞 K) K) :
    IsInducing fun x : InfiniteAdeleRing K => (x, (0 : FiniteAdeleRing (𝓞 K) K))).secondCountableTopology

end arch

end C3f25

open C3f25 in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (γ : GL (Fin 2) (InfiniteAdeleRing K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (hγ₀₁ : (γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 1 = 0)
    (hγ₁₀ : (γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0 = 0)
    (ν' : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)))
    (hν' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)) ν')
    (wt : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ) (hwtc : Continuous wt)
    (hwt : ∀ t x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
      (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 1 = 0 → (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 1 0 = 0 →
        wt (t * x) = wt x)
    (τ : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))) [τ.IsHaarMeasure]
    (c : ℝ) (hc : 0 < c)
    (δ₁ δ₂ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hδ₁ : AutomorphicForm.normString K L (InfiniteAdeleRing K) σ δ₁ =
      AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) γ)
    (hδ₂ : AutomorphicForm.normString K L (InfiniteAdeleRing K) σ δ₂ =
      AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) γ)
    (τ'₁ : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ₁)) (hτ'₁ : τ'₁.IsHaarMeasure)
    (hc₁ : AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ γ δ₁ 1 τ τ'₁)
    (τ'₂ : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ₂)) (hτ'₂ : τ'₂.IsHaarMeasure)
    (hc₂ : AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ γ δ₂ 1 (ENNReal.ofReal c • τ) τ'₂)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : AutomorphicForm.IsArchTestFactor L φa)
    (J'₁ J'₂ : ℂ)
    (hJ'₁ : AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ ν' wt δ₁ τ'₁
      (φa ∘ AutomorphicForm.archIdentGL K L) J'₁)
    (hJ'₂ : AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ ν' wt δ₂ τ'₂
      (φa ∘ AutomorphicForm.archIdentGL K L) J'₂) :
    J'₂ = (c : ℂ)⁻¹ * J'₁ := by
  classical
  haveI : SecondCountableTopology (InfiniteAdeleRing K) := C3f25.secondCountableTopology_infiniteAdeleRing K
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  haveI := AutomorphicForm.t2Space_tensor K L (InfiniteAdeleRing K)
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L (InfiniteAdeleRing K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (InfiniteAdeleRing K)
  haveI := AutomorphicForm.t2Space_tensorGL K L (InfiniteAdeleRing K)
  have hσ : σ ^ Module.finrank K L = 1 := pow_finrank_eq_one K L σ

  set γ' : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) := AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) γ with hγ'
  have hγ'01 : (γ' : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 1 = 0 := by
    rw [hγ', toTensorGL_apply, hγ₀₁, map_zero]
  have hγ'10 : (γ' : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 1 0 = 0 := by
    rw [hγ', toTensorGL_apply, hγ₁₀, map_zero]
  have hu : IsUnit ((γ' : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 0 -
      (γ' : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 1 1) := by
    rw [hγ', toTensorGL_apply, toTensorGL_apply, ← map_sub]
    exact (isUnit_sub_of_isRegularSemisimple γ hγ₀₁ hγ₁₀ hγ).map _
  have hreg' : AutomorphicForm.IsRegularSemisimple γ' := isRegularSemisimple_of_isUnit_sub γ' hγ'01 hγ'10 hu
  have hσγ' : AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ γ' = γ' := by
    rw [hγ']; exact sigmaGL_toTensorGL K L (InfiniteAdeleRing K) σ γ

  have hdiag : ∀ δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
      AutomorphicForm.normString K L (InfiniteAdeleRing K) σ δ = γ' →
      (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 1 = 0 ∧
      (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 1 0 = 0 := by
    intro δ hδ
    have hc : δ * AutomorphicForm.normString K L (InfiniteAdeleRing K) σ δ =
        AutomorphicForm.normString K L (InfiniteAdeleRing K) σ δ * δ :=
      mul_normString_comm K L (InfiniteAdeleRing K) σ δ (by rw [hδ, hσγ'])
    rw [hδ] at hc
    exact offdiag_eq_zero_of_commute γ' δ hγ'01 hγ'10 hu hc.symm
  obtain ⟨h1_01, h1_10⟩ := hdiag δ₁ hδ₁
  obtain ⟨h2_01, h2_10⟩ := hdiag δ₂ hδ₂

  have hT : ∀ t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
      t ∈ AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ₁ →
      (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 1 = 0 ∧
      (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 1 0 = 0 := by
    intro t ht
    have hc := mul_normString_comm_of_mem_twistedCentralizer K L (InfiniteAdeleRing K) σ δ₁ t ht
    rw [hδ₁] at hc
    exact offdiag_eq_zero_of_commute γ' t hγ'01 hγ'10 hu hc

  set Nm : L ⊗[K] InfiniteAdeleRing K → L ⊗[K] InfiniteAdeleRing K := fun a =>
    ((List.range (Module.finrank K L)).map fun i =>
      (⇑(AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ))^[i] a).prod with hNm
  have hNmul : ∀ p q, Nm (p * q) = Nm p * Nm q := fun p q => by
    simp only [hNm]; exact prod_iterate_mul K L (InfiniteAdeleRing K) σ _ p q
  have hN : ∀ δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
      AutomorphicForm.normString K L (InfiniteAdeleRing K) σ δ = γ' →
      (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 1 = 0 →
      (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 1 0 = 0 →
      Nm ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 0) =
        (γ' : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 0 ∧
      Nm ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 1 1) =
        (γ' : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 1 1 := by
    intro δ hδ h01 h10
    obtain ⟨-, -, h00, h11⟩ := P_diag K L (InfiniteAdeleRing K) σ δ h01 h10 (Module.finrank K L)
    rw [← normString_eq_P, hδ] at h00 h11
    exact ⟨h00.symm, h11.symm⟩
  obtain ⟨hN1_0, hN1_1⟩ := hN δ₁ hδ₁ h1_01 h1_10
  obtain ⟨hN2_0, hN2_1⟩ := hN δ₂ hδ₂ h2_01 h2_10
  obtain ⟨hu1_0, hu1_1⟩ := isUnit_diag_entries δ₁ h1_01 h1_10
  obtain ⟨hγu0, hγu1⟩ := isUnit_diag_entries γ' hγ'01 hγ'10

  have key : ∀ (a b g : L ⊗[K] InfiniteAdeleRing K) (ha : IsUnit a), IsUnit g → Nm a = g → Nm b = g →
      Nm (b * ((ha.unit⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K)) = 1 := by
    intro a b g ha hg hNa hNb
    have h1 : Nm (b * ((ha.unit⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K)) * g = g := by
      rw [← hNa, ← hNmul, mul_assoc, ha.val_inv_mul, mul_one, hNb, hNa]
    exact hg.mul_right_cancel (h1.trans (one_mul g).symm)
  obtain ⟨y₀, hy₀⟩ :=
    AutomorphicForm.exists_units_eq_sigmaTensor_mul_inv_of_prod_iterate_sigmaTensor_eq_one_infiniteAdeleRing K L σ hgen
      ((δ₂ : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 0 *
        ((hu1_0.unit⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K))
      (key _ _ _ hu1_0 hγu0 hN1_0 hN2_0)
  obtain ⟨y₁, hy₁⟩ :=
    AutomorphicForm.exists_units_eq_sigmaTensor_mul_inv_of_prod_iterate_sigmaTensor_eq_one_infiniteAdeleRing K L σ hgen
      ((δ₂ : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 1 1 *
        ((hu1_1.unit⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K))
      (key _ _ _ hu1_1 hγu1 hN1_1 hN2_1)

  set s : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) := LanglandsTunnell.CubicInduction.diagUnits2 y₀ y₁ with hs
  have hs01 : (s : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 1 = 0 := by
    rw [hs, LanglandsTunnell.CubicInduction.coe_diagUnits2]; rfl
  have hs10 : (s : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 1 0 = 0 := by
    rw [hs, LanglandsTunnell.CubicInduction.coe_diagUnits2]; rfl
  have hs00 : (s : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 0 = (y₀ : L ⊗[K] InfiniteAdeleRing K) := by
    rw [hs, LanglandsTunnell.CubicInduction.coe_diagUnits2]; rfl
  have hs11 : (s : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 1 1 = (y₁ : L ⊗[K] InfiniteAdeleRing K) := by
    rw [hs, LanglandsTunnell.CubicInduction.coe_diagUnits2]; rfl
  have hsi01 : ((s⁻¹ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 1 = 0 := by
    rw [hs, coe_diagUnits2_inv]; rfl
  have hsi10 : ((s⁻¹ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 1 0 = 0 := by
    rw [hs, coe_diagUnits2_inv]; rfl
  have hsi00 : ((s⁻¹ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 0 =
      ((y₀⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K) := by
    rw [hs, coe_diagUnits2_inv]; rfl
  have hsi11 : ((s⁻¹ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 1 1 =
      ((y₁⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K) := by
    rw [hs, coe_diagUnits2_inv]; rfl

  have hent : ∀ (a b : L ⊗[K] InfiniteAdeleRing K) (ha : IsUnit a) (y : (L ⊗[K] InfiniteAdeleRing K)ˣ),
      b * ((ha.unit⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K) =
        AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (y : L ⊗[K] InfiniteAdeleRing K) * ↑y⁻¹ →
      b = ((y⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K) * a *
        AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (y : L ⊗[K] InfiniteAdeleRing K) := by
    intro a b ha y h
    calc b = b * ((ha.unit⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K) * a := by
          rw [mul_assoc, ha.val_inv_mul, mul_one]
      _ = AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (y : L ⊗[K] InfiniteAdeleRing K) * ↑y⁻¹ * a := by rw [h]
      _ = _ := by ring
  have he0 := hent _ _ hu1_0 y₀ hy₀
  have he1 := hent _ _ hu1_1 y₁ hy₁
  have hδs : δ₂ = s⁻¹ * δ₁ * AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ s := by
    apply Units.ext
    ext i j
    simp only [val_mul_apply, sigmaGL_apply]
    fin_cases i <;> fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, hsi01, hsi00, h1_01, h1_10, hs01, hs10, hs00, map_zero,
        mul_zero, zero_mul, add_zero]
      exact he0
    · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, hsi01, hsi00, h1_01, h1_10, hs01, hs11, map_zero,
        mul_zero, zero_mul, add_zero, zero_add]
      exact h2_01
    · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, hsi10, hsi11, h1_01, h1_10, hs10, hs00, map_zero,
        mul_zero, zero_mul, add_zero, zero_add]
      exact h2_10
    · simp only [Fin.mk_one, Fin.isValue, hsi10, hsi11, h1_01, h1_10, hs01, hs10, hs11, map_zero,
        mul_zero, zero_mul, add_zero, zero_add]
      exact he1

  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := AutomorphicForm.borelSpace_glBorelOf _
  have hcpl : Measure.map (Subtype.val : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ₂ → _) τ'₂ =
      ENNReal.ofReal c • Measure.map (Subtype.val : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ₁ → _) τ'₁ := by
    have e2 : (fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ₂ =>
        (1 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))⁻¹ * (t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) * 1) = Subtype.val := by
      funext t; simp
    have e1 : (fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ₁ =>
        (1 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))⁻¹ * (t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) * 1) = Subtype.val := by
      funext t; simp
    have h1 : Measure.map (fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ₁ =>
        (1 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))⁻¹ * (t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) * 1) τ'₁ =
        Measure.map (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
          AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (t : GL (Fin 2) (InfiniteAdeleRing K))) τ := hc₁
    have h2 : Measure.map (fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ₂ =>
        (1 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))⁻¹ * (t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) * 1) τ'₂ =
        Measure.map (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
          AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (t : GL (Fin 2) (InfiniteAdeleRing K)))
          (ENNReal.ofReal c • τ) := hc₂
    rw [e1] at h1
    rw [e2] at h2
    rw [h1, h2, Measure.map_smul]

  obtain ⟨⟨Φ, hΦ, hφaΦ⟩, hφacs⟩ := hφa
  have hcontE : Continuous (AutomorphicForm.archEntries L) :=
    continuous_pi fun i => continuous_pi fun j =>
      (NumberField.AdelicBox.continuous_ringEquiv_mixedSpace L).comp (Units.continuous_val.matrix_elem i j)
  have hφac : Continuous φa := by
    rw [show φa = Φ ∘ AutomorphicForm.archEntries L from funext hφaΦ]
    exact hΦ.continuous.comp hcontE
  have hAc : Continuous (AutomorphicForm.archIdentGL K L) := map_continuous (AutomorphicForm.archIdentGLEquiv K L)
  have hφm : Measurable (φa ∘ AutomorphicForm.archIdentGL K L) := (hφac.comp hAc).measurable
  have hφb : ∃ C : ℝ, ∀ g, ‖(φa ∘ AutomorphicForm.archIdentGL K L) g‖ ≤ C := by
    obtain ⟨C, hC⟩ := hφac.bounded_above_of_compact_support hφacs
    exact ⟨C, fun g => hC _⟩

  have hval : AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ ν' wt δ₁ τ'₁
      (φa ∘ AutomorphicForm.archIdentGL K L) ((c : ℂ) * J'₂) :=
    core K L (InfiniteAdeleRing K) σ ν' hν' wt hwt δ₁ δ₂ s hs01 hs10 hδs hT τ'₁ τ'₂ c hc hcpl _ J'₂ hJ'₂

  have hregN : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (InfiniteAdeleRing K) σ δ₁) := by
    rw [hδ₁]; exact hreg'
  have hwt' : ∀ t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ₁,
      ∀ x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
        wt ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) * x) = wt x := by
    intro t x
    obtain ⟨a, b⟩ := hT t t.2
    exact hwt _ x a b
  have huniq :=
    AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString_of_forall_twistedCentralizer_mul_eq
      K L (InfiniteAdeleRing K) σ hσ ν' hν' δ₁ hregN τ'₁ hτ'₁ wt hwtc hwt' (φa ∘ AutomorphicForm.archIdentGL K L)
      hφm hφb hJ'₁ hval
  rw [huniq, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hc.ne'), one_mul]

end
end S_AutomorphicForm_eq_inv_mul_of_isTwistedWeightedOrbitalIntegralOn_of_normString_eq_toTensorGL_diagonal_of_coupled_one_smul_infiniteAdeleRing
end P2MW
export P2MW.S_AutomorphicForm_eq_inv_mul_of_isTwistedWeightedOrbitalIntegralOn_of_normString_eq_toTensorGL_diagonal_of_coupled_one_smul_infiniteAdeleRing (solution)
