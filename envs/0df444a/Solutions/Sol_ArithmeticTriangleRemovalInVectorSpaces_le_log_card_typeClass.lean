-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.le_log_card_typeClass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:28.249497+00:00
-- url     : https://prove2.me/submissions/871bdc47-2004-4c48-8214-dbf3c4d4b8f1

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Perm
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_LogSumSupport
public import Mathlib.GroupTheory.Perm.DomMulAct
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_TypeClass
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_typeClass_nonempty
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_sum_card_filter_eq
public import Theorems.Thm_Real_le_sum_log_nat
public import Theorems.Thm_Real_sum_log_eq_log_factorial
public import Theorems.Thm_Real_sum_log_le

attribute [local simp] ArithmeticTriangleRemovalInVectorSpaces.typeClass_nonempty
section
public section
open Finset Real
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {n N : ℕ} {a b b' : Fin n → ℕ}
private lemma card_filter_comp_eq_comp (a : Fin n → ℕ) (τ : Equiv.Perm (Fin n)) :
    #{σ : Equiv.Perm (Fin n) | a ∘ σ = a ∘ τ} =
      Fintype.card {σ : Equiv.Perm (Fin n) // a ∘ σ = a} := by
  rw [← Fintype.card_subtype]
  refine Fintype.card_congr ((Equiv.mulRight τ⁻¹).subtypeEquiv ?_)
  intro σ
  simp [Equiv.Perm.coe_mul, ← Function.comp_assoc, Equiv.Perm.inv_def, Equiv.comp_symm_eq]
private lemma card_typeClass_mul_prod_factorial (a : Fin n → ℕ) (ha : ∀ r, a r ≤ N) :
    #(typeClass a) * ∏ k ∈ range (N + 1), (#{r | a r = k}).factorial = n.factorial := by
  have hprod : ∏ k ∈ range (N + 1), (#{r | a r = k}).factorial =
      ∏ k ∈ univ.image a, (Fintype.card {r // a r = k}).factorial := by
    simp_rw [Fintype.card_subtype]
    refine (prod_subset ?_ ?_).symm
    · intro k
      simp only [mem_image, mem_univ, true_and, mem_range]
      grind
    · intro k _ hk
      simp_all
  rw [hprod, ← DomMulAct.stabilizer_card',
    (by simp [Fintype.card_perm] : n.factorial = #(univ : Finset (Equiv.Perm (Fin n)))),
    card_eq_sum_card_image fun σ : Equiv.Perm (Fin n) ↦ a ∘ σ, typeClass, sum_const_nat]
  simp only [mem_image, mem_univ, true_and]
  rintro _ ⟨τ, rfl⟩
  exact card_filter_comp_eq_comp a τ
private lemma log_card_typeClass (a : Fin n → ℕ) (ha : ∀ r, a r ≤ N) :
    log #(typeClass a) =
      log n.factorial - ∑ k ∈ range (N + 1), log (#{r | a r = k}).factorial := by
  rw [eq_sub_iff_add_eq, ← log_prod fun k _ ↦ by positivity,
    ← log_mul (by simpa using (typeClass_nonempty a).ne_empty) (by positivity),
    ← card_typeClass_mul_prod_factorial a ha]
  push_cast
  rfl
private lemma mul_log_div_sub_le {D : ℕ} (hD : D ≤ n) :
    D * log (n / D) - (1 + log (n + 1)) ≤ D * log n - D - log D.factorial := by
  rcases D.eq_zero_or_pos with rfl | hD₀
  · simpa using (by linarith [log_nonneg (by simp : (1 : ℝ) ≤ n + 1)] : -log (n + 1 : ℝ) ≤ 1)
  have h := sum_log_le (x := D) (by exact_mod_cast hD₀)
  rw [Nat.floor_natCast, sum_log_eq_log_factorial] at h
  rw [log_div (by norm_cast; grind) (by positivity)]
  linarith [log_le_log (by positivity) (by norm_cast; grind : (D : ℝ) ≤ n + 1)]
private lemma sum_mul_log_div_sub_le_log {s : Finset ℕ} (D : ℕ → ℕ) (hD : ∑ k ∈ s, D k = n) :
    ∑ k ∈ s, D k * log (n / D k) - #s * (1 + log (n + 1)) ≤
      log n.factorial - ∑ k ∈ s, log (D k).factorial := by
  have h : ∑ k ∈ s, (D k * log (n / D k) - (1 + log (n + 1))) ≤
      ∑ k ∈ s, (D k * log n - D k - log (D k).factorial) := by
    apply sum_le_sum
    intro k hk
    exact mul_log_div_sub_le (hD ▸ single_le_sum (by simp) hk)
  simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, ← sum_mul,
    (by exact_mod_cast hD : ∑ k ∈ s, (D k : ℝ) = n)] at h
  linarith [le_sum_log_nat n, sum_log_eq_log_factorial n]
private lemma mul_log_inv_sub_sq_div_sub_le {D x ψ : ℝ} (hD : 0 ≤ D) (hDx : D ≤ x) (hψ : 0 < ψ) :
    D * log ψ⁻¹ - (D - x * ψ) ^ 2 / (x * ψ) - (D - x * ψ) ≤ D * log (x / D) := by
  rcases hD.eq_or_lt with rfl | hD
  · simp [sq]
  have hx : 0 < x := hD.trans_le hDx
  have hxψ : 0 < x * ψ := by positivity
  have hlog := one_sub_inv_le_log_of_pos (div_pos hxψ hD)
  rw [inv_div, log_div hxψ.ne' hD.ne', log_mul (by positivity) hψ.ne'] at hlog
  rw [log_div (by positivity) hD.ne', log_inv]
  have hid : D * (1 - D / (x * ψ)) = -((D - x * ψ) ^ 2 / (x * ψ)) - (D - x * ψ) := by
    field_simp
    ring
  linarith [mul_le_mul_of_nonneg_left hlog hD.le]
private lemma sum_mul_log_inv_sub_le {s : Finset ℕ} (D : ℕ → ℕ) (hD : ∑ k ∈ s, D k = n) {ψ : ℕ → ℝ}
    (hψ : ∀ k ∈ s, 0 < ψ k) (hψ₁ : ∑ k ∈ s, ψ k = 1) :
    ∑ k ∈ s, D k * log (ψ k)⁻¹ - ∑ k ∈ s, (D k - n * ψ k) ^ 2 / (n * ψ k) ≤
      ∑ k ∈ s, D k * log (n / D k) := by
  have hY : ∑ k ∈ s, ((D k : ℝ) - n * ψ k) = 0 := by
    rw [sum_sub_distrib, ← mul_sum, hψ₁, mul_one, sub_eq_zero]
    exact_mod_cast hD
  have h : ∑ k ∈ s, (D k * log (ψ k)⁻¹ - (D k - n * ψ k) ^ 2 / (n * ψ k) - (D k - n * ψ k)) ≤
      ∑ k ∈ s, D k * log (n / D k) := by
    apply sum_le_sum
    intro k hk
    exact mul_log_inv_sub_sq_div_sub_le (by positivity)
      (by exact_mod_cast hD ▸ single_le_sum (by simp) hk) (hψ k hk)
  rwa [sum_sub_distrib, hY, sub_zero, sum_sub_distrib] at h
end ArithmeticTriangleRemovalInVectorSpaces
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset Real
open ArithmeticTriangleRemovalInVectorSpaces
variable {n N : ℕ} {a b b' : Fin n → ℕ}
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution (a : Fin n → ℕ) (ha : ∀ r, a r ≤ N) {ψ : ℕ → ℝ}
    (hψ : ∀ k ∈ range (N + 1), 0 < ψ k) (hψ₁ : ∑ k ∈ range (N + 1), ψ k = 1) :
    ∑ k ∈ range (N + 1), #{r | a r = k} * log (ψ k)⁻¹ -
        ∑ k ∈ range (N + 1), (#{r | a r = k} - n * ψ k) ^ 2 / (n * ψ k) -
        (N + 1) * (1 + log (n + 1)) ≤ log #(typeClass a) := by
  have h := sum_mul_log_div_sub_le_log _ (sum_card_filter_eq ha)
  rw [card_range, Nat.cast_add_one] at h
  rw [log_card_typeClass a ha]
  linarith [sum_mul_log_inv_sub_le _ (sum_card_filter_eq ha) hψ hψ₁]
end ArithmeticTriangleRemovalInVectorSpaces
