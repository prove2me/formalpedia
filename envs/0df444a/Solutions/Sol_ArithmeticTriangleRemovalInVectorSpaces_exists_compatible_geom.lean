-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.exists_compatible_geom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:17:17.63881+00:00
-- url     : https://prove2.me/submissions/3293af98-7a2f-4841-a07f-f0b3f516230e

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Decomposition
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Decreasing
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsBalanced_compatible_hat
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsDecreasingOn_eq_hat
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsDecreasingOn_weight_eq_zero
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsDecreasingOn_weight_nonneg
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mass_hat
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mem_sumTriples
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_moment_hat
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_sum_range_succ_cast
attribute [local simp] ArithmeticTriangleRemovalInVectorSpaces.mem_sumTriples


section
public section
open Finset
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {N : ℕ} {π π₁ π₂ π₃ : ℕ → ℝ}
private lemma IsDecreasingOn.isWeight (h : IsDecreasingOn N π) :
    IsWeight N fun k ↦ (k + 1) * (π k - π (k + 1)) :=
  ⟨h.weight_nonneg, fun _ hk ↦ h.weight_eq_zero hk⟩
private lemma IsDecreasingOn.mass_eq (h : IsDecreasingOn N π) :
    mass N π = mass N fun k ↦ (k + 1) * (π k - π (k + 1)) := by
  nth_rw 1 [h.eq_hat]
  exact mass_hat _
private lemma IsDecreasingOn.moment_eq (h : IsDecreasingOn N π) :
    moment N π = moment N (fun k ↦ (k + 1) * (π k - π (k + 1))) / 2 := by
  nth_rw 1 [h.eq_hat]
  exact moment_hat _
private lemma decreasingCompatible (N : ℕ) : DecreasingCompatible N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro π₁ π₂ π₃ h₁ h₂ h₃ hm₂ hm₃ hmom
  rw [h₁.eq_hat, h₂.eq_hat, h₃.eq_hat]
  refine IsBalanced.compatible_hat ih ⟨h₁.isWeight, h₂.isWeight, h₃.isWeight, ?_, ?_, ?_⟩
  · rw [← h₁.mass_eq, ← h₂.mass_eq, hm₂]
  · rw [← h₁.mass_eq, ← h₃.mass_eq, hm₃]
  · rw [← h₁.mass_eq]
    linarith [h₁.moment_eq, h₂.moment_eq, h₃.moment_eq]
private lemma compatible_of_isDecreasingOn (h₁ : IsDecreasingOn N π₁) (h₂ : IsDecreasingOn N π₂)
    (h₃ : IsDecreasingOn N π₃) (hm₂ : mass N π₂ = mass N π₁) (hm₃ : mass N π₃ = mass N π₁)
    (hmom : moment N π₁ + moment N π₂ + moment N π₃ = N * mass N π₁) :
    Compatible N π₁ π₂ π₃ :=
  decreasingCompatible N π₁ π₂ π₃ h₁ h₂ h₃ hm₂ hm₃ hmom
private lemma mass_geom (ρ : ℝ) : mass N (geom N ρ) = ∑ k ∈ range (N + 1), ρ ^ k := by
  rw [mass]
  congr! 1 with k hk
  simp [geom, Nat.le_of_lt_succ (mem_range.1 hk)]
private lemma moment_geom (ρ : ℝ) : moment N (geom N ρ) = ∑ k ∈ range (N + 1), k * ρ ^ k := by
  rw [moment]
  congr! 1 with k hk
  simp [geom, Nat.le_of_lt_succ (mem_range.1 hk)]
private lemma isDecreasingOn_geom {ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) :
    IsDecreasingOn N (geom N ρ) := by
  refine ⟨?_, ?_, by simp [geom]⟩
  · intro k
    unfold geom
    positivity
  · intro a b hab
    unfold geom
    grind [pow_le_pow_of_le_one, pow_nonneg]
private lemma sum_mul_half_pow (N M : ℕ) :
    ∑ k ∈ range (M + 1), (3 * k - N : ℝ) * (1 / 2) ^ k = 6 - 2 * N - (3 * M + 6 - N) / 2 ^ M := by
  induction M with
  | zero =>
    norm_num
    ring
  | succ M ih =>
    rw [sum_range_succ, ih, one_div_pow]
    push_cast
    field_simp
    ring
private lemma sum_mul_half_pow_nonpos (hN : 0 < N) :
    ∑ k ∈ range (N + 1), (3 * k - N : ℝ) * (1 / 2) ^ k ≤ 0 := by
  rw [sum_mul_half_pow]
  obtain rfl | rfl | hN := (by grind : N = 1 ∨ N = 2 ∨ 3 ≤ N)
  · norm_num
  · norm_num
  · have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith [div_nonneg (by linarith : (0 : ℝ) ≤ 3 * N + 6 - N) (by positivity : (0 : ℝ) ≤ 2 ^ N)]
private lemma exists_sum_mul_pow_eq_zero (hN : 0 < N) :
    ∃ ρ : ℝ, 1 / 2 ≤ ρ ∧ ρ < 1 ∧ ∑ k ∈ range (N + 1), (3 * k - N) * ρ ^ k = 0 := by
  set f : ℝ → ℝ := fun ρ ↦ ∑ k ∈ range (N + 1), (3 * k - N) * ρ ^ k
  have hf₁ : f 1 = N * (N + 1) / 2 := by
    simp only [f, one_pow, mul_one, sum_sub_distrib, ← mul_sum, sum_const, card_range,
      nsmul_eq_mul, sum_range_succ_cast]
    push_cast
    ring
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨ρ, ⟨hρ₀, hρ₁⟩, hρ⟩ := intermediate_value_Icc (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (by fun_prop : Continuous f).continuousOn
    (⟨sum_mul_half_pow_nonpos hN, by nlinarith⟩ : (0 : ℝ) ∈ Set.Icc (f (1 / 2)) (f 1))
  refine ⟨ρ, hρ₀, lt_of_le_of_ne hρ₁ ?_, hρ⟩
  rintro rfl
  nlinarith
end ArithmeticTriangleRemovalInVectorSpaces
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ArithmeticTriangleRemovalInVectorSpaces
variable {N : ℕ} {π π₁ π₂ π₃ : ℕ → ℝ}
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution (hN : 0 < N) :
    ∃ ρ : ℝ, 1 / 2 ≤ ρ ∧ ρ < 1 ∧
      3 * ∑ k ∈ range (N + 1), k * ρ ^ k = N * ∑ k ∈ range (N + 1), ρ ^ k ∧
      Compatible N (geom N ρ) (geom N ρ) (geom N ρ) := by
  obtain ⟨ρ, hρ₀, hρ₁, hρ⟩ := exists_sum_mul_pow_eq_zero hN
  have hmean : 3 * ∑ k ∈ range (N + 1), k * ρ ^ k = N * ∑ k ∈ range (N + 1), ρ ^ k := by
    simp only [sub_mul, sum_sub_distrib, mul_assoc, ← mul_sum] at hρ
    linarith
  have hd := isDecreasingOn_geom (N := N) (by linarith) hρ₁.le
  refine ⟨ρ, hρ₀, hρ₁, hmean, compatible_of_isDecreasingOn hd hd hd rfl rfl ?_⟩
  rw [moment_geom, mass_geom]
  linarith
end ArithmeticTriangleRemovalInVectorSpaces
