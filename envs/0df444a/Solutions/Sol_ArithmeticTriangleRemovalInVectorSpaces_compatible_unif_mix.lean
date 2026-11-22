-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.compatible_unif_mix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:48.595833+00:00
-- url     : https://prove2.me/submissions/25b5da9b-4fc9-4332-ad5c-a4d89435a1d0

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Peeling
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Uniform
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsDecreasingOn_add
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsDecreasingOn_smul
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_sum_range_succ_cast
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_Compatible_add
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_Compatible_shift
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_Compatible_smul
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsDecreasingOn_shift
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_compatible_layer
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_compatible_of_eq_zero_of_eq_zero
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mass_add
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mass_smul
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mem_sumTriples
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_moment_add
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_moment_smul
public import Theorems.Thm_P2M_ArithmeticTriangleRemovalInVectorSpaces_Compatible_comm___20106223d85b
public import Theorems.Thm_P2M_ArithmeticTriangleRemovalInVectorSpaces_Compatible_comm___bf003541382f
public import Theorems.Thm_P2M_ArithmeticTriangleRemovalInVectorSpaces_Compatible_comm___c955cfa1f590
attribute [local simp] ArithmeticTriangleRemovalInVectorSpaces.mem_sumTriples


section
public section
open Finset
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {N k : ℕ} {π π' π₁ π₂ π₃ : ℕ → ℝ}
private lemma isDecreasingOn_unif (hk : k ≤ N) : IsDecreasingOn N (unif k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    unfold unif
    positivity
  · intro a b hab
    unfold unif
    grind [(by positivity : (0 : ℝ) ≤ ((k : ℝ) + 1)⁻¹)]
  · simp only [unif, ite_eq_right_iff]
    grind
private lemma unif_eq_zero (hk : k < N) : unif k N = 0 := by
  simp only [unif, ite_eq_right_iff]
  grind
private lemma sum_mul_unif (hk : k ≤ N) (f : ℕ → ℝ) :
    ∑ j ∈ range (N + 1), f j * unif k j = (∑ j ∈ range (k + 1), f j) / (k + 1) := by
  rw [← sum_range_add_sum_Ico _ (by grind : k + 1 ≤ N + 1), sum_eq_zero (s := Ico _ _),
    add_zero, div_eq_mul_inv, sum_mul]
  · rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
    congr with j
    simp [unif, j.is_le]
  · intro j hj
    simp only [mem_Ico] at hj
    simp [unif, (by grind : ¬j ≤ k)]
private lemma mass_unif (hk : k ≤ N) : mass N (unif k) = 1 := by
  have h := sum_mul_unif hk fun _ ↦ 1
  simp only [one_mul, sum_const, card_range, nsmul_eq_mul, mul_one] at h
  rw [mass, h]
  push_cast
  field_simp
private lemma moment_unif (hk : k ≤ N) : moment N (unif k) = k / 2 := by
  rw [moment, sum_mul_unif hk, sum_range_succ_cast]
  field_simp
private lemma isDecreasingOn_mix {y z : ℕ} (hy : y ≤ N) (hz : z ≤ N) {α : ℝ} (hα₀ : 0 ≤ α)
    (hα₁ : α ≤ 1) : IsDecreasingOn N (α • unif y + (1 - α) • unif z) :=
  ((isDecreasingOn_unif hy).smul hα₀).add ((isDecreasingOn_unif hz).smul (by linarith))
private lemma mass_mix {y z : ℕ} (hy : y ≤ N) (hz : z ≤ N) (α : ℝ) :
    mass N (α • unif y + (1 - α) • unif z) = 1 := by
  rw [mass_add, mass_smul, mass_smul, mass_unif hy, mass_unif hz]
  ring
private lemma moment_mix {y z : ℕ} (hy : y ≤ N) (hz : z ≤ N) (α : ℝ) :
    moment N (α • unif y + (1 - α) • unif z) = (α * y + (1 - α) * z) / 2 := by
  rw [moment_add, moment_smul, moment_smul, moment_unif hy, moment_unif hz]
  ring
private lemma mix_eq_zero {y z : ℕ} {α : ℝ} (hy : y < N ∨ α = 0) (hz : z < N ∨ α = 1) :
    (α • unif y + (1 - α) • unif z) N = 0 := by
  rcases hy with hy | rfl <;> rcases hz with hz | hz <;> simp_all [unif_eq_zero]
private lemma mix_eq_unif_zero {y z : ℕ} {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (h : α * y + (1 - α) * z = 0) : α • unif y + (1 - α) • unif z = unif 0 := by
  obtain ⟨hy, hz⟩ := (add_eq_zero_iff_of_nonneg (by positivity)
    (mul_nonneg (sub_nonneg.2 hα₁) z.cast_nonneg)).1 h
  rcases mul_eq_zero.1 hy with rfl | hy <;> rcases mul_eq_zero.1 hz with hz | hz
  · norm_num at hz
  · simp_all
  · rw [(by linarith : α = 1)]
    simp_all
  · simp_all [← add_smul]
private lemma compatible_unif_zero : Compatible N (unif 0) (unif N) (unif N) := by
  convert compatible_layer (N := N) (f := fun _ ↦ ((N : ℝ) + 1)⁻¹) (fun _ ↦ by positivity)
    using 1
  · ext a
    simp only [unif, nonpos_iff_eq_zero, CharP.cast_eq_zero, zero_add, inv_one, sum_const,
      card_range, nsmul_eq_mul]
    push_cast
    grind
  · ext b
    rfl
  · ext c
    rfl
private lemma compatible_unif_triple {a b : ℕ} (h : DecreasingCompatible (a + b)) :
    Compatible (a + b) (unif a) (unif b) (unif (a + b)) := by
  refine h _ _ _ (isDecreasingOn_unif (by grind)) (isDecreasingOn_unif (by grind))
    (isDecreasingOn_unif le_rfl) ?_ ?_ ?_
  · rw [mass_unif (by grind), mass_unif (by grind)]
  · rw [mass_unif le_rfl, mass_unif (by grind)]
  · rw [moment_unif (by grind), moment_unif (by grind), moment_unif le_rfl, mass_unif (by grind)]
    push_cast
    ring
private lemma compatible_of_eq_zero_of_eq_zero_of_mass_eq_one (ih : ∀ m < N, DecreasingCompatible m)
    (hN : N ≠ 0) (h₁ : IsDecreasingOn N π₁) (h₂ : IsDecreasingOn N π₂) (h₃ : IsDecreasingOn N π₃)
    (h₂N : π₂ N = 0) (h₃N : π₃ N = 0) (hm₁ : mass N π₁ = 1) (hm₂ : mass N π₂ = 1)
    (hm₃ : mass N π₃ = 1) (hmom : moment N π₁ + moment N π₂ + moment N π₃ = N) :
    Compatible N π₁ π₂ π₃ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
  refine compatible_of_eq_zero_of_eq_zero (ih n (by grind)) h₁ h₂ h₃ h₂N h₃N
    (hm₂.trans hm₁.symm) (hm₃.trans hm₁.symm) ?_
  rw [hm₁, mul_one, hmom]
private lemma compatible_lastcase {i j r : ℕ} (hij : DecreasingCompatible (i + j))
    (hir : DecreasingCompatible (i + r)) :
    Compatible (i + j + r + 1) (unif i) (unif (i + j + r + 1))
      (((i : ℝ) / (i + r + 1)) • unif j + (1 - (i : ℝ) / (i + r + 1)) • unif (i + j + r + 1)) := by
  have hw₁ : (0 : ℝ) ≤ 1 - (i + j + 1) / (i + j + r + 2) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    linarith
  have h₁ := ((compatible_unif_triple hij).shift (r + 1)).comm₂₃.smul
    (by positivity : (0 : ℝ) ≤ (i + j + 1) / (i + j + r + 2))
  have h₂ := ((compatible_unif_triple hir).shift (j + 1)).smul hw₁
  rw [(by grind : i + r + (j + 1) = i + j + (r + 1))] at h₂
  rw [(by grind : i + j + r + 1 = i + j + (r + 1))]
  convert h₁.add h₂ using 1
  · ext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · ext k
    simp only [unif, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    grind
  · ext k
    simp only [unif, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    grind
private lemma compatible_top (ih : ∀ m < N, DecreasingCompatible m) {i j : ℕ} (hi : i ≤ N)
    (hj : j ≤ N) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hsum : (i : ℝ) + α * j + (1 - α) * N = N) :
    Compatible N (unif N) (unif i) (α • unif j + (1 - α) • unif N) := by
  have hieq : (i : ℝ) = α * (N - j) := by linarith
  obtain rfl | hi₀ := Nat.eq_zero_or_pos i
  · rcases mul_eq_zero.1 (by simpa using hieq.symm : α * (N - j : ℝ) = 0) with rfl | hjN
    · simpa using compatible_unif_zero.comm₁₂
    obtain rfl : j = N := by exact_mod_cast (by linarith : (j : ℝ) = N)
    rw [← add_smul]
    simpa using compatible_unif_zero.comm₁₂
  have hij : i + j < N := by
    have : (0 : ℝ) < i := by exact_mod_cast hi₀
    exact_mod_cast (by nlinarith : (i + j : ℝ) < N)
  obtain ⟨r, rfl⟩ : ∃ r, N = i + j + r + 1 := ⟨N - i - j - 1, by grind⟩
  have hα : α = i / (i + r + 1) := by
    rw [eq_div_iff (by positivity)]
    push_cast at hieq
    linarith
  rw [hα]
  exact (compatible_lastcase (ih _ (by grind)) (ih _ (by grind))).comm₁₂
private lemma compatible_unif_top_mix (ih : ∀ m < N, DecreasingCompatible m) {i y z : ℕ}
    (hi : i ≤ N) (hy : y ≤ N) (hz : z ≤ N) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (hyz : y = N ∧ α ≠ 0 ∨ z = N ∧ α ≠ 1) (hsum : (i + N + α * y + (1 - α) * z : ℝ) = 2 * N) :
    Compatible N (unif N) (unif i) (α • unif y + (1 - α) • unif z) := by
  rcases hyz with ⟨rfl, hα0⟩ | ⟨rfl, hα1⟩
  · have h := compatible_top ih hi hz (α := 1 - α) (by linarith)
      (by linarith [lt_of_le_of_ne hα₀ (Ne.symm hα0)]) (by linarith)
    rwa [sub_sub_cancel, add_comm ((1 - α) • unif z)] at h
  · exact compatible_top ih hi hy hα₀ (lt_of_le_of_ne hα₁ hα1) (by linarith)
end ArithmeticTriangleRemovalInVectorSpaces
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ArithmeticTriangleRemovalInVectorSpaces
variable {N k : ℕ} {π π' π₁ π₂ π₃ : ℕ → ℝ}
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution (ih : ∀ m < N, DecreasingCompatible m) {k₁ k₂ y z : ℕ} (hk₁ : k₁ ≤ N)
    (hk₂ : k₂ ≤ N) (hy : y ≤ N) (hz : z ≤ N) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (hsum : (k₁ + k₂ + α * y + (1 - α) * z : ℝ) = 2 * N) :
    Compatible N (unif k₁) (unif k₂) (α • unif y + (1 - α) • unif z) := by
  obtain rfl | hN := eq_or_ne N 0
  · obtain ⟨rfl, rfl, rfl, rfl⟩ : k₁ = 0 ∧ k₂ = 0 ∧ y = 0 ∧ z = 0 := by grind
    rw [← add_smul, add_sub_cancel, one_smul]
    exact compatible_unif_zero
  have hd := isDecreasingOn_mix hy hz hα₀ hα₁
  have hm := mass_mix hy hz α
  have hmom : moment N (unif k₁) + moment N (unif k₂) +
      moment N (α • unif y + (1 - α) • unif z) = N := by
    rw [moment_unif hk₁, moment_unif hk₂, moment_mix hy hz]
    linarith
  by_cases hA : k₁ < N ∧ k₂ < N
  · obtain ⟨hA₁, hA₂⟩ := hA
    exact (compatible_of_eq_zero_of_eq_zero_of_mass_eq_one ih hN hd (isDecreasingOn_unif hk₁)
      (isDecreasingOn_unif hk₂) (unif_eq_zero hA₁) (unif_eq_zero hA₂) hm (mass_unif hk₁)
      (mass_unif hk₂) (by linarith)).comm₁₂.comm₂₃
  by_cases hQ : (y < N ∨ α = 0) ∧ (z < N ∨ α = 1)
  · obtain ⟨hQy, hQz⟩ := hQ
    obtain hk₂N | rfl := hk₂.lt_or_eq
    · exact compatible_of_eq_zero_of_eq_zero_of_mass_eq_one ih hN (isDecreasingOn_unif hk₁)
        (isDecreasingOn_unif hk₂) hd (unif_eq_zero hk₂N) (mix_eq_zero hQy hQz) (mass_unif hk₁)
        (mass_unif hk₂) hm hmom
    obtain hk₁N | rfl := hk₁.lt_or_eq
    · exact (compatible_of_eq_zero_of_eq_zero_of_mass_eq_one ih hN (isDecreasingOn_unif hk₂)
        (isDecreasingOn_unif hk₁) hd (unif_eq_zero hk₁N) (mix_eq_zero hQy hQz) (mass_unif hk₂)
        (mass_unif hk₁) hm (by linarith)).comm₁₂
    rw [mix_eq_unif_zero hα₀ hα₁ (by linarith)]
    exact compatible_unif_zero.comm₁₃
  rcases (by grind : k₁ = N ∨ k₂ = N) with rfl | rfl
  · exact compatible_unif_top_mix ih hk₂ hy hz hα₀ hα₁ (by grind) (by linarith)
  · exact (compatible_unif_top_mix ih hk₁ hy hz hα₀ hα₁ (by grind) (by linarith)).comm₁₂
end ArithmeticTriangleRemovalInVectorSpaces
