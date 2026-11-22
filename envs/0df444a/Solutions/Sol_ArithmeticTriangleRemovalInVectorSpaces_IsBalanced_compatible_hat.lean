-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.IsBalanced.compatible_hat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:16:00.124933+00:00
-- url     : https://prove2.me/submissions/a7df1165-4e64-4bd3-bdf5-aa6df22b809d

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Uniform
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Decomposition
public import Theorems.Thm_P2M_ArithmeticTriangleRemovalInVectorSpaces_IsBalanced_comm___927a6ae1263a
public import Theorems.Thm_P2M_ArithmeticTriangleRemovalInVectorSpaces_IsBalanced_comm___3c74011adbe1
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_Compatible_add
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_Compatible_smul
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsDecreasingOn_add
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsDecreasingOn_smul
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_compatible_unif_mix
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_compatible_zero
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_hat_add
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_hat_single
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_hat_smul
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mass_add
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mass_smul
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mass_sub
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mem_sumTriples
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_moment_add
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_moment_smul
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_moment_sub
public import Theorems.Thm_P2M_ArithmeticTriangleRemovalInVectorSpaces_Compatible_comm___bf003541382f
public import Theorems.Thm_P2M_ArithmeticTriangleRemovalInVectorSpaces_Compatible_comm___c955cfa1f590
attribute [local simp] ArithmeticTriangleRemovalInVectorSpaces.mem_sumTriples


section
public section
open Finset Function
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {N : ℕ} {w w₁ w₂ w₃ σ σ₁ σ₂ σ₃ : ℕ → ℝ} {μ μ₁ μ₂ μ₃ p : ℝ}
private lemma IsWeight.mass_nonneg (hw : IsWeight N w) : 0 ≤ mass N w := by
  obtain ⟨hw₀, -⟩ := hw
  apply sum_nonneg
  intro k _
  exact hw₀ k
private lemma IsWeight.hat_eq_zero (hw : IsWeight N w) (h0 : mass N w = 0) : hat N w = 0 := by
  obtain ⟨hw₀, -⟩ := hw
  ext j
  apply sum_eq_zero
  intro k hk
  rw [(sum_eq_zero_iff_of_nonneg fun k _ ↦ hw₀ k).1 h0 k hk, zero_mul]
private lemma IsWeight.sub (hw : IsWeight N w) (hσ : IsWeight N σ) (hle : ∀ k, p * σ k ≤ w k) :
    IsWeight N (w - p • σ) := by
  obtain ⟨-, hwN⟩ := hw
  obtain ⟨-, hσN⟩ := hσ
  exact ⟨fun k ↦ sub_nonneg.2 (hle k), fun k hk ↦ by simp [hwN k hk, hσN k hk]⟩
private lemma IsWeight.exists_le_moment_le (hw : IsWeight N w) (hM : mass N w ≠ 0) :
    (∃ a ≤ N, w a ≠ 0 ∧ a * mass N w ≤ moment N w) ∧
      ∃ b ≤ N, w b ≠ 0 ∧ moment N w ≤ b * mass N w := by
  obtain ⟨hw₀, -⟩ := hw
  set s := {k ∈ range (N + 1) | w k ≠ 0}
  obtain ⟨k, hk, hwk⟩ := exists_ne_zero_of_sum_ne_zero hM
  have hs : s.Nonempty := ⟨k, mem_filter.2 ⟨hk, hwk⟩⟩
  have heq : ∑ k ∈ s, w k * (k * mass N w) = ∑ k ∈ s, w k * moment N w := by
    simp only [mass, moment]
    rw [sum_filter_of_ne fun k _ h ↦ left_ne_zero_of_mul h,
      sum_filter_of_ne fun k _ h ↦ left_ne_zero_of_mul h]
    simp_rw [mul_left_comm (w _), ← mul_assoc, ← sum_mul]
    ring
  obtain ⟨a, ha, hle⟩ := exists_le_of_sum_le hs heq.le
  obtain ⟨b, hb, hge⟩ := exists_le_of_sum_le hs heq.ge
  simp only [s, mem_filter, mem_range] at ha hb
  obtain ⟨ha, hwa⟩ := ha
  obtain ⟨hb, hwb⟩ := hb
  exact ⟨⟨a, by grind, hwa, le_of_mul_le_mul_left hle ((hw₀ a).lt_of_ne' hwa)⟩,
    ⟨b, by grind, hwb, le_of_mul_le_mul_left hge ((hw₀ b).lt_of_ne' hwb)⟩⟩
private lemma isUnitBelow_single {c : ℕ} (hc : c ≤ N) (hw : w c ≠ 0) :
    IsUnitBelow N w (Pi.single c 1) c := by
  refine ⟨⟨(by intro k; by_cases h : k = c <;> simp [Pi.single_apply, h]), fun _ hk ↦ Pi.single_eq_of_ne (by grind) _⟩,
    by simp [mass, Nat.lt_succ_of_le hc], by simp [moment, Pi.single_apply, Nat.lt_succ_of_le hc],
    ?_⟩
  exact Pi.support_single_subset.trans (Set.singleton_subset_iff.2 hw)
private lemma isUnitBelow_mix {y z : ℕ} (hy : y ≤ N) (hz : z ≤ N) {α : ℝ} (hα₀ : 0 ≤ α)
    (hα₁ : α ≤ 1) (hwy : w y ≠ 0) (hwz : w z ≠ 0) :
    IsUnitBelow N w (α • (Pi.single y 1 : ℕ → ℝ) + (1 - α) • (Pi.single z 1 : ℕ → ℝ))
      (α * y + (1 - α) * z) := by
  obtain ⟨⟨hy₀, hyN⟩, hy₁, hyμ, hys⟩ := isUnitBelow_single hy hwy
  obtain ⟨⟨hz₀, hzN⟩, hz₁, hzμ, hzs⟩ := isUnitBelow_single hz hwz
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro k
    exact add_nonneg (mul_nonneg hα₀ (hy₀ k)) (mul_nonneg (by linarith) (hz₀ k))
  · intro k hk
    simp [hyN k hk, hzN k hk]
  · rw [mass_add, mass_smul, mass_smul, hy₁, hz₁]
    ring
  · rw [moment_add, moment_smul, moment_smul, hyμ, hzμ]
  · exact (support_add _ _).trans (Set.union_subset ((support_const_smul_subset _ _).trans hys)
      ((support_const_smul_subset _ _).trans hzs))
private lemma IsUnitBelow.mass_sub_smul (hσ : IsUnitBelow N w σ μ) :
    mass N (w - p • σ) = mass N w - p := by
  obtain ⟨-, hσ₁, -, -⟩ := hσ
  rw [mass_sub, mass_smul, hσ₁, mul_one]
private lemma IsUnitBelow.moment_sub_smul (hσ : IsUnitBelow N w σ μ) :
    moment N (w - p • σ) = moment N w - p * μ := by
  obtain ⟨-, -, hσμ, -⟩ := hσ
  rw [moment_sub, moment_smul, hσμ]
private lemma IsUnitBelow.exists_ratio (hσ : IsUnitBelow N w σ μ) (hw : IsWeight N w) :
    ∃ r > 0, (∀ k, r * σ k ≤ w k) ∧ ∃ k ≤ N, σ k ≠ 0 ∧ r * σ k = w k := by
  obtain ⟨⟨hσ₀, hσN⟩, hσ₁, -, hσs⟩ := hσ
  obtain ⟨hw₀, -⟩ := hw
  set s := {k ∈ range (N + 1) | σ k ≠ 0}
  obtain ⟨k, hk, hσk⟩ := exists_ne_zero_of_sum_ne_zero (hσ₁.trans_ne one_ne_zero)
  have hs : s.Nonempty := ⟨k, mem_filter.2 ⟨hk, hσk⟩⟩
  obtain ⟨k₀, hk₀, heq⟩ := exists_mem_eq_inf' hs fun k ↦ w k / σ k
  simp only [s, mem_filter, mem_range] at hk₀
  obtain ⟨hk₀N, hσk₀⟩ := hk₀
  refine ⟨s.inf' hs fun k ↦ w k / σ k, ?_, ?_, k₀, by grind, hσk₀, ?_⟩
  · rw [gt_iff_lt, lt_inf'_iff]
    intro k hk
    simp only [s, mem_filter] at hk
    obtain ⟨-, hσk⟩ := hk
    exact div_pos ((hw₀ k).lt_of_ne' (hσs hσk)) ((hσ₀ k).lt_of_ne' hσk)
  · intro k
    by_cases hσk : σ k = 0
    · rw [hσk, mul_zero]
      exact hw₀ k
    · rw [← le_div_iff₀ ((hσ₀ k).lt_of_ne' hσk)]
      apply inf'_le
      simp only [s, mem_filter, mem_range]
      exact ⟨by_contra fun h ↦ hσk (hσN k (by grind)), hσk⟩
  · rw [heq]
    field_simp [hσk₀]
private lemma IsUnitBelow.mul_le (hσ : IsUnitBelow N w σ μ) {r : ℝ} (hpr : p ≤ r)
    (hr : ∀ k, r * σ k ≤ w k) (k : ℕ) : p * σ k ≤ w k := by
  obtain ⟨⟨hσ₀, -⟩, -⟩ := hσ
  grw [hpr]
  · exact hr k
  · exact hσ₀ k
private lemma IsUnitBelow.support_sub_subset (hσ : IsUnitBelow N w σ μ) :
    {k ∈ range (N + 1) | (w - p • σ) k ≠ 0} ⊆ {k ∈ range (N + 1) | w k ≠ 0} := by
  obtain ⟨-, -, -, hσs⟩ := hσ
  have hsub : support (w - p • σ) ⊆ support w :=
    (support_sub _ _).trans (Set.union_subset subset_rfl
      ((support_const_smul_subset _ _).trans hσs))
  intro k
  simp only [mem_filter]
  rintro ⟨hk, hne⟩
  exact ⟨hk, hsub hne⟩
private lemma IsUnitBelow.supportCard_sub_le (hσ : IsUnitBelow N w σ μ) :
    supportCard N (w - p • σ) ≤ supportCard N w :=
  card_le_card hσ.support_sub_subset
private lemma IsUnitBelow.supportCard_sub_lt (hσ : IsUnitBelow N w σ μ) {k : ℕ} (hk : k ≤ N)
    (hσk : σ k ≠ 0) (hpk : p * σ k = w k) : supportCard N (w - p • σ) < supportCard N w := by
  have ⟨_, _, _, hσs⟩ := hσ
  refine card_lt_card ((ssubset_iff_of_subset hσ.support_sub_subset).2 ⟨k, ?_, ?_⟩)
  · simp only [mem_filter, mem_range]
    exact ⟨by grind, hσs hσk⟩
  · simp [hpk]
private lemma IsBalanced.sub (hb : IsBalanced N w₁ w₂ w₃) (h₁ : IsUnitBelow N w₁ σ₁ μ₁)
    (h₂ : IsUnitBelow N w₂ σ₂ μ₂) (h₃ : IsUnitBelow N w₃ σ₃ μ₃) (hμ : μ₁ + μ₂ + μ₃ = 2 * N)
    (hle₁ : ∀ k, p * σ₁ k ≤ w₁ k) (hle₂ : ∀ k, p * σ₂ k ≤ w₂ k) (hle₃ : ∀ k, p * σ₃ k ≤ w₃ k) :
    IsBalanced N (w₁ - p • σ₁) (w₂ - p • σ₂) (w₃ - p • σ₃) := by
  obtain ⟨hw₁, hw₂, hw₃, hm₂, hm₃, hmom⟩ := hb
  have ⟨hσ₁, _⟩ := h₁
  have ⟨hσ₂, _⟩ := h₂
  have ⟨hσ₃, _⟩ := h₃
  refine ⟨hw₁.sub hσ₁ hle₁, hw₂.sub hσ₂ hle₂, hw₃.sub hσ₃ hle₃, ?_, ?_, ?_⟩
  · rw [h₂.mass_sub_smul, h₁.mass_sub_smul, hm₂]
  · rw [h₃.mass_sub_smul, h₁.mass_sub_smul, hm₃]
  · rw [h₁.moment_sub_smul, h₂.moment_sub_smul, h₃.moment_sub_smul, h₁.mass_sub_smul]
    linear_combination hmom - p * hμ
private lemma IsBalanced.compatible_hat_of_isUnitBelow (hb : IsBalanced N w₁ w₂ w₃)
    (h₁ : IsUnitBelow N w₁ σ₁ μ₁) (h₂ : IsUnitBelow N w₂ σ₂ μ₂) (h₃ : IsUnitBelow N w₃ σ₃ μ₃)
    (hμ : μ₁ + μ₂ + μ₃ = 2 * N) (hs : Compatible N (hat N σ₁) (hat N σ₂) (hat N σ₃))
    (IH : ∀ v₁ v₂ v₃, IsBalanced N v₁ v₂ v₃ →
      supportCard N v₁ + supportCard N v₂ + supportCard N v₃ <
        supportCard N w₁ + supportCard N w₂ + supportCard N w₃ →
      Compatible N (hat N v₁) (hat N v₂) (hat N v₃)) :
    Compatible N (hat N w₁) (hat N w₂) (hat N w₃) := by
  have ⟨hw₁, hw₂, hw₃, _⟩ := hb
  obtain ⟨r₁, hr₁, hle₁, k₁, hk₁, hσk₁, heq₁⟩ := h₁.exists_ratio hw₁
  obtain ⟨r₂, hr₂, hle₂, k₂, hk₂, hσk₂, heq₂⟩ := h₂.exists_ratio hw₂
  obtain ⟨r₃, hr₃, hle₃, k₃, hk₃, hσk₃, heq₃⟩ := h₃.exists_ratio hw₃
  set p := min (min r₁ r₂) r₃ with hp
  have hcomp := (IH _ _ _ (hb.sub h₁ h₂ h₃ hμ
    (h₁.mul_le (p := p) ((min_le_left _ _).trans (min_le_left _ _)) hle₁)
    (h₂.mul_le (p := p) ((min_le_left _ _).trans (min_le_right _ _)) hle₂)
    (h₃.mul_le (p := p) (min_le_right _ _) hle₃)) ?_).add (hs.smul (by positivity : 0 ≤ p))
  · simpa only [← hat_smul, ← hat_add, sub_add_cancel] using hcomp
  obtain hp | hp | hp : p = r₁ ∨ p = r₂ ∨ p = r₃ := by grind
  · grind [h₁.supportCard_sub_lt hk₁ hσk₁ (hp ▸ heq₁), h₂.supportCard_sub_le (p := p),
      h₃.supportCard_sub_le (p := p)]
  · grind [h₁.supportCard_sub_le (p := p), h₂.supportCard_sub_lt hk₂ hσk₂ (hp ▸ heq₂),
      h₃.supportCard_sub_le (p := p)]
  · grind [h₁.supportCard_sub_le (p := p), h₂.supportCard_sub_le (p := p),
      h₃.supportCard_sub_lt hk₃ hσk₃ (hp ▸ heq₃)]
private lemma exists_mix {c d y z : ℕ} (h₁ : c + d + y ≤ 2 * N) (h₂ : 2 * N ≤ c + d + z) :
    ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧ (c + d + α * y + (1 - α) * z : ℝ) = 2 * N := by
  have h₁' : (c + d + y : ℝ) ≤ 2 * N := by exact_mod_cast h₁
  have h₂' : (2 * N : ℝ) ≤ c + d + z := by exact_mod_cast h₂
  obtain ⟨α, ⟨hα₀, hα₁⟩, hα⟩ := intermediate_value_Icc' zero_le_one
    (by fun_prop : Continuous fun α : ℝ ↦ (c + d + α * y + (1 - α) * z : ℝ)).continuousOn
    ⟨by simpa using h₁', by simpa using h₂'⟩
  exact ⟨α, hα₀, hα₁, hα⟩
private lemma IsBalanced.compatible_hat_of_mix (ih : ∀ m < N, DecreasingCompatible m)
    (hb : IsBalanced N w₁ w₂ w₃) {n : ℕ}
    (hn : supportCard N w₁ + supportCard N w₂ + supportCard N w₃ ≤ n)
    (IH : ∀ m < n, ∀ v₁ v₂ v₃, IsBalanced N v₁ v₂ v₃ →
      supportCard N v₁ + supportCard N v₂ + supportCard N v₃ ≤ m →
      Compatible N (hat N v₁) (hat N v₂) (hat N v₃))
    {c d y z : ℕ} (hc : c ≤ N) (hd : d ≤ N) (hy : y ≤ N) (hz : z ≤ N) (hwc : w₁ c ≠ 0)
    (hwd : w₂ d ≠ 0) (hwy : w₃ y ≠ 0) (hwz : w₃ z ≠ 0) (h₁ : c + d + y ≤ 2 * N)
    (h₂ : 2 * N ≤ c + d + z) : Compatible N (hat N w₁) (hat N w₂) (hat N w₃) := by
  obtain ⟨α, hα₀, hα₁, hsum⟩ := exists_mix h₁ h₂
  refine hb.compatible_hat_of_isUnitBelow (isUnitBelow_single hc hwc) (isUnitBelow_single hd hwd)
    (isUnitBelow_mix hy hz hα₀ hα₁ hwy hwz) (by linarith) ?_ ?_
  · rw [hat_single hc, hat_single hd, hat_add, hat_smul, hat_smul, hat_single hy, hat_single hz]
    exact compatible_unif_mix ih hc hd hy hz hα₀ hα₁ hsum
  · intro v₁ v₂ v₃ hv hlt
    exact IH _ (by grind) _ _ _ hv le_rfl
private lemma IsBalanced.compatible_hat_of_le (ih : ∀ m < N, DecreasingCompatible m)
    (hb : IsBalanced N w₁ w₂ w₃) (n : ℕ)
    (hn : supportCard N w₁ + supportCard N w₂ + supportCard N w₃ ≤ n) :
    Compatible N (hat N w₁) (hat N w₂) (hat N w₃) := by
  induction n using Nat.strong_induction_on generalizing w₁ w₂ w₃ with
  | _ n IH =>
  have ⟨hw₁, hw₂, hw₃, hm₂, hm₃, hmom⟩ := hb
  by_cases hM : mass N w₁ = 0
  · rw [hw₁.hat_eq_zero hM, hw₂.hat_eq_zero (hm₂.trans hM), hw₃.hat_eq_zero (hm₃.trans hM)]
    exact compatible_zero
  obtain ⟨⟨a₁, ha₁, hwa₁, hla₁⟩, ⟨b₁, hb₁, hwb₁, hlb₁⟩⟩ := hw₁.exists_le_moment_le hM
  obtain ⟨⟨a₂, ha₂, hwa₂, hla₂⟩, ⟨b₂, hb₂, hwb₂, hlb₂⟩⟩ :=
    hw₂.exists_le_moment_le (by rwa [hm₂])
  obtain ⟨⟨a₃, ha₃, hwa₃, hla₃⟩, ⟨b₃, hb₃, hwb₃, hlb₃⟩⟩ :=
    hw₃.exists_le_moment_le (by rwa [hm₃])
  rw [hm₂] at hla₂ hlb₂
  rw [hm₃] at hla₃ hlb₃
  have hMpos : 0 < mass N w₁ := hw₁.mass_nonneg.lt_of_ne' hM
  have hA : a₁ + a₂ + a₃ ≤ 2 * N := by
    exact_mod_cast (by nlinarith : (a₁ + a₂ + a₃ : ℝ) ≤ 2 * N)
  have hB : 2 * N ≤ b₁ + b₂ + b₃ := by
    exact_mod_cast (by nlinarith : (2 * N : ℝ) ≤ b₁ + b₂ + b₃)
  by_cases h₁ : 2 * N ≤ a₁ + a₂ + b₃
  · exact hb.compatible_hat_of_mix ih hn IH ha₁ ha₂ ha₃ hb₃ hwa₁ hwa₂ hwa₃ hwb₃ hA h₁
  by_cases h₂ : 2 * N ≤ a₁ + b₂ + b₃
  · exact (hb.comm₂₃.compatible_hat_of_mix ih (by grind) IH ha₁ hb₃ ha₂ hb₂ hwa₁ hwb₃ hwa₂ hwb₂
      (by grind) (by grind)).comm₂₃
  · exact (hb.comm₁₃.compatible_hat_of_mix ih (by grind) IH hb₃ hb₂ ha₁ hb₁ hwb₃ hwb₂ hwa₁ hwb₁
      (by grind) (by grind)).comm₁₃
end ArithmeticTriangleRemovalInVectorSpaces
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset Function
open ArithmeticTriangleRemovalInVectorSpaces
variable {N : ℕ} {w w₁ w₂ w₃ σ σ₁ σ₂ σ₃ : ℕ → ℝ} {μ μ₁ μ₂ μ₃ p : ℝ}
namespace ArithmeticTriangleRemovalInVectorSpaces
namespace IsBalanced
theorem _root_.solution (ih : ∀ m < N, DecreasingCompatible m)
    (hb : IsBalanced N w₁ w₂ w₃) : Compatible N (hat N w₁) (hat N w₂) (hat N w₃) :=
  hb.compatible_hat_of_le ih _ le_rfl
end IsBalanced
end ArithmeticTriangleRemovalInVectorSpaces
