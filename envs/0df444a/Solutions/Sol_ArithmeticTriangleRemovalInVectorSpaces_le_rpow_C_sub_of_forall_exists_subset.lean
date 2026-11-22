-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.le_rpow_C_sub_of_forall_exists_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:19:42.762281+00:00
-- url     : https://prove2.me/submissions/6754bb6d-2e1a-4a4e-bcb9-bf8faa999e41

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_LowerBound
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_MaximalFamily
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_TensorPower
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Product
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_TensorPower
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Tightness_Exponent
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_ZMod
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsMulticoloredSumFree_card_triangles_image
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsMulticoloredSumFree_comp
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsMulticoloredSumFree_injective_left
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsMulticoloredSumFree_injective_middle
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsMulticoloredSumFree_injective_right
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_c_lt_one
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_c_pos
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_div_le_sq_div_mul_min_div_two
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_exists_isMulticoloredSumFree_rpow_le
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_exists_lt_pow_le_inv_lt
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_inv_pow_le_inv_add_sq_rpow
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_inv_pow_le_mul_rpow
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_le_mul_rpow_one_add_of_mul_sq_le
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mem_sumTriples
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mem_triangles
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mk_mem_vecSumTriples
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mul_min_div_two_lt_inv_max_sub
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mul_min_div_two_pos
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mul_pow_lt_of_rpow_mul_le
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mul_rpow_le_rpow_sub
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_shares_mk
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_triangles_eq_empty_iff
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_triangles_nonempty_of_card_sdiff_add_lt
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_typeClass_nonempty
public import Theorems.Thm_P2M_ArithmeticTriangleRemovalInVectorSpaces_sq_add_one_le_n__a0a2c17b21cd
attribute [local simp] ArithmeticTriangleRemovalInVectorSpaces.mem_sumTriples
attribute [local simp] ArithmeticTriangleRemovalInVectorSpaces.mem_triangles
attribute [local simp] ArithmeticTriangleRemovalInVectorSpaces.mk_mem_vecSumTriples
attribute [local simp] ArithmeticTriangleRemovalInVectorSpaces.shares_mk
attribute [local simp] ArithmeticTriangleRemovalInVectorSpaces.typeClass_nonempty


section
public section
open Finset Function
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {p n : ℕ} [Fact p.Prime]
variable {l : ℕ} {ι : Type*} [Fintype ι] {x y z : ι → Fin n → ZMod p}
private lemma IsMulticoloredSumFree.mul_sq_le_card_of_forall_exists_subset {ε δ : ℝ}
    (h : IsMulticoloredSumFree x y z) (hε : ε * p ^ n < Fintype.card ι)
    (hδ : ∀ X Y Z : Finset (Fin n → ZMod p),
      #((X ×ˢ Y ×ˢ Z).filter fun (x, y, z) ↦ x + y + z = 0) < δ * (p ^ n) ^ 2 →
        ∃ X' ⊆ X, ∃ Y' ⊆ Y, ∃ Z' ⊆ Z, #(X \ X') + #(Y \ Y') + #(Z \ Z') ≤ ε * p ^ n ∧
          ∀ x ∈ X', ∀ y ∈ Y', ∀ z ∈ Z', x + y + z ≠ 0) :
    δ * (p ^ n) ^ 2 ≤ Fintype.card ι := by
  by_contra! hlt
  obtain ⟨X', -, Y', -, Z', -, hcard, hempty⟩ := hδ _ _ _ (by rwa [← triangles,
    h.card_triangles_image])
  simpa [triangles_eq_empty_iff.2 hempty] using triangles_nonempty_of_card_sdiff_add_lt
    (X := X') (Y := Y') (Z := Z') h.injective_left h.injective_middle h.injective_right
    (fun i ↦ (h i i i).2 ⟨rfl, rfl⟩) (by exact_mod_cast hcard.trans_lt hε)
private lemma IsMulticoloredSumFree.mul_sq_le_mul_add_one {ε δ : ℝ}
    (h : IsMulticoloredSumFree x y z) (hε0 : 0 ≤ ε) (hε : ε * p ^ n < Fintype.card ι)
    (hδ : ∀ X Y Z : Finset (Fin n → ZMod p),
      #((X ×ˢ Y ×ˢ Z).filter fun (x, y, z) ↦ x + y + z = 0) < δ * (p ^ n) ^ 2 →
        ∃ X' ⊆ X, ∃ Y' ⊆ Y, ∃ Z' ⊆ Z, #(X \ X') + #(Y \ Y') + #(Z \ Z') ≤ ε * p ^ n ∧
          ∀ x ∈ X', ∀ y ∈ Y', ∀ z ∈ Z', x + y + z ≠ 0) :
    δ * (p ^ n) ^ 2 ≤ ε * p ^ n + 1 := by
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (α := Fin (⌊ε * p ^ n⌋₊ + 1)) (β := ι)
    (by rw [Fintype.card_fin]; exact (Nat.floor_lt (by positivity)).2 hε)
  grw [(h.comp f.injective).mul_sq_le_card_of_forall_exists_subset ?_ hδ]
  · rw [Fintype.card_fin]
    push_cast
    linarith [Nat.floor_le (by positivity : 0 ≤ ε * p ^ n)]
  · rw [Fintype.card_fin]
    exact_mod_cast Nat.lt_floor_add_one (ε * p ^ n)
private lemma le_rpow_C_sub_of_lt {η κ η' ε δ : ℝ} (hη : 0 < η) (hκ₁ : 1 ≤ κ)
    (hκη : (c p)⁻¹ - η / 2 ≤ κ) (hη'₀ : 0 < η') (hη' : η' < κ⁻¹ - c p) (hε0 : 0 < ε)
    (hε : ε < ((p : ℝ) ^ (n₀ p η' + 1))⁻¹) (hε' : ε ≤ (p + p ^ 2 : ℝ)⁻¹ ^ (2 / η))
    (hδ : ∀ n (X Y Z : Finset (Fin n → ZMod p)),
      #((X ×ˢ Y ×ˢ Z).filter fun (x, y, z) ↦ x + y + z = 0) < δ * (p ^ n) ^ 2 →
        ∃ X' ⊆ X, ∃ Y' ⊆ Y, ∃ Z' ⊆ Z, #(X \ X') + #(Y \ Y') + #(Z \ Z') ≤ ε * p ^ n ∧
          ∀ x ∈ X', ∀ y ∈ Y', ∀ z ∈ Z', x + y + z ≠ 0) :
    δ ≤ ε ^ (C p - η) := by
  have hp₀ := (Fact.out : p.Prime).pos
  have hp : 1 < (p : ℝ) := Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt
  have hεκ : ε < (((p : ℝ) ^ κ⁻¹) ^ (n₀ p η' + 1))⁻¹ := by
    grw [Real.rpow_le_self_of_one_le hp.le (inv_le_one_of_one_le₀ hκ₁)]
    exact hε
  obtain ⟨n, hn, hpow, hpow'⟩ :=
    exists_lt_pow_le_inv_lt (Real.one_lt_rpow hp (by positivity)) hε0 hεκ
  have hε₁ : ε ≤ 1 := hε.le.trans (inv_le_one_of_one_le₀ (one_le_pow₀ hp.le))
  obtain ⟨m, x, y, z, hxyz, hm⟩ :=
    exists_isMulticoloredSumFree_rpow_le (Fact.out : p.Prime).two_le hη'₀ hn.le
  have := hxyz.mul_sq_le_mul_add_one hε0.le (by
    rw [Fintype.card_fin]
    exact mul_pow_lt_of_rpow_mul_le hp hε0 (by grind) (by linarith) hpow hm) (hδ n)
  grw [le_mul_rpow_one_add_of_mul_sq_le (by positivity) (by positivity) hε0 hε₁ hκ₁
    (inv_pow_le_mul_rpow (by positivity) hε0 (by positivity) hpow') this]
  exact mul_rpow_le_rpow_sub (by positivity) hε0 hε₁ hη (by rw [C, one_div]; linarith) hε'
end ArithmeticTriangleRemovalInVectorSpaces
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset Function
open ArithmeticTriangleRemovalInVectorSpaces
variable {p n : ℕ} [Fact p.Prime]
variable {l : ℕ} {ι : Type*} [Fintype ι] {x y z : ι → Fin n → ZMod p}
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution {η ε δ : ℝ} (hη : 0 < η) (hε : 0 < ε)
    (hε₀ : ε < ε₀ p η)
    (hδ : ∀ n (X Y Z : Finset (Fin n → ZMod p)),
      #((X ×ˢ Y ×ˢ Z).filter fun (x, y, z) ↦ x + y + z = 0) < δ * (p ^ n) ^ 2 →
        ∃ X' ⊆ X, ∃ Y' ⊆ Y, ∃ Z' ⊆ Z, #(X \ X') + #(Y \ Y') + #(Z \ Z') ≤ ε * p ^ n ∧
          ∀ x ∈ X', ∀ y ∈ Y', ∀ z ∈ Z', x + y + z ≠ 0) :
    δ ≤ ε ^ (C p - η) := by
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hc := c_pos (Fact.out : p.Prime).two_le
  have hc₁ := c_lt_one (Fact.out : p.Prime).two_le
  rw [ε₀] at hε₀
  refine le_rpow_C_sub_of_lt hη (le_max_left _ _) (le_max_right _ _)
    (mul_min_div_two_pos hc hc₁ hη) (mul_min_div_two_lt_inv_max_sub hc hc₁ hη) hε hε₀
    (hε₀.le.trans (inv_pow_le_inv_add_sq_rpow hp hη ?_)) hδ
  push_cast
  linarith [div_le_sq_div_mul_min_div_two (X := 2 ^ (p + 3) * (p : ℝ) ^ 10) hc hc₁ hη
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by linarith))),
    sq_add_one_le_n₀ p (c p * min (1 - c p) (c p * η / 2) / 2)]
end ArithmeticTriangleRemovalInVectorSpaces
