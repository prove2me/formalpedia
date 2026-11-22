-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.rpow_le_mul_rpow_mul_card_triangles_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:19:26.240802+00:00
-- url     : https://prove2.me/submissions/5941f727-52e7-4163-9c1d-fb29af0c8844

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Triangle_Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_Sampling
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_Pruning
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_card_triangles_pos
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_c_pos
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_card_triangles_erase_left
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_card_triangles_erase_middle
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_card_triangles_erase_right
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_card_triangles_le_of_degree_le
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mem_triangles
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_triangles_mono
attribute [local simp] ArithmeticTriangleRemovalInVectorSpaces.mem_triangles


section
public section
open Finset Function Submodule
namespace ArithmeticTriangleRemovalInVectorSpaces
private lemma le_rpow_one_sub_div_of_mul_rpow_le {A η D d : ℝ} (hA : 0 < A) (hη₀ : 0 < η)
    (hη₁ : η ≤ 1) (hd₀ : 0 ≤ d) (hdD : d ≤ D) (h : A * D ^ η ≤ 1 + A * (D - d) ^ η) :
    d ≤ D ^ (1 - η) / (A * η) := by
  rcases hd₀.eq_or_lt with rfl | hd
  · positivity
  have hD : 0 < D := hd.trans_le hdD
  have hB : (D - d) ^ η ≤ D ^ η * (1 - η * (d / D)) := by
    rw [(by field_simp : D - d = D * (1 - d / D)),
      Real.mul_rpow hD.le (sub_nonneg.2 ((div_le_one hD).2 hdD))]
    gcongr
    simpa [sub_eq_add_neg] using
      rpow_one_add_le_one_add_mul_self (neg_le_neg ((div_le_one hD).2 hdD)) hη₀.le hη₁
  have key : A * D ^ η * η * (d / D) ≤ 1 := by linarith [mul_le_mul_of_nonneg_left hB hA.le]
  rw [mul_div_assoc', div_le_one hD] at key
  rw [Real.rpow_sub hD, Real.rpow_one, div_div, le_div_iff₀ (by positivity)]
  linarith
private lemma rpow_le_mul_rpow_of_le_mul_div_rpow {K N D' B c η : ℝ} (hN : 0 < N) (hD' : 0 < D')
    (hB : 0 < B) (hη : (1 - η) * (1 + c) = 1)
    (h : D' ≤ K * (D' ^ (1 - η) / B / N) ^ (1 + c) * N ^ 2) :
    B ^ (1 + c) ≤ K * N ^ (1 - c) := by
  have hN2 : N ^ 2 = N ^ (1 + c) * N ^ (1 - c) := by
    rw [← Real.rpow_add hN]
    norm_num
  rw [Real.div_rpow (by positivity) hN.le, Real.div_rpow (by positivity) hB.le,
    ← Real.rpow_mul hD'.le, hη, Real.rpow_one, hN2] at h
  field_simp at h
  exact h
private lemma rpow_le_mul_rpow_mul_rpow_of_le {K N D D' m c : ℝ} (hc : 0 < c) (hN : 0 < N)
    (hD : 0 < D) (hD' : 0 < D') (hm : 0 < m)
    (h : D' ≤ K * (D' ^ (1 - c / (1 + c)) / (m / (2 * D ^ (c / (1 + c))) * (c / (1 + c))) / N) ^
      (1 + c) * N ^ 2) :
    (c / (1 + c) * m / 2) ^ (1 + c) ≤ K * N ^ (1 - c) * D ^ c := by
  have h := rpow_le_mul_rpow_of_le_mul_div_rpow hN hD' (by positivity) (by grind) h
  rwa [(by field_simp : m / (2 * D ^ (c / (1 + c))) * (c / (1 + c)) =
    c / (1 + c) * m / 2 / D ^ (c / (1 + c))), Real.div_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hD.le, (by grind : c / (1 + c) * (1 + c) = c),
    div_le_iff₀ (by positivity)] at h
variable {V ι : Type*} [AddCommGroup V] [DecidableEq V] [Fintype ι] {x y z : ι → V}
omit [AddCommGroup V] in
/-- An injective family takes each value at most once. -/
private lemma card_filter_apply_eq_le_one {f : ι → V} (hf : Injective f) (v : V) :
    #{i | f i = v} ≤ 1 :=
  card_le_one.2 fun _ _ _ _ ↦ hf (by simp_all)
omit [AddCommGroup V] in
/-- Removing a vertex from `X` puts at most one more vertex-disjoint triangle outside. -/
private lemma card_filter_not_mem_erase_left_le (hx : Injective x) (X Y Z : Finset V) (v : V) :
    #{i | ¬(x i ∈ X.erase v ∧ y i ∈ Y ∧ z i ∈ Z)} ≤ #{i | ¬(x i ∈ X ∧ y i ∈ Y ∧ z i ∈ Z)} + 1 := by
  classical
  grw [← card_filter_apply_eq_le_one hx v, ← card_union_le]
  apply card_le_card
  intro i
  simp only [mem_filter, mem_univ, true_and, mem_union, mem_erase]
  tauto
omit [AddCommGroup V] in
/-- Removing a vertex from `Y` puts at most one more vertex-disjoint triangle outside. -/
private lemma card_filter_not_mem_erase_middle_le (hy : Injective y) (X Y Z : Finset V) (v : V) :
    #{i | ¬(x i ∈ X ∧ y i ∈ Y.erase v ∧ z i ∈ Z)} ≤ #{i | ¬(x i ∈ X ∧ y i ∈ Y ∧ z i ∈ Z)} + 1 := by
  classical
  grw [← card_filter_apply_eq_le_one hy v, ← card_union_le]
  apply card_le_card
  intro i
  simp only [mem_filter, mem_univ, true_and, mem_union, mem_erase]
  tauto
omit [AddCommGroup V] in
/-- Removing a vertex from `Z` puts at most one more vertex-disjoint triangle outside. -/
private lemma card_filter_not_mem_erase_right_le (hz : Injective z) (X Y Z : Finset V) (v : V) :
    #{i | ¬(x i ∈ X ∧ y i ∈ Y ∧ z i ∈ Z.erase v)} ≤ #{i | ¬(x i ∈ X ∧ y i ∈ Y ∧ z i ∈ Z)} + 1 := by
  classical
  grw [← card_filter_apply_eq_le_one hz v, ← card_union_le]
  apply card_le_card
  intro i
  simp only [mem_filter, mem_univ, true_and, mem_union, mem_erase]
  tauto
variable {A η : ℝ} {X Y Z X' Y' Z' : Finset V} {v : V}
private lemma card_filter_fst_le_of_potential_le (hx : Injective x) (hA : 0 < A) (hη₀ : 0 < η)
    (hη₁ : η ≤ 1) (h : potential x y z A η (X, Y, Z) ≤ potential x y z A η (X.erase v, Y, Z)) :
    #((triangles X Y Z).filter fun (x, _, _) ↦ x = v) ≤
      #(triangles X Y Z) ^ (1 - η) / (A * η) := by
  refine le_rpow_one_sub_div_of_mul_rpow_le hA hη₀ hη₁ (Nat.cast_nonneg _)
    (by exact_mod_cast card_filter_le _ _) ?_
  have hr : (#{i | ¬(x i ∈ X.erase v ∧ y i ∈ Y ∧ z i ∈ Z)} : ℝ) ≤
      #{i | ¬(x i ∈ X ∧ y i ∈ Y ∧ z i ∈ Z)} + 1 := by
    exact_mod_cast card_filter_not_mem_erase_left_le hx X Y Z v
  simp only [potential, ← card_triangles_erase_left X Y Z v] at h ⊢
  push_cast at h ⊢
  rw [add_sub_cancel_right]
  linarith
private lemma card_filter_snd_le_of_potential_le (hy : Injective y) (hA : 0 < A) (hη₀ : 0 < η)
    (hη₁ : η ≤ 1) (h : potential x y z A η (X, Y, Z) ≤ potential x y z A η (X, Y.erase v, Z)) :
    #((triangles X Y Z).filter fun (_, y, _) ↦ y = v) ≤
      #(triangles X Y Z) ^ (1 - η) / (A * η) := by
  refine le_rpow_one_sub_div_of_mul_rpow_le hA hη₀ hη₁ (Nat.cast_nonneg _)
    (by exact_mod_cast card_filter_le _ _) ?_
  have hr : (#{i | ¬(x i ∈ X ∧ y i ∈ Y.erase v ∧ z i ∈ Z)} : ℝ) ≤
      #{i | ¬(x i ∈ X ∧ y i ∈ Y ∧ z i ∈ Z)} + 1 := by
    exact_mod_cast card_filter_not_mem_erase_middle_le hy X Y Z v
  simp only [potential, ← card_triangles_erase_middle X Y Z v] at h ⊢
  push_cast at h ⊢
  rw [add_sub_cancel_right]
  linarith
private lemma card_filter_thd_le_of_potential_le (hz : Injective z) (hA : 0 < A) (hη₀ : 0 < η)
    (hη₁ : η ≤ 1) (h : potential x y z A η (X, Y, Z) ≤ potential x y z A η (X, Y, Z.erase v)) :
    #((triangles X Y Z).filter fun (_, _, z) ↦ z = v) ≤
      #(triangles X Y Z) ^ (1 - η) / (A * η) := by
  refine le_rpow_one_sub_div_of_mul_rpow_le hA hη₀ hη₁ (Nat.cast_nonneg _)
    (by exact_mod_cast card_filter_le _ _) ?_
  have hr : (#{i | ¬(x i ∈ X ∧ y i ∈ Y ∧ z i ∈ Z.erase v)} : ℝ) ≤
      #{i | ¬(x i ∈ X ∧ y i ∈ Y ∧ z i ∈ Z)} + 1 := by
    exact_mod_cast card_filter_not_mem_erase_right_le hz X Y Z v
  simp only [potential, ← card_triangles_erase_right X Y Z v] at h ⊢
  push_cast at h ⊢
  rw [add_sub_cancel_right]
  linarith
private lemma potential_eq_mul_rpow (hxX : ∀ i, x i ∈ X) (hyY : ∀ i, y i ∈ Y) (hzZ : ∀ i, z i ∈ Z) :
    potential x y z A η (X, Y, Z) = A * #(triangles X Y Z) ^ η := by
  simp [potential, hxX, hyY, hzZ]
private lemma potential_eq_card_of_triangles_eq_empty (hsum : ∀ i, x i + y i + z i = 0) (hη : η ≠ 0)
    (h : triangles X Y Z = ∅) : potential x y z A η (X, Y, Z) = Fintype.card ι := by
  have hout (i : ι) : ¬(x i ∈ X ∧ y i ∈ Y ∧ z i ∈ Z) := by
    rintro ⟨hx, hy, hz⟩
    simpa [h] using mem_triangles.2 ⟨hx, hy, hz, hsum i⟩
  simp [potential, hout, h, Real.zero_rpow hη]
private lemma card_triangles_pos_of_potential_le [Nonempty ι] (hsum : ∀ i, x i + y i + z i = 0)
    (hxX : ∀ i, x i ∈ X) (hyY : ∀ i, y i ∈ Y) (hzZ : ∀ i, z i ∈ Z) (hη : η ≠ 0)
    (h : potential x y z (Fintype.card ι / (2 * #(triangles X Y Z) ^ η)) η (X', Y', Z') ≤
      potential x y z (Fintype.card ι / (2 * #(triangles X Y Z) ^ η)) η (X, Y, Z)) :
    0 < #(triangles X' Y' Z') := by
  have hD := card_triangles_pos hxX hyY hzZ hsum
  rw [card_pos, nonempty_iff_ne_empty]
  intro hT
  rw [potential_eq_card_of_triangles_eq_empty hsum hη hT, potential_eq_mul_rpow hxX hyY hzZ] at h
  field_simp at h
  linarith [(by positivity : (0 : ℝ) < Fintype.card ι)]
variable {p : ℕ} [Fact p.Prime] [Module (ZMod p) V] [Fintype V]
end ArithmeticTriangleRemovalInVectorSpaces
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset Function Submodule
open ArithmeticTriangleRemovalInVectorSpaces
variable {V ι : Type*} [AddCommGroup V] [DecidableEq V] [Fintype ι] {x y z : ι → V}
variable {A η : ℝ} {X Y Z X' Y' Z' : Finset V} {v : V}
variable {p : ℕ} [Fact p.Prime] [Module (ZMod p) V] [Fintype V]
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution
    (hli : ∀ x y z, (x, y, z) ∈ triangles X Y Z → LinearIndependent (ZMod p) ![x, y])
    (hspan : ∀ x y z, (x, y, z) ∈ triangles X Y Z → ∀ x' y' z', (x', y', z') ∈ triangles X Y Z →
      x' ∈ span (ZMod p) {x, y} → y' ∈ span (ZMod p) {x, y} → x' = x ∧ y' = y)
    (hx : Injective x) (hy : Injective y) (hz : Injective z) (hxX : ∀ i, x i ∈ X)
    (hyY : ∀ i, y i ∈ Y) (hzZ : ∀ i, z i ∈ Z) (hsum : ∀ i, x i + y i + z i = 0) :
    (c p / (1 + c p) * Fintype.card ι / 2) ^ (1 + c p) ≤
      125 * p ^ 2 * Fintype.card V ^ (1 - c p) * #(triangles X Y Z) ^ c p := by
  have hc := c_pos (Fact.out : p.Prime).two_le
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [Fintype.card_eq_zero, Nat.cast_zero, mul_zero, zero_div,
      Real.zero_rpow (by linarith : 1 + c p ≠ 0)]
    positivity
  have hD := card_triangles_pos hxX hyY hzZ hsum
  have hA : 0 < (Fintype.card ι : ℝ) / (2 * #(triangles X Y Z) ^ (c p / (1 + c p))) := by
    positivity
  obtain ⟨⟨X', Y', Z'⟩, hS, hmin⟩ := exists_min_image (X.powerset ×ˢ Y.powerset ×ˢ Z.powerset)
    (potential x y z ((Fintype.card ι : ℝ) / (2 * #(triangles X Y Z) ^ (c p / (1 + c p))))
      (c p / (1 + c p))) ⟨(X, Y, Z), by simp⟩
  obtain ⟨hX', hY', hZ'⟩ : X' ⊆ X ∧ Y' ⊆ Y ∧ Z' ⊆ Z := by simpa using hS
  have hη₁ : c p / (1 + c p) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  refine rpow_le_mul_rpow_mul_rpow_of_le hc (by positivity) (by positivity)
    (Nat.cast_pos.2 (card_triangles_pos_of_potential_le hsum hxX hyY hzZ (by positivity)
      (hmin _ (by simp)))) (by positivity) ?_
  refine card_triangles_le_of_degree_le
    (fun a b c ht ↦ hli a b c (triangles_mono hX' hY' hZ' ht))
    (fun a b c ht a' b' c' ht' ↦ hspan a b c (triangles_mono hX' hY' hZ' ht) a' b' c'
      (triangles_mono hX' hY' hZ' ht')) ?_ ?_ ?_
  · intro v
    rw [div_mul_cancel₀ _ (by positivity)]
    exact card_filter_fst_le_of_potential_le hx hA (by positivity) hη₁
      (hmin _ (by simp [hY', hZ', (erase_subset v X').trans hX']))
  · intro v
    rw [div_mul_cancel₀ _ (by positivity)]
    exact card_filter_snd_le_of_potential_le hy hA (by positivity) hη₁
      (hmin _ (by simp [hX', hZ', (erase_subset v Y').trans hY']))
  · intro v
    rw [div_mul_cancel₀ _ (by positivity)]
    exact card_filter_thd_le_of_potential_le hz hA (by positivity) hη₁
      (hmin _ (by simp [hX', hY', (erase_subset v Z').trans hZ']))
end ArithmeticTriangleRemovalInVectorSpaces
