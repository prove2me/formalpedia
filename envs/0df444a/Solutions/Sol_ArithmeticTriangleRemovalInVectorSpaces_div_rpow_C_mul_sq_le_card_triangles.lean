-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.div_rpow_C_mul_sq_le_card_triangles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:21:48.17502+00:00
-- url     : https://prove2.me/submissions/ca0b2274-a9f2-47a9-a3ec-12f0f1f5f966

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Triangle_Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_Embedding
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_Pruning
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_TensorPower
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_TensorPower
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_c_pos
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_card_triangles_piFinset
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_card_triangles_pos
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_le_of_forall_pow_le_mul_pow
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mem_triangles
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_rpow_le_mul_card_rpow_mul_card_triangles_rpow
attribute [local simp] ArithmeticTriangleRemovalInVectorSpaces.mem_triangles


section
public section
open Finset Function
namespace ArithmeticTriangleRemovalInVectorSpaces
private lemma div_rpow_one_add_one_div_mul_sq_le {m N D c : ℝ} (hc : 0 < c) (hm : 0 ≤ m)
    (hN : 0 < N) (hD : 0 ≤ D) (h : m ^ (1 + c) ≤ N ^ (1 - c) * D ^ c) :
    (m / N) ^ (1 + 1 / c) * N ^ 2 ≤ D := by
  have h' := Real.rpow_le_rpow (by positivity) h (by positivity : 0 ≤ 1 / c)
  rw [← Real.rpow_mul hm, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hN.le,
    ← Real.rpow_mul hD, mul_one_div_cancel hc.ne', Real.rpow_one,
    (by grind : (1 + c) * (1 / c) = 1 + 1 / c), (by grind : (1 - c) * (1 / c) = 1 / c - 1),
    Real.rpow_sub hN, Real.rpow_one] at h'
  rw [Real.div_rpow hm hN.le, Real.rpow_add hN, Real.rpow_one]
  field_simp at h' ⊢
  linarith
variable {p : ℕ} [Fact p.Prime] {V ι : Type*} [AddCommGroup V] [Module (ZMod p) V] [Fintype V]
  [DecidableEq V] [Fintype ι] {x y z : ι → V} {X Y Z : Finset V}
private lemma rpow_le_mul_card_pow_rpow_mul_card_triangles_pow_rpow (hx : Injective x)
    (hy : Injective y)
    (hz : Injective z) (hxX : ∀ i, x i ∈ X) (hyY : ∀ i, y i ∈ Y) (hzZ : ∀ i, z i ∈ Z)
    (hsum : ∀ i, x i + y i + z i = 0) (k : ℕ) :
    (c p / (1 + c p) * Fintype.card ι ^ k / 2) ^ (1 + c p) ≤
      125 * p ^ 2 * (p ^ 2 * Fintype.card V ^ k) ^ (1 - c p) * (#(triangles X Y Z) ^ k) ^ c p := by
  have h := rpow_le_mul_card_rpow_mul_card_triangles_rpow (p := p)
    (X := Fintype.piFinset fun _ : Fin k ↦ X) (Y := Fintype.piFinset fun _ ↦ Y)
    (Z := Fintype.piFinset fun _ ↦ Z) hx.comp_left hy.comp_left hz.comp_left
    (fun I ↦ Fintype.mem_piFinset.2 fun t ↦ hxX (I t))
    (fun I ↦ Fintype.mem_piFinset.2 fun t ↦ hyY (I t))
    (fun I ↦ Fintype.mem_piFinset.2 fun t ↦ hzZ (I t)) (fun I ↦ funext fun t ↦ hsum (I t))
  rw [card_triangles_piFinset, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin] at h
  exact_mod_cast h
private lemma card_rpow_le_card_rpow_mul_card_triangles_rpow (hx : Injective x) (hy : Injective y)
    (hz : Injective z) (hxX : ∀ i, x i ∈ X) (hyY : ∀ i, y i ∈ Y) (hzZ : ∀ i, z i ∈ Z)
    (hsum : ∀ i, x i + y i + z i = 0) :
    (Fintype.card ι : ℝ) ^ (1 + c p) ≤
      Fintype.card V ^ (1 - c p) * #(triangles X Y Z) ^ c p := by
  have hc := c_pos (Fact.out : p.Prime).two_le
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [Fintype.card_eq_zero, Nat.cast_zero, Real.zero_rpow (by linarith : 1 + c p ≠ 0)]
    positivity
  have hD := card_triangles_pos hxX hyY hzZ hsum
  refine le_of_forall_pow_le_mul_pow (M := 125 * p ^ 2 * ((p : ℝ) ^ 2) ^ (1 - c p) /
    (c p / (1 + c p) / 2) ^ (1 + c p)) (by positivity) ?_
  intro k
  have h := rpow_le_mul_card_pow_rpow_mul_card_triangles_pow_rpow (p := p) hx hy hz hxX hyY hzZ
    hsum k
  rw [mul_div_right_comm, Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_pow_comm (Nat.cast_nonneg (Fintype.card ι)),
    ← Real.rpow_pow_comm (Nat.cast_nonneg (Fintype.card V)),
    ← Real.rpow_pow_comm (Nat.cast_nonneg #(triangles X Y Z))] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), mul_pow]
  linarith
end ArithmeticTriangleRemovalInVectorSpaces
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset Function
open ArithmeticTriangleRemovalInVectorSpaces
variable {p : ℕ} [Fact p.Prime] {V ι : Type*} [AddCommGroup V] [Module (ZMod p) V] [Fintype V]
  [DecidableEq V] [Fintype ι] {x y z : ι → V} {X Y Z : Finset V}
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution (hx : Injective x) (hy : Injective y)
    (hz : Injective z) (hxX : ∀ i, x i ∈ X) (hyY : ∀ i, y i ∈ Y) (hzZ : ∀ i, z i ∈ Z)
    (hsum : ∀ i, x i + y i + z i = 0) :
    ((Fintype.card ι : ℝ) / Fintype.card V) ^ C p * Fintype.card V ^ 2 ≤ #(triangles X Y Z) :=
  div_rpow_one_add_one_div_mul_sq_le (c_pos (Fact.out : p.Prime).two_le) (Nat.cast_nonneg _)
    (Nat.cast_pos.2 Fintype.card_pos) (Nat.cast_nonneg _)
    (card_rpow_le_card_rpow_mul_card_triangles_rpow hx hy hz hxX hyY hzZ hsum)
end ArithmeticTriangleRemovalInVectorSpaces
