-- Prove2me | solution 1 for AaronsonAmbainis.cs_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:21:20.833461+00:00
-- url     : https://prove2.me/submissions/9e9b1dc1-4bc1-4a8e-bb9f-2732adc7829f

import Mathlib
import Definitions.Def_AaronsonAmbainis_TwoSided_CauchySchwarz
import Theorems.Thm_AaronsonAmbainis_sum_mul_rows
import Theorems.Thm_AaronsonAmbainis_pair_cs
import Theorems.Thm_AaronsonAmbainis_weight_choice
import Theorems.Thm_AaronsonAmbainis_le_of_sq_le_mul

set_option autoImplicit true
open AaronsonAmbainis
open Finset
namespace AaronsonAmbainis
theorem _root_.solution {α β ι : Type*} [Fintype ι] (O : Finset α) (N : Finset β)
    (a : α → ι → ℝ) (b : β → ι → ℝ) (ha : ∀ x j, 0 ≤ a x j) (hb : ∀ y j, 0 ≤ b y j)
    (u : α → ℝ) (v : β → ℝ)
    (hua : ∀ x, u x ^ 2 * ∑ j, a x j = u x) (hvb : ∀ y, v y ^ 2 * ∑ j, b y j = v y)
    (D : α → β → Finset ι) (C : ℝ) (hC : 0 ≤ C)
    (hpos : ∀ x ∈ O, ∀ y ∈ N, ∀ w : ι → ℝ, (∀ j, 0 < w j) →
      0 < ∑ j ∈ D x y, w j * a x j * b y j)
    (hpairs : ∀ w : ι → ℝ, (∀ j, 0 < w j) →
      ∑ x ∈ O, ∑ y ∈ N, (∑ j ∈ D x y, w j * a x j * b y j)⁻¹ ≤ C * ∑ j, (w j)⁻¹) :
    (∑ x ∈ O, u x) * (∑ y ∈ N, v y) ≤ C := by
  have hX : ∀ j, 0 ≤ ∑ x ∈ O, u x ^ 2 * a x j := fun j =>
    Finset.sum_nonneg fun x _ => mul_nonneg (sq_nonneg _) (ha x j)
  have hY : ∀ j, 0 ≤ ∑ y ∈ N, v y ^ 2 * b y j := fun j =>
    Finset.sum_nonneg fun y _ => mul_nonneg (sq_nonneg _) (hb y j)
  have hXsum : ∑ j, ∑ x ∈ O, u x ^ 2 * a x j = ∑ x ∈ O, u x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Finset.mul_sum, hua x]
  have hYsum : ∑ j, ∑ y ∈ N, v y ^ 2 * b y j = ∑ y ∈ N, v y := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [← Finset.mul_sum, hvb y]
  -- Cauchy–Schwarz over pairs, for every weight vector
  have hB : ∀ w : ι → ℝ, (∀ j, 0 < w j) →
      ((∑ x ∈ O, u x) * (∑ y ∈ N, v y)) ^ 2
        ≤ (∑ j, w j * (∑ x ∈ O, u x ^ 2 * a x j) * (∑ y ∈ N, v y ^ 2 * b y j))
          * (C * ∑ j, (w j)⁻¹) := by
    intro w hw
    have h1 := pair_cs O N (fun x y => u x * v y)
      (fun x y => ∑ j ∈ D x y, w j * a x j * b y j) (fun x hx y hy => hpos x hx y hy w hw)
    have h2 : ∑ x ∈ O, ∑ y ∈ N, (u x * v y) ^ 2 * ∑ j ∈ D x y, w j * a x j * b y j
        ≤ ∑ j, w j * (∑ x ∈ O, u x ^ 2 * a x j) * (∑ y ∈ N, v y ^ 2 * b y j) := by
      rw [sum_mul_rows O N w (fun x => u x ^ 2) (fun y => v y ^ 2) a b]
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => mul_nonneg (mul_nonneg (hw j).le (ha x j)) (hb y j)))
        (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    have h3 : 0 ≤ ∑ x ∈ O, ∑ y ∈ N, (∑ j ∈ D x y, w j * a x j * b y j)⁻¹ :=
      Finset.sum_nonneg fun x hx => Finset.sum_nonneg fun y hy =>
        (inv_pos.mpr (hpos x hx y hy w hw)).le
    have h4 : 0 ≤ ∑ j, w j * (∑ x ∈ O, u x ^ 2 * a x j) * (∑ y ∈ N, v y ^ 2 * b y j) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (hw j).le (hX j)) (hY j)
    calc ((∑ x ∈ O, u x) * (∑ y ∈ N, v y)) ^ 2
        = (∑ x ∈ O, ∑ y ∈ N, u x * v y) ^ 2 := by rw [Finset.sum_mul_sum]
      _ ≤ (∑ x ∈ O, ∑ y ∈ N, (u x * v y) ^ 2 * ∑ j ∈ D x y, w j * a x j * b y j)
          * (∑ x ∈ O, ∑ y ∈ N, (∑ j ∈ D x y, w j * a x j * b y j)⁻¹) := h1
      _ ≤ (∑ j, w j * (∑ x ∈ O, u x ^ 2 * a x j) * (∑ y ∈ N, v y ^ 2 * b y j))
          * (C * ∑ j, (w j)⁻¹) := mul_le_mul h2 (hpairs w hw) h3 h4
  -- the choice of the weights
  have hW := weight_choice (fun j => ∑ x ∈ O, u x ^ 2 * a x j)
    (fun j => ∑ y ∈ N, v y ^ 2 * b y j) hX hY C
    (((∑ x ∈ O, u x) * (∑ y ∈ N, v y)) ^ 2) hC hB
  -- Cauchy–Schwarz over the coordinates
  have hCS : (∑ j, Real.sqrt ((∑ x ∈ O, u x ^ 2 * a x j) * (∑ y ∈ N, v y ^ 2 * b y j))) ^ 2
      ≤ (∑ j, ∑ x ∈ O, u x ^ 2 * a x j) * (∑ j, ∑ y ∈ N, v y ^ 2 * b y j) :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ (fun j _ => hX j) (fun j _ => hY j)
      (fun j _ => (Real.sq_sqrt (mul_nonneg (hX j) (hY j))).le)
  rw [hXsum, hYsum] at hCS
  exact le_of_sq_le_mul hC (le_trans hW (mul_le_mul_of_nonneg_left hCS hC))
end AaronsonAmbainis
