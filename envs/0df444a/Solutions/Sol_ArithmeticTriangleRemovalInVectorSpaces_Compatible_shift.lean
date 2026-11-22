-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.Compatible.shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:10:57.465231+00:00
-- url     : https://prove2.me/submissions/2e46ccf2-5801-4f29-a4cf-0660cf56b2c2

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Basic
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mem_sumTriples
attribute [local simp] ArithmeticTriangleRemovalInVectorSpaces.mem_sumTriples
section
public section
open Finset
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {N : ℕ} {J J' : ℕ × ℕ × ℕ → ℝ} {g : ℕ × ℕ × ℕ → ℕ} {π₁ π₂ π₃ π₁' π₂' π₃' : ℕ → ℝ}
private lemma marginal_shiftThird (d k : ℕ) :
    marginal (N + d) (shiftThird d J) g k =
      ∑ x ∈ sumTriples N with g (x + (0, 0, d)) = k, J x := by
  rw [marginal, ← sum_filter_of_ne (p := fun (_, _, c) ↦ d ≤ c), filter_filter]
  · refine sum_nbij' (· - (0, 0, d)) (· + (0, 0, d)) ?_ ?_ ?_ ?_ ?_
    all_goals
      rintro ⟨a, b, c⟩ hx
      simp only [mem_filter, mem_sumTriples, Prod.mk_sub_mk, Prod.mk_add_mk, add_zero,
        tsub_zero] at hx ⊢
    · obtain ⟨h₁, rfl, h₃⟩ := hx
      rw [Nat.sub_add_cancel h₃]
      grind
    · grind
    · obtain ⟨-, -, h₃⟩ := hx
      rw [Nat.sub_add_cancel h₃]
    · simp
    · obtain ⟨-, -, h₃⟩ := hx
      simp [shiftThird, h₃]
  · rintro ⟨a, b, c⟩ - hne
    by_contra h
    simp [shiftThird, h] at hne
end ArithmeticTriangleRemovalInVectorSpaces
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ArithmeticTriangleRemovalInVectorSpaces
variable {N : ℕ} {J J' : ℕ × ℕ × ℕ → ℝ} {g : ℕ × ℕ × ℕ → ℕ} {π₁ π₂ π₃ π₁' π₂' π₃' : ℕ → ℝ}
namespace ArithmeticTriangleRemovalInVectorSpaces
namespace Compatible
theorem _root_.solution (h : Compatible N π₁ π₂ π₃) (d : ℕ) :
    Compatible (N + d) π₁ π₂ fun c ↦ if d ≤ c then π₃ (c - d) else 0 := by
  obtain ⟨J, hJ, rfl, rfl, rfl⟩ := h
  refine ⟨shiftThird d J, ?_, ?_, ?_, ?_⟩
  · rintro ⟨a, b, c⟩
    unfold shiftThird
    grind
  · ext k
    rw [marginal_shiftThird]
    rfl
  · ext k
    rw [marginal_shiftThird]
    rfl
  · ext k
    rw [marginal_shiftThird, marginal]
    by_cases hk : d ≤ k
    · simp only [hk, ↓reduceIte]
      congr 1
      ext ⟨a, b, c⟩
      simp only [mem_filter]
      grind
    · simp only [hk, ↓reduceIte]
      apply sum_eq_zero
      rintro ⟨a, b, c⟩ hx
      simp only [mem_filter] at hx
      grind
end Compatible
end ArithmeticTriangleRemovalInVectorSpaces
