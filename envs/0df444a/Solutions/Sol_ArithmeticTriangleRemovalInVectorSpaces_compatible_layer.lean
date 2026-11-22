-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.compatible_layer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:11:51.729136+00:00
-- url     : https://prove2.me/submissions/461abc42-4a09-4be7-b098-1dfb1c3fcdcc

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Basic
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mem_sumTriples
attribute [local simp] ArithmeticTriangleRemovalInVectorSpaces.mem_sumTriples

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ArithmeticTriangleRemovalInVectorSpaces
variable {N : ℕ} {J J' : ℕ × ℕ × ℕ → ℝ} {g : ℕ × ℕ × ℕ → ℕ} {π₁ π₂ π₃ π₁' π₂' π₃' : ℕ → ℝ}
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k) :
    Compatible N (fun a ↦ if a = 0 then ∑ k ∈ range (N + 1), f k else 0)
      (fun b ↦ if b ≤ N then f b else 0) fun c ↦ if c ≤ N then f (N - c) else 0 := by
  refine ⟨fun (a, b, _) ↦ if a = 0 then f b else 0, ?_, ?_, ?_, ?_⟩
  · rintro ⟨a, b, c⟩
    grind
  · ext a
    simp only [marginal]
    by_cases ha : a = 0
    · simp only [ha, ↓reduceIte]
      subst ha
      refine sum_nbij' (fun (_, b, _) ↦ b) (fun b ↦ (0, b, N - b)) ?_ ?_ ?_ ?_ ?_
      · rintro ⟨a, b, c⟩ hx
        simp only [mem_filter, mem_sumTriples, mem_range] at hx ⊢
        grind
      · intro b hb
        simp only [mem_range] at hb
        simp only [mem_filter, mem_sumTriples]
        grind
      · rintro ⟨a, b, c⟩ hx
        simp only [mem_filter, mem_sumTriples] at hx
        grind
      · intro b _
        rfl
      · rintro ⟨a, b, c⟩ hx
        simp only [mem_filter, mem_sumTriples] at hx
        grind
    · simp only [ha, ↓reduceIte]
      apply sum_eq_zero
      rintro ⟨a', b, c⟩ hx
      simp only [mem_filter] at hx
      grind
  · ext b
    simp only [marginal]
    by_cases hb : b ≤ N
    · simp only [hb, ↓reduceIte]
      rw [sum_eq_single_of_mem (0, b, N - b) (by simp; grind)]
      · simp
      · rintro ⟨a, b', c⟩ hx hne
        simp only [mem_filter, mem_sumTriples] at hx
        grind
    · simp only [hb, ↓reduceIte]
      apply sum_eq_zero
      rintro ⟨a, b', c⟩ hx
      simp only [mem_filter, mem_sumTriples] at hx
      grind
  · ext c
    simp only [marginal]
    by_cases hc : c ≤ N
    · simp only [hc, ↓reduceIte]
      rw [sum_eq_single_of_mem (0, N - c, c) (by simp; grind)]
      · simp
      · rintro ⟨a, b, c'⟩ hx hne
        simp only [mem_filter, mem_sumTriples] at hx
        grind
    · simp only [hc, ↓reduceIte]
      apply sum_eq_zero
      rintro ⟨a, b, c'⟩ hx
      simp only [mem_filter, mem_sumTriples] at hx
      grind
end ArithmeticTriangleRemovalInVectorSpaces
