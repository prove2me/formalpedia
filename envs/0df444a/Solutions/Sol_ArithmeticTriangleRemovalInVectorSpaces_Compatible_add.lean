-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.Compatible.add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:10:55.834709+00:00
-- url     : https://prove2.me/submissions/518b3d3a-f20a-4cce-96b0-20b67a722c03

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
private lemma marginal_add : marginal N (J + J') g = marginal N J g + marginal N J' g := by
  ext k
  simp [marginal, sum_add_distrib]
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
theorem _root_.solution (h : Compatible N π₁ π₂ π₃) (h' : Compatible N π₁' π₂' π₃') :
    Compatible N (π₁ + π₁') (π₂ + π₂') (π₃ + π₃') := by
  obtain ⟨J, hJ, rfl, rfl, rfl⟩ := h
  obtain ⟨J', hJ', rfl, rfl, rfl⟩ := h'
  exact ⟨J + J', fun x ↦ add_nonneg (hJ x) (hJ' x), marginal_add, marginal_add, marginal_add⟩
end Compatible
end ArithmeticTriangleRemovalInVectorSpaces
