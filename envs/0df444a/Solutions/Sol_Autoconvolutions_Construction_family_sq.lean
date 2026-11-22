-- Prove2me | solution 1 for Autoconvolutions.Construction.family_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:50:26.544034+00:00
-- url     : https://prove2.me/submissions/ca1717e3-4cd6-4a80-ba1e-2bc8f863244f

module
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Real.Basic
public import Definitions.Def_Autoconvolutions_Levels

set_option autoImplicit true
@[expose] public section
public section
open Finset Polynomial
open scoped BigOperators
open Autoconvolutions Autoconvolutions.Construction
namespace Autoconvolutions.Construction
theorem _root_.solution (P : ℕ → Polynomial ℝ) (U V : Polynomial ℝ) {n K : ℕ} (hK : K ≤ n) :
    family P U V n K ^ 2 = ∑ s ∈ range (2 * K + 1), level U V n s * block P K s := by
  classical
  let I := range (K + 1)
  let t (i : ℕ) := U ^ (n - i) * V ^ (n + i) * P i
  let S := I ×ˢ I
  have hmap : ∀ ij ∈ S, ij.1 + ij.2 ∈ range (2 * K + 1) := by
    intro ⟨i,j⟩ hij
    simp only [S, I, mem_product, mem_range] at hij ⊢
    omega
  have hfiber (s : ℕ) :
      S.filter (fun ij => ij.1 + ij.2 = s) =
        (antidiagonal s).filter (fun ij => ij.1 ≤ K ∧ ij.2 ≤ K) := by
    ext ⟨i,j⟩
    simp only [S, I, mem_filter, mem_product, mem_range, mem_antidiagonal]
    omega
  change (∑ i ∈ I, t i) ^ 2 = _
  rw [pow_two, Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_product' I I (fun i j => t i * t j)]
  change ∑ ij ∈ S, t ij.1 * t ij.2 = _
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply sum_congr rfl
  intro s _
  rw [hfiber, block, Finset.mul_sum]
  apply sum_congr rfl
  intro ⟨i,j⟩ hij
  simp only [mem_filter, mem_antidiagonal] at hij
  have hU : (n - i) + (n - j) = 2*n - s := by omega
  have hV : (n + i) + (n + j) = 2*n + s := by omega
  dsimp [t, level]
  rw [← hU, ← hV, pow_add, pow_add]
  ring
end Autoconvolutions.Construction
