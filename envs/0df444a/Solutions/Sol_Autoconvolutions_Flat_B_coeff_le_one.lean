-- Prove2me | solution 1 for Autoconvolutions.Flat.B_coeff_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:54:36.257961+00:00
-- url     : https://prove2.me/submissions/05b8283b-f3be-4962-9e31-62a317211574

module
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Definitions.Def_Autoconvolutions_Flat
public import Theorems.Thm_Autoconvolutions_Flat_P_coeff_nonneg
public import Theorems.Thm_Autoconvolutions_Flat_P_flat
section
@[expose] public section
open Finset Polynomial
namespace Autoconvolutions.Flat
noncomputable section
private theorem geom_coeff (s h : ℕ) :
    (∑ j ∈ range (s+1), (X : Polynomial ℝ)^j).coeff h = if h ≤ s then 1 else 0 := by
  rw [Polynomial.finsetSum_coeff]
  simp [Polynomial.coeff_X_pow]
private theorem product_coeff_nonneg (i j h : ℕ) : 0 ≤ (P i * P j).coeff h := by
  rw [Polynomial.coeff_mul]
  exact Finset.sum_nonneg fun p _ => mul_nonneg (P_coeff_nonneg _ _) (P_coeff_nonneg _ _)
private theorem B_coeff_le_geom (K s h : ℕ) :
    (B K s).coeff h ≤ if h ≤ s then 1 else 0 := by
  rw [← geom_coeff, ← P_flat, B, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun p _ _ => product_coeff_nonneg _ _ _)
end
end Autoconvolutions.Flat
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset Polynomial
open Autoconvolutions Autoconvolutions.Flat
noncomputable section
namespace Autoconvolutions.Flat
theorem _root_.solution (K s h : ℕ) : (B K s).coeff h ≤ 1 := by
  apply (B_coeff_le_geom K s h).trans
  split <;> norm_num
end Autoconvolutions.Flat
