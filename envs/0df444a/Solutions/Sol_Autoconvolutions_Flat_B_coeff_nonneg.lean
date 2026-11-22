-- Prove2me | solution 1 for Autoconvolutions.Flat.B_coeff_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:54:32.964827+00:00
-- url     : https://prove2.me/submissions/61cc3334-89f6-4da0-95ad-665a61c7e35c

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
section
@[expose] public section
open Finset Polynomial
namespace Autoconvolutions.Flat
noncomputable section
private theorem product_coeff_nonneg (i j h : ℕ) : 0 ≤ (P i * P j).coeff h := by
  rw [Polynomial.coeff_mul]
  exact Finset.sum_nonneg fun p _ => mul_nonneg (P_coeff_nonneg _ _) (P_coeff_nonneg _ _)
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
theorem _root_.solution (K s h : ℕ) : 0 ≤ (B K s).coeff h := by
  rw [B, Polynomial.finsetSum_coeff]
  exact Finset.sum_nonneg fun p _ => product_coeff_nonneg _ _ _
end Autoconvolutions.Flat
