-- Prove2me | solution 1 for Autoconvolutions.Blocks.expand_level
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:06.482657+00:00
-- url     : https://prove2.me/submissions/64256218-cb7a-4136-8c9e-d7c1bceffe8e

module
public import Definitions.Def_Autoconvolutions_BlockKeys
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Tactic.Ring
public import Definitions.Def_Autoconvolutions_BlockExpansion
public import Theorems.Thm_Autoconvolutions_Blocks_eval_gen_one
public import Theorems.Thm_Autoconvolutions_Blocks_gen_pow
attribute [local simp] Autoconvolutions.Blocks.eval_gen_one
section
@[expose] public section
open Finset Polynomial
open scoped BigOperators
namespace Autoconvolutions.Blocks
private theorem sum_monomials_below (B : Polynomial ℝ) (D : ℕ)
    (hB : ∀ h, D ≤ h → B.coeff h = 0) :
    B = ∑ h ∈ range D, monomial h (B.coeff h) := by
  classical
  calc
    B = ∑ h ∈ B.support, monomial h (B.coeff h) := B.as_sum_support
    _ = _ := by
      apply Finset.sum_subset
      · intro h hh
        exact mem_range.mpr (by_contra fun hn =>
          (Polynomial.mem_support_iff.mp hh) (hB h (Nat.le_of_not_gt hn)))
      · intro h _ hh
        simp [Polynomial.notMem_support_iff.mp hh]
end Autoconvolutions.Blocks
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset Polynomial
open scoped BigOperators
open Autoconvolutions Autoconvolutions.Blocks
namespace Autoconvolutions.Blocks
theorem _root_.solution {m : ℕ} (D : ℕ) (I J : Finset (Fin m)) (u v : ℕ)
    (B : Polynomial ℝ) (hB : ∀ h, D ≤ h → B.coeff h = 0) :
    (gen D I)^u * (gen D J)^v * B =
      ∑ t ∈ rows I J u v D, monomial (rowKey D t)
        ((Nat.multinomial I t.1.1 : ℝ) * (Nat.multinomial J t.1.2 : ℝ) * B.coeff t.2) := by
  classical
  rw [gen_pow, gen_pow]
  conv_lhs => rhs; rw [sum_monomials_below B D hB]
  simp only [rows, Finset.sum_product, Finset.sum_mul, Finset.mul_sum,
    Polynomial.monomial_mul_monomial, rowKey, key, Nat.mul_add]
  conv_lhs =>
    enter [2, h]
    rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, a]
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro h _
  rw [add_comm (D * code D a + D * code D b) h]
end Autoconvolutions.Blocks
