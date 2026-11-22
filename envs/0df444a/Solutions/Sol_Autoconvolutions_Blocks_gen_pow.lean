-- Prove2me | solution 1 for Autoconvolutions.Blocks.gen_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:29.596403+00:00
-- url     : https://prove2.me/submissions/6d330064-bf6c-48ed-9825-5ad352c51a37

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
attribute [local simp] Autoconvolutions.Blocks.eval_gen_one

set_option autoImplicit true
@[expose] public section
public section
open Finset Polynomial
open scoped BigOperators
open Autoconvolutions Autoconvolutions.Blocks
namespace Autoconvolutions.Blocks
theorem _root_.solution {m : ℕ} (D : ℕ) (I : Finset (Fin m)) (u : ℕ) :
    (gen D I)^u = ∑ a ∈ I.piAntidiag u,
      monomial (D * code D a) (Nat.multinomial I a : ℝ) := by
  classical
  rw [gen, Finset.sum_pow_eq_sum_piAntidiag]
  apply Finset.sum_congr rfl
  intro a ha
  have he : (∑ i ∈ I, a i * D ^ i.val) = code D a := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    simp [(not_imp_comm.mp ((Finset.mem_piAntidiag.mp ha).2 i)) hi]
  simp_rw [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  have hsum : (∑ i ∈ I, (D * D ^ i.val) * a i) = D * code D a := by
    rw [← he, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hsum, ← Polynomial.C_eq_natCast, Polynomial.C_mul_X_pow_eq_monomial]
end Autoconvolutions.Blocks
