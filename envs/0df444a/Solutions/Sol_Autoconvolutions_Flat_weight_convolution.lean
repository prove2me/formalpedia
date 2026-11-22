-- Prove2me | solution 1 for Autoconvolutions.Flat.weight_convolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:50:50.954802+00:00
-- url     : https://prove2.me/submissions/2b6f29c4-7199-4415-8ab2-8d082b8cf7fb

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
section
@[expose] public section
open Finset Polynomial
namespace Autoconvolutions.Flat
noncomputable section
private theorem weight_succ (n : ℕ) :
    ((n : ℝ) + 1) * weight (n + 1) = ((n : ℝ) + 1 / 2) * weight n := by
  have h : ((n : ℝ) + 1) * (n + 1).centralBinom =
      2 * (2 * (n : ℝ) + 1) * n.centralBinom := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  unfold weight
  rw [pow_succ]
  field_simp
  linear_combination 2 * h
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
theorem _root_.solution (n : ℕ) :
    ∑ p ∈ antidiagonal n, weight p.1 * weight p.2 = 1 := by
  induction n with
  | zero => simp [weight]
  | succ n ih =>
    let L (p : ℕ × ℕ) := ((p.1 : ℝ) * weight p.1) * weight p.2
    let R (p : ℕ × ℕ) := weight p.1 * ((p.2 : ℝ) * weight p.2)
    have hL : ∑ p ∈ antidiagonal (n+1), L p =
        ∑ p ∈ antidiagonal n, (((p.1 : ℝ) + 1/2) * weight p.1) * weight p.2 := by
      rw [Finset.Nat.sum_antidiagonal_succ]
      simp [L, weight_succ]
    have hR : ∑ p ∈ antidiagonal (n+1), R p =
        ∑ p ∈ antidiagonal n, weight p.1 * (((p.2 : ℝ) + 1/2) * weight p.2) := by
      rw [Finset.Nat.sum_antidiagonal_succ']
      simp [R, weight_succ]
    have h : ((n : ℝ)+1) * (∑ p ∈ antidiagonal (n+1), weight p.1 * weight p.2) =
        ((n : ℝ)+1) * (∑ p ∈ antidiagonal n, weight p.1 * weight p.2) := by
      calc
        _ = ∑ p ∈ antidiagonal (n+1), (L p + R p) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          have e : (p.1 : ℝ) + p.2 = (n : ℝ) + 1 := by
            exact_mod_cast Finset.mem_antidiagonal.mp hp
          rw [← e]
          dsimp [L, R]
          ring
        _ = _ := by
          rw [Finset.sum_add_distrib, hL, hR, ← Finset.sum_add_distrib, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          have e : (p.1 : ℝ) + p.2 = n := by
            exact_mod_cast Finset.mem_antidiagonal.mp hp
          rw [← e]
          ring
    exact (mul_left_cancel₀ (by positivity : (n : ℝ) + 1 ≠ 0) h).trans ih
end Autoconvolutions.Flat
