-- Prove2me | solution 1 for Autoconvolutions.Parameters.factorialRatio_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:30.550806+00:00
-- url     : https://prove2.me/submissions/417a29fa-eafa-465d-8277-d10c6569d6a3

module
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_Autoconvolutions_Parameters
section
@[expose] public section
open Finset
namespace Autoconvolutions.Parameters
private theorem factorialRatio_succ {N j : ℕ} (hj : j < N) :
    factorialRatio N (j+1) =
      (((N : ℝ) - j) / (N+j+1)) * factorialRatio N j := by
  have h₁ : N-j = (N-(j+1))+1 := by omega
  have h₂ : N+(j+1) = (N+j)+1 := by omega
  have h₃ : ((N-(j+1) : ℕ) : ℝ) + 1 = N-j := by
    rw [Nat.cast_sub (by omega : j+1 ≤ N)]
    push_cast
    ring
  unfold factorialRatio
  rw [h₁, h₂, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  rw [h₃]
  have h₄ : (j : ℝ) < N := by exact_mod_cast hj
  have h₅ : (0 : ℝ) < (N-(j+1)).factorial := by positivity
  have h₆ : (0 : ℝ) < (N+j).factorial := by positivity
  field_simp
  all_goals simp [ne_of_gt (sub_pos.mpr h₄)]
end Autoconvolutions.Parameters
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Autoconvolutions Autoconvolutions.Parameters
namespace Autoconvolutions.Parameters
theorem _root_.solution {N j : ℕ} (hN : 0 < N) (hj : j ≤ N) :
    1 - (j : ℝ)^2 / N ≤ factorialRatio N j := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  induction j with
  | zero =>
    simp [factorialRatio, pow_two, (Nat.factorial_pos N).ne']
  | succ j ih =>
    have hj' : j < N := by omega
    have hjR : (j : ℝ) < N := by exact_mod_cast hj'
    have hj0 : (0 : ℝ) ≤ j := by positivity
    have hp : 0 ≤ ((N : ℝ)-j)/(N+j+1) := by positivity
    have hstep : 1 - ((j : ℝ)+1)^2 / N ≤
        (((N : ℝ)-j)/(N+j+1)) * (1-(j : ℝ)^2/N) := by
      have hden : (0 : ℝ) < N+j+1 := by positivity
      field_simp
      nlinarith [sq_nonneg (j : ℝ), mul_nonneg hj0 (sq_nonneg (j : ℝ))]
    rw [factorialRatio_succ hj', Nat.cast_succ]
    exact hstep.trans (mul_le_mul_of_nonneg_left (ih (by omega)) hp)
end Autoconvolutions.Parameters
