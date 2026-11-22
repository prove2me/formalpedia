-- Prove2me | solution 1 for Autoconvolutions.Digits.distinctFraction_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:49.049795+00:00
-- url     : https://prove2.me/submissions/b248129a-2bb3-4041-9530-83b21eb764a8

module
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_Autoconvolutions_Digits

set_option autoImplicit true
@[expose] public section
public section
open Autoconvolutions Autoconvolutions.Digits
namespace Autoconvolutions.Digits
theorem _root_.solution {r : ℕ} (hr : 0 < r) (k : ℕ) :
    (r : ℝ) * distinctFraction r k =
      (r : ℝ) * distinctFraction r (k + 1) + (k : ℝ) * distinctFraction r k := by
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hrec : (r.descFactorial k : ℝ) * r =
      (r.descFactorial (k+1) : ℝ) + k * (r.descFactorial k : ℝ) := by
    by_cases hk : k ≤ r
    · rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hk]
      ring
    · have hz : r.descFactorial k = 0 :=
        Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge hk)
      simp [Nat.descFactorial_succ, hz]
  unfold distinctFraction
  calc
    _ = ((r.descFactorial (k+1) : ℝ) + k * (r.descFactorial k : ℝ)) / (r : ℝ)^k := by
      rw [← hrec]
      ring
    _ = _ := by
      rw [pow_succ]
      field_simp [hr']
end Autoconvolutions.Digits
