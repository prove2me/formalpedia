-- Prove2me | solution 1 for Autoconvolutions.Digits.collision_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:24.152597+00:00
-- url     : https://prove2.me/submissions/d673a565-5497-4b0f-81bd-5a87b60ac7bc

module
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_Autoconvolutions_Digits
public import Theorems.Thm_Autoconvolutions_Digits_distinctFraction_le_one
public import Theorems.Thm_Autoconvolutions_Digits_distinctFraction_recurrence

set_option autoImplicit true
@[expose] public section
public section
open Autoconvolutions Autoconvolutions.Digits
namespace Autoconvolutions.Digits
theorem _root_.solution {r : ℕ} (hr : 0 < r) (k : ℕ) :
    2 * (r : ℝ) * (1 - distinctFraction r k) ≤ (k : ℝ)^2 := by
  induction k with
  | zero => simp [distinctFraction]
  | succ k ih =>
    have hdrop := distinctFraction_recurrence hr k
    have hk : (0 : ℝ) ≤ k := by positivity
    have hstep := mul_nonneg hk (sub_nonneg.mpr (distinctFraction_le_one hr k))
    push_cast
    nlinarith only [ih, hdrop, hstep]
end Autoconvolutions.Digits
