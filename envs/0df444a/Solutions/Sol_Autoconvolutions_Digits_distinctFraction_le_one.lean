-- Prove2me | solution 1 for Autoconvolutions.Digits.distinctFraction_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:50:15.314391+00:00
-- url     : https://prove2.me/submissions/e7c244d5-ee67-4ae7-8039-db3664ff9f37

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
    distinctFraction r k ≤ 1 := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  apply (div_le_iff₀ (pow_pos hr' k)).2
  simpa only [one_mul, Nat.cast_pow] using
    (show (r.descFactorial k : ℝ) ≤ (r ^ k : ℕ) by exact_mod_cast Nat.descFactorial_le_pow r k)
end Autoconvolutions.Digits
