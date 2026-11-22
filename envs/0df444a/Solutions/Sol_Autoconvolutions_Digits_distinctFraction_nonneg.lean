-- Prove2me | solution 1 for Autoconvolutions.Digits.distinctFraction_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:48.345731+00:00
-- url     : https://prove2.me/submissions/f3636bce-e177-42e2-b686-f90062b7f21c

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
theorem _root_.solution (r k : ℕ) : 0 ≤ distinctFraction r k := by
  unfold distinctFraction
  positivity
end Autoconvolutions.Digits
