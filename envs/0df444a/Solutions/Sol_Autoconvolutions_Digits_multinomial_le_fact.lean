-- Prove2me | solution 1 for Autoconvolutions.Digits.multinomial_le_fact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:33.512064+00:00
-- url     : https://prove2.me/submissions/55386067-6938-4c35-a053-f167183becb2

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
theorem _root_.solution {ι : Type*} (I : Finset ι) (a : ι → ℕ) :
    Nat.multinomial I a ≤ (∑ i ∈ I, a i).factorial := by
  exact Nat.div_le_self _ _
end Autoconvolutions.Digits
