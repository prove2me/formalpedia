-- Prove2me | solution 1 for Autoconvolutions.Digits.multinomial_of_distinct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:47.673033+00:00
-- url     : https://prove2.me/submissions/97348188-2a5b-4ccb-bacc-c699bfa406ab

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
theorem _root_.solution {ι : Type*} (I : Finset ι) (a : ι → ℕ)
    (ha : ∀ i ∈ I, a i ≤ 1) :
    Nat.multinomial I a = (∑ i ∈ I, a i).factorial := by
  have hp : (∏ i ∈ I, (a i).factorial) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (ha i hi) with h | h <;> simp [h]
  simp [Nat.multinomial, hp]
end Autoconvolutions.Digits
