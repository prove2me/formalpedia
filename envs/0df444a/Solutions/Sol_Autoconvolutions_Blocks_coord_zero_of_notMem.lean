-- Prove2me | solution 1 for Autoconvolutions.Blocks.coord_zero_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:50:02.722953+00:00
-- url     : https://prove2.me/submissions/8213ffb4-c486-4b54-8c24-1fe3f633a9ac

module
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring
public import Definitions.Def_Autoconvolutions_BlockKeys

set_option autoImplicit true
@[expose] public section
public section
open Autoconvolutions Autoconvolutions.Blocks
open Finset
namespace Autoconvolutions.Blocks
theorem _root_.solution {m k : ℕ} {I : Finset (Fin m)} {a : Fin m → ℕ}
    (ha : a ∈ I.piAntidiag k) {i : Fin m} (hi : i ∉ I) : a i = 0 := by
  by_contra h
  exact hi ((Finset.mem_piAntidiag.mp ha).2 i h)
end Autoconvolutions.Blocks
