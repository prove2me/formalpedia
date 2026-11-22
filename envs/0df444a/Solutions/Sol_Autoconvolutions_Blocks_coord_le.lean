-- Prove2me | solution 1 for Autoconvolutions.Blocks.coord_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:26.464844+00:00
-- url     : https://prove2.me/submissions/0ae52630-8738-4cf8-a1b9-764d1087229c

module
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring
public import Definitions.Def_Autoconvolutions_BlockKeys
public import Theorems.Thm_Autoconvolutions_Blocks_coord_zero_of_notMem

set_option autoImplicit true
@[expose] public section
public section
open Autoconvolutions Autoconvolutions.Blocks
open Finset
namespace Autoconvolutions.Blocks
theorem _root_.solution {m k : ℕ} {I : Finset (Fin m)} {a : Fin m → ℕ}
    (ha : a ∈ I.piAntidiag k) (i : Fin m) : a i ≤ k := by
  by_cases hi : i ∈ I
  · rw [← (Finset.mem_piAntidiag.mp ha).1]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) hi
  · rw [coord_zero_of_notMem ha hi]
    exact Nat.zero_le _
end Autoconvolutions.Blocks
