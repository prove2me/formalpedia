-- Prove2me | solution 1 for AbstractLaminar.mem_Roots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:26:42.678274+00:00
-- url     : https://prove2.me/submissions/39458a6b-5b87-462b-8c20-1112a539a8d6

module
public import Definitions.Def_LeanPool_CriticalPortraits_Core
public import Definitions.Def_LeanPool_CriticalPortraits_Portraits
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Forward

set_option autoImplicit true
@[expose] public section
public section
open AbstractLaminar
open Finset
variable {ι : Type*} [DecidableEq ι]
variable (fam : Family ι)
variable {a b : ℕ}
namespace AbstractLaminar
theorem _root_.solution {r : ι} : r ∈ Roots fam a b ↔ r ∈ Sstrict fam a b ∧ rootS fam a b r = r := by
  unfold Roots; rw [mem_filter]
end AbstractLaminar
