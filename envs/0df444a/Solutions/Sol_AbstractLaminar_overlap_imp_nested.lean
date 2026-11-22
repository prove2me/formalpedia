-- Prove2me | solution 1 for AbstractLaminar.overlap_imp_nested
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:27:05.849968+00:00
-- url     : https://prove2.me/submissions/bbfd6a45-7906-4d5d-8edf-cdbc8ff4d675

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
namespace AbstractLaminar
theorem _root_.solution {e f : ι} (he : e ∈ fam.E) (hf : f ∈ fam.E)
    (h1 : fam.lo e < fam.hi f) (h2 : fam.lo f < fam.hi e) :
    (fam.lo f ≤ fam.lo e ∧ fam.hi e ≤ fam.hi f) ∨
    (fam.lo e ≤ fam.lo f ∧ fam.hi f ≤ fam.hi e) := by
  have lam1 := fam.laminar e he f hf
  have lam2 := fam.laminar f hf e he
  omega
end AbstractLaminar
