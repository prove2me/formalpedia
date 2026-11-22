-- Prove2me | solution 1 for AbstractLaminar.rootS_width_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:46.108922+00:00
-- url     : https://prove2.me/submissions/b8504438-1461-4fed-a5fd-8c8342758de6

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
public import Theorems.Thm_AbstractLaminar_rootS_mem_E
public import Theorems.Thm_AbstractLaminar_rootS_window
public import Theorems.Thm_AbstractLaminar_rootS_strict

set_option autoImplicit true
@[expose] public section
public section
open AbstractLaminar
open Finset
variable {ι : Type*} [DecidableEq ι]
variable (fam : Family ι)
variable {a b : ℕ}
namespace AbstractLaminar
theorem _root_.solution {f : ι} (hf : f ∈ Sstrict fam a b) :
    fam.hi (rootS fam a b f) - fam.lo (rootS fam a b f) < b - a := by
  obtain ⟨hwlo, hwhi⟩ := rootS_window fam hf
  have hlh := fam.lh (rootS fam a b f) (rootS_mem_E fam hf)
  rcases rootS_strict fam hf with h | h <;> omega
end AbstractLaminar
