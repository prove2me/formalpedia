-- Prove2me | solution 1 for AbstractLaminar.rootS_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:27:55.390237+00:00
-- url     : https://prove2.me/submissions/1b02edec-b8b1-4b42-baa6-ca52d7809ee3

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
public import Theorems.Thm_AbstractLaminar_rootS_mem_containersS

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
    fam.lo (rootS fam a b f) ≠ a ∨ fam.hi (rootS fam a b f) ≠ b := by
  have := rootS_mem_containersS fam hf; rw [mem_containersS] at this; exact this.1.2
end AbstractLaminar
