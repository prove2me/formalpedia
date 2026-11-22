-- Prove2me | solution 1 for AbstractLaminar.rootS_mem_Sstrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:27:16.304859+00:00
-- url     : https://prove2.me/submissions/0a829a0f-829c-4dce-9180-6e0a69253d67

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
theorem _root_.solution {f : ι} (hf : f ∈ Sstrict fam a b) : rootS fam a b f ∈ Sstrict fam a b := by
  have := rootS_mem_containersS fam hf; rw [mem_containersS] at this
  rw [mem_Sstrict]; exact this.1
end AbstractLaminar
