-- Prove2me | solution 1 for AbstractLaminar.rootS_maximal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:46.547446+00:00
-- url     : https://prove2.me/submissions/8fa17f8a-bb12-429a-9f34-8b6f68839842

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
public import Theorems.Thm_AbstractLaminar_rootS_max
public import Theorems.Thm_AbstractLaminar_rootS_mem_E
public import Theorems.Thm_AbstractLaminar_rootS_contains

set_option autoImplicit true
@[expose] public section
public section
open AbstractLaminar
open Finset
variable {ι : Type*} [DecidableEq ι]
variable (fam : Family ι)
variable {a b : ℕ}
namespace AbstractLaminar
theorem _root_.solution {f : ι} (hf : f ∈ Sstrict fam a b)
    {g : ι} (hg : g ∈ Sstrict fam a b)
    (h1 : fam.lo g ≤ fam.lo (rootS fam a b f)) (h2 : fam.hi (rootS fam a b f) ≤ fam.hi g) :
    fam.lo g = fam.lo (rootS fam a b f) ∧ fam.hi g = fam.hi (rootS fam a b f) := by
  obtain ⟨hrlo, hrhi⟩ := rootS_contains fam hf
  have hgf : g ∈ containersS fam a b f := by
    rw [mem_containersS]
    rw [mem_Sstrict] at hg
    exact ⟨hg, le_trans h1 hrlo, le_trans hrhi h2⟩
  have hmax := rootS_max fam hf g hgf
  have hlhr := fam.lh (rootS fam a b f) (rootS_mem_E fam hf)
  omega
end AbstractLaminar
