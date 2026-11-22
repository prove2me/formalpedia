-- Prove2me | solution 1 for AbstractLaminar.seam_of_adjacent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:10.783384+00:00
-- url     : https://prove2.me/submissions/aa403c67-c774-4b93-9809-f869ee066608

module
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
public import Theorems.Thm_AbstractLaminar_roots_interval_disjoint


set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open AbstractLaminar
variable {ι : Type*} [DecidableEq ι]
variable (fam : Family ι)
namespace AbstractLaminar
theorem _root_.solution {a b : ℕ} {r'' r : ι} (hr'' : r'' ∈ Roots fam a b) (hr : r ∈ Roots fam a b)
    {s : ℕ} (hs1 : fam.lo r'' < s) (hs2 : s ≤ fam.hi r'')
    (hrhi : s + 1 ≤ fam.hi r) (hadj : fam.lo r = s) : fam.hi r'' = s := by
  -- r'' covers s, r covers s+1; if hi r'' ≥ s+1, both Iocs contain s+1 (disjoint) ⇒ contra
  rcases roots_interval_disjoint fam hr'' hr (by
      intro h; rw [h] at hs1 hs2; omega) with hd | hd
  · omega
  · omega
end AbstractLaminar
