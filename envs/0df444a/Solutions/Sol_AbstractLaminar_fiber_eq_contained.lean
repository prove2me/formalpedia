-- Prove2me | solution 1 for AbstractLaminar.fiber_eq_contained
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:23.221548+00:00
-- url     : https://prove2.me/submissions/3155b556-24ac-4c74-9ab2-153a2932315b

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
public import Theorems.Thm_AbstractLaminar_rootS_contains
public import Theorems.Thm_AbstractLaminar_rootS_mem_Roots
public import Theorems.Thm_AbstractLaminar_root_self_props
public import Theorems.Thm_AbstractLaminar_root_unique

set_option autoImplicit true
@[expose] public section
public section
open AbstractLaminar
open Finset
variable {ι : Type*} [DecidableEq ι]
variable (fam : Family ι)
variable {a b : ℕ}
namespace AbstractLaminar
theorem _root_.solution {r : ι} (hr : r ∈ Roots fam a b) :
    (Sstrict fam a b).filter (fun g => rootS fam a b g = r) =
      contained fam (fam.lo r) (fam.hi r) := by
  obtain ⟨hrE, hra, hrb, hrs⟩ := root_self_props fam hr
  ext g
  rw [mem_filter, mem_Sstrict, mem_contained]
  constructor
  · rintro ⟨hgS, hgr⟩
    have hgSmem : g ∈ Sstrict fam a b := by rw [mem_Sstrict]; exact hgS
    have hcont := rootS_contains fam hgSmem
    rw [hgr] at hcont
    exact ⟨hgS.1.1, hcont.1, hcont.2⟩
  · rintro ⟨hgE, hglo, hghi⟩
    have hgwin : a ≤ fam.lo g ∧ fam.hi g ≤ b := ⟨le_trans hra hglo, le_trans hghi hrb⟩
    have hglh := fam.lh g hgE
    have hgstrict : fam.lo g ≠ a ∨ fam.hi g ≠ b := by
      rcases hrs with h | h
      · left; omega
      · right; omega
    have hgS : g ∈ Sstrict fam a b := by
      rw [mem_Sstrict]; exact ⟨⟨hgE, hgwin.1, hgwin.2⟩, hgstrict⟩
    refine ⟨⟨⟨hgE, hgwin.1, hgwin.2⟩, hgstrict⟩, ?_⟩
    have hrootg := rootS_mem_Roots fam hgS
    have hcontg := rootS_contains fam hgS
    exact root_unique fam hrootg hr hgE hcontg.1 hcontg.2 hglo hghi
end AbstractLaminar
