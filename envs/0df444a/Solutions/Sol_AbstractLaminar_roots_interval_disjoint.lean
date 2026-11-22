-- Prove2me | solution 1 for AbstractLaminar.roots_interval_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:06.549638+00:00
-- url     : https://prove2.me/submissions/e1e8e25d-2c47-4f3d-97a9-345820fb069e

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
public import Theorems.Thm_AbstractLaminar_overlap_imp_nested
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
theorem _root_.solution {r r' : ι} (hr : r ∈ Roots fam a b) (hr' : r' ∈ Roots fam a b)
    (hne : r ≠ r') : fam.hi r ≤ fam.lo r' ∨ fam.hi r' ≤ fam.lo r := by
  by_contra hc
  rw [not_or] at hc
  obtain ⟨h1, h2⟩ := hc
  rw [not_le] at h1 h2
  obtain ⟨hrE, _, _, _⟩ := root_self_props fam hr
  obtain ⟨hr'E, _, _, _⟩ := root_self_props fam hr'
  have hov := overlap_imp_nested fam hrE hr'E (by omega) (by omega)
  rcases hov with ⟨hle1, hle2⟩ | ⟨hle1, hle2⟩
  · exact hne (root_unique fam hr hr' hrE (le_refl _) (le_refl _) hle1 hle2)
  · exact hne (root_unique fam hr hr' hr'E hle1 hle2 (le_refl _) (le_refl _))
end AbstractLaminar
