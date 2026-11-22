-- Prove2me | solution 1 for AbstractLaminar.root_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:29:26.457787+00:00
-- url     : https://prove2.me/submissions/25a38e66-899d-48f4-9902-16270fa1cf9a

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
public import Theorems.Thm_AbstractLaminar_rootS_maximal
public import Theorems.Thm_AbstractLaminar_mem_Roots
public import Theorems.Thm_AbstractLaminar_root_self_props

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
    {g : ι} (hg : g ∈ fam.E)
    (h1 : fam.lo r ≤ fam.lo g) (h2 : fam.hi g ≤ fam.hi r)
    (h1' : fam.lo r' ≤ fam.lo g) (h2' : fam.hi g ≤ fam.hi r') :
    r = r' := by
  obtain ⟨hrE, hra, hrb, hrs⟩ := root_self_props fam hr
  obtain ⟨hr'E, hr'a, hr'b, hr's⟩ := root_self_props fam hr'
  have hlg := fam.lh g hg
  have hov := overlap_imp_nested fam hrE hr'E (by omega) (by omega)
  rw [mem_Roots] at hr hr'
  have hrS : r ∈ Sstrict fam a b := hr.1
  have hr'S : r' ∈ Sstrict fam a b := hr'.1
  rcases hov with ⟨hle1, hle2⟩ | ⟨hle1, hle2⟩
  · have hmax := rootS_maximal fam hrS hr'S (g := r')
        (by rw [hr.2]; exact hle1) (by rw [hr.2]; exact hle2)
    rw [hr.2] at hmax
    exact fam.inj r hrE r' hr'E (by omega) (by omega)
  · have hmax := rootS_maximal fam hr'S hrS (g := r)
        (by rw [hr'.2]; exact hle1) (by rw [hr'.2]; exact hle2)
    rw [hr'.2] at hmax
    exact fam.inj r hrE r' hr'E (by omega) (by omega)
end AbstractLaminar
