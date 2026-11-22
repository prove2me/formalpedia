-- Prove2me | solution 1 for AbstractLaminar.edge_tight_of_saturated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:34:23.552896+00:00
-- url     : https://prove2.me/submissions/adb1ee57-9b97-4ded-a25a-6427bfad996f

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
public import Theorems.Thm_AbstractLaminar_root_saturated
public import Theorems.Thm_AbstractLaminar_rootS_contains
public import Theorems.Thm_AbstractLaminar_rootS_mem_Roots
public import Theorems.Thm_AbstractLaminar_rootS_width_lt


set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open AbstractLaminar
variable {ι : Type*} [DecidableEq ι]
variable (fam : Family ι)
namespace AbstractLaminar
theorem _root_.solution :
    ∀ w : ℕ, ∀ a b : ℕ, b - a = w → N fam a b = b - a →
      ∀ e ∈ contained fam a b, N fam (fam.lo e) (fam.hi e) = fam.hi e - fam.lo e := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro a b hw hsat e he
    rw [mem_contained] at he
    obtain ⟨heE, hea, heb⟩ := he
    by_cases htop : fam.lo e = a ∧ fam.hi e = b
    · -- e is the top edge: its window IS the saturated window.
      rw [htop.1, htop.2]; rw [hsat]
    · -- e is strict; its root is saturated, and the root window is smaller.
      have heS : e ∈ Sstrict fam a b := by
        rw [mem_Sstrict]
        refine ⟨⟨heE, hea, heb⟩, ?_⟩
        rw [not_and_or] at htop; exact htop
      have hr := rootS_mem_Roots fam heS
      have hrsat := root_saturated fam hsat _ hr
      have hcont := rootS_contains fam heS
      -- e contained in (lo r, hi r)
      have hewin : e ∈ contained fam (fam.lo (rootS fam a b e)) (fam.hi (rootS fam a b e)) := by
        rw [mem_contained]; exact ⟨heE, hcont.1, hcont.2⟩
      -- root window width < w
      have hrwidth := rootS_width_lt fam heS
      exact ih (fam.hi (rootS fam a b e) - fam.lo (rootS fam a b e)) (by omega)
        (fam.lo (rootS fam a b e)) (fam.hi (rootS fam a b e)) rfl hrsat e hewin
end AbstractLaminar
