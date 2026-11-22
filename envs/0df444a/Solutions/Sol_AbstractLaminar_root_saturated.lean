-- Prove2me | solution 1 for AbstractLaminar.root_saturated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:33:47.085977+00:00
-- url     : https://prove2.me/submissions/d25dd95a-a2e4-46ed-984d-6f302f866738

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
public import Theorems.Thm_AbstractLaminar_N_split
public import Theorems.Thm_AbstractLaminar_Sstrict_card_eq_sum
public import Theorems.Thm_AbstractLaminar_crux
public import Theorems.Thm_AbstractLaminar_master
public import Theorems.Thm_AbstractLaminar_root_self_props
public import Theorems.Thm_AbstractLaminar_roots_width_sum_le
public import Theorems.Thm_AbstractLaminar_topEdges_card_le


set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open AbstractLaminar
variable {ι : Type*} [DecidableEq ι]
variable (fam : Family ι)
namespace AbstractLaminar
theorem _root_.solution {a b : ℕ} (hsat : N fam a b = b - a) :
    ∀ r ∈ Roots fam a b, N fam (fam.lo r) (fam.hi r) = fam.hi r - fam.lo r := by
  -- The master chain, but tracking equality.
  rcases Nat.lt_or_ge a b with hab | hba
  · -- termwise bound N(lo r, hi r) ≤ hi r - lo r
    have hterm : ∀ r ∈ Roots fam a b, N fam (fam.lo r) (fam.hi r) ≤ fam.hi r - fam.lo r := by
      intro r _; exact master fam _ _
    -- ∑ N(lo r, hi r) = #Sstrict (forest decomposition)
    have hSstrict := Sstrict_card_eq_sum fam (a := a) (b := b)
    -- N = #top + #Sstrict
    have hNsplit := N_split fam (a := a) (b := b)
    have htle := topEdges_card_le fam (a := a) (b := b)
    have hwidth := roots_width_sum_le fam (a := a) (b := b)
    -- Show ∑ N(lo r, hi r) = ∑ (hi r - lo r), then conclude pointwise.
    have hsumeq : (∑ r ∈ Roots fam a b, N fam (fam.lo r) (fam.hi r))
        = ∑ r ∈ Roots fam a b, (fam.hi r - fam.lo r) := by
      -- ≤ direction is termwise.
      have hle : (∑ r ∈ Roots fam a b, N fam (fam.lo r) (fam.hi r))
          ≤ ∑ r ∈ Roots fam a b, (fam.hi r - fam.lo r) := Finset.sum_le_sum hterm
      -- Now lower bound ∑ N(lo r,hi r) using the saturation.
      rcases Finset.eq_empty_or_nonempty (topEdges fam a b) with htop | htop
      · -- no top edge: #Sstrict = N = b - a, and ∑(hi-lo) ≤ b-a.
        rw [htop, Finset.card_empty] at hNsplit
        -- hNsplit : N = 0 + #Sstrict
        have : (∑ r ∈ Roots fam a b, N fam (fam.lo r) (fam.hi r)) = b - a := by
          rw [← hSstrict]; omega
        omega
      · -- top edge present: crux gives ∑(hi-lo) ≤ b-a-1, #top = 1, #Sstrict = N - 1.
        have hcrux := crux fam hab htop
        have htpos : 1 ≤ (topEdges fam a b).card := Finset.card_pos.mpr htop
        have htone : (topEdges fam a b).card = 1 := le_antisymm htle htpos
        have : (∑ r ∈ Roots fam a b, N fam (fam.lo r) (fam.hi r)) = b - a - 1 := by
          rw [← hSstrict]; omega
        omega
    -- pointwise equality.
    exact (Finset.sum_eq_sum_iff_of_le hterm).mp hsumeq
  · -- empty window
    intro r hr
    obtain ⟨hrE, hra, hrb, hrs⟩ := root_self_props fam hr
    -- if b ≤ a then there are no roots (window empty) — contradiction or vacuous.
    have hlh := fam.lh r hrE
    omega
end AbstractLaminar
