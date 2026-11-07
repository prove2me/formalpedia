-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.twoSided_iff_printed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:32:34.082765+00:00
-- url     : https://prove2.me/submissions/f626bdb3-e22d-4499-9ccc-ced9e02de320

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
import Definitions.Def_AaronsonAmbainis_Bridge_PaperInequalities
import Theorems.Thm_AaronsonAmbainis_Bridge_infl_nonneg
import Theorems.Thm_AaronsonAmbainis_Bridge_nonempty_of_ne


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution : TwoSidedInequality ↔ TwoSidedPrinted := by
  constructor
  · intro h ι _ _ hne g _ lam hrow
    have hτ0 : 0 ≤ Finset.univ.sup' Finset.univ_nonempty (fun j => infl g j) := by
      obtain ⟨j⟩ := hne
      exact (infl_nonneg g j).trans (Finset.le_sup' (fun j => infl g j) (Finset.mem_univ j))
    have h1 := h ι g lam hrow _ hτ0
      (fun j => Finset.le_sup' (fun j => infl g j) (Finset.mem_univ j))
    rw [Finset.sum_filter, Finset.sum_filter] at h1
    simp only [one_div]
    exact h1
  · intro h ι _ _ g lam hrow τ hτ hinfl
    by_cases hnc : ∃ x y, g x ≠ g y
    · obtain ⟨x, y, hxy⟩ := hnc
      have : Nonempty ι := nonempty_of_ne hxy
      have h1 := h ι g ⟨x, y, hxy⟩ lam hrow
      simp only [one_div] at h1
      rw [Finset.sum_filter, Finset.sum_filter]
      exact h1.trans ((Finset.sup'_le_iff _ _).mpr (fun j _ => hinfl j))
    · have hconst : ∀ x y, g x = g y := by
        intro x y
        by_contra hxy
        exact hnc ⟨x, y, hxy⟩
      have hz : (∑ x ∈ univ.filter (fun x : Cube ι => g x = true), (∑ j, lam x j)⁻¹) = 0 ∨
          (∑ x ∈ univ.filter (fun x : Cube ι => g x = false), (∑ j, lam x j)⁻¹) = 0 := by
        cases h0 : g (fun _ => false)
        · left
          apply Finset.sum_eq_zero
          intro x hx
          exfalso
          have hx' : g x = true := (Finset.mem_filter.mp hx).2
          rw [hconst x (fun _ => false), h0] at hx'
          exact Bool.noConfusion hx'
        · right
          apply Finset.sum_eq_zero
          intro x hx
          exfalso
          have hx' : g x = false := (Finset.mem_filter.mp hx).2
          rw [hconst x (fun _ => false), h0] at hx'
          exact Bool.noConfusion hx'
      rcases hz with hz | hz
      · rw [hz, zero_div, mul_zero, zero_mul]
        exact hτ
      · rw [hz, zero_div, mul_zero]
        exact hτ
end AaronsonAmbainis.Bridge
