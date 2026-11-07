-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.antipodal_iff_onZone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:37:16.443384+00:00
-- url     : https://prove2.me/submissions/5e3251f9-0824-448c-96f5-01c2d3b04d3f

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
import Theorems.Thm_AaronsonAmbainis_Bridge_antipode_antipode
import Theorems.Thm_AaronsonAmbainis_Bridge_isRow_one
import Theorems.Thm_AaronsonAmbainis_Bridge_extendRows_pos
import Theorems.Thm_AaronsonAmbainis_Bridge_extendRows_neg

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution : AntipodalInequality ↔ AntipodalOnZone := by
  constructor
  · intro h ι _ _ g w hw lam hrow
    have hrow' : ∀ x, IsRow g x (extendRows g lam x) := by
      intro x
      by_cases hx : x ∈ zone g ∨ antipode x ∈ zone g
      · rw [extendRows_pos hx]
        rcases hx with hx | hx
        · exact (hrow x hx).1
        · have h2 := (hrow (antipode x) hx).2
          rw [antipode_antipode] at h2
          exact h2
      · rw [extendRows_neg hx]
        exact isRow_one g x
    have h1 := h ι g w hw (extendRows g lam) hrow'
    have e : ∑ u ∈ zone g, 1 / (∑ j, w j * lam u j * lam (antipode u) j)
        = ∑ u ∈ zone g,
            (∑ j, w j * extendRows g lam u j * extendRows g lam (antipode u) j)⁻¹ := by
      apply Finset.sum_congr rfl
      intro u hu
      have hu2 : antipode (antipode u) ∈ zone g := by
        rw [antipode_antipode]
        exact hu
      rw [extendRows_pos (Or.inl hu), extendRows_pos (Or.inr hu2), one_div]
    rw [e]
    exact h1
  · intro h ι _ _ g w hw lam hrow
    have h1 := h ι g w hw lam (fun u _ => ⟨hrow u, hrow (antipode u)⟩)
    simp only [one_div] at h1
    exact h1
end AaronsonAmbainis.Bridge
