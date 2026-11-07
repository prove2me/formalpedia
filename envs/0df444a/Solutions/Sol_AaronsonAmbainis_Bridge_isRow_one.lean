-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.isRow_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:27:01.828801+00:00
-- url     : https://prove2.me/submissions/2cc2a465-189d-4f81-b820-4f441ea132c1

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
import Theorems.Thm_AaronsonAmbainis_Bridge_flipSet_empty
import Theorems.Thm_AaronsonAmbainis_flipSet_empty


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (g : Cube ι → Bool) (x : Cube ι) : IsRow g x (fun _ => 1) := by
  refine ⟨fun _ => zero_le_one, fun S hS => ?_⟩
  have hne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, AaronsonAmbainis.Bridge.flipSet_empty] at hS
    exact hS rfl
  show (1 : ℝ) ≤ ∑ _j ∈ S, (1 : ℝ)
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast Finset.one_le_card.mpr hne
end AaronsonAmbainis.Bridge
