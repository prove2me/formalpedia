-- Prove2me | solution 1 for AaronsonAmbainis.Level.bdry_lev
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:38:45.750624+00:00
-- url     : https://prove2.me/submissions/1a6456a1-613e-4842-a227-c3e03add43d6

import Definitions.Def_AaronsonAmbainis_Level_Rows
import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Level_AllPairs

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution (f : Cube ι → ℝ) (t : ℝ) (j : ι) :
    (bdry (lev f t) j : ℝ)
      = ∑ x, if f (flipSet x {j}) ≤ t ∧ t < f x then (1 : ℝ) else 0 := by
  unfold bdry
  rw [Finset.natCast_card_filter]
  apply Finset.sum_congr rfl
  intro x _
  apply if_congr _ rfl rfl
  simp only [lev, decide_eq_true_eq, decide_eq_false_iff_not, not_lt]
  exact and_comm
end AaronsonAmbainis.Level
