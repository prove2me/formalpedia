-- Prove2me | solution 1 for AaronsonAmbainis.Dual.rowBoundPM_of_packing_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:44:53.431806+00:00
-- url     : https://prove2.me/submissions/923b4bfb-ecb4-45eb-bde2-26c759d9025a

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Dual_RowAux
import Theorems.Thm_AaronsonAmbainis_flipSet_diffSet
import Theorems.Thm_AaronsonAmbainis_flipSet_empty


set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
namespace AaronsonAmbainis.Dual
theorem _root_.solution : PackingBound → CoverDuality → RowBoundPM := by
  intro hPB hCD ι _ _ d f hf hdeg
  have key : ∀ x : Cube ι, ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧
      ∑ i, a i ≤ Real.pi ^ 2 * (d : ℝ) ^ 2 ∧
      ∀ S : Finset ι, |f x - f (flipSet x S)| ≤ ∑ i ∈ S, a i := by
    intro x
    refine hCD ι (fun S => |f x - f (flipSet x S)|) (Real.pi ^ 2 * (d : ℝ) ^ 2)
      (by positivity) ?_ ?_
    · -- `t ∅ = 0`
      rw [flipSet_empty, sub_self, abs_zero]
    · -- the hypothesis of `CoverDuality` is `PackingBound` at `x`
      intro κ hκ hpack
      exact hPB ι d f hf hdeg x κ hκ hpack
  choose a ha0 haK hacov using key
  refine ⟨a, ha0, haK, fun x y => ?_⟩
  have h := hacov x (diffSet x y)
  rwa [flipSet_diffSet] at h
end AaronsonAmbainis.Dual
