-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.packingBound_iff_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:37:54.289199+00:00
-- url     : https://prove2.me/submissions/3ac9111d-dbd0-4931-bf71-d34455797b82

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
import Definitions.Def_AaronsonAmbainis_Bridge_PaperInequalities
import Theorems.Thm_AaronsonAmbainis_Bridge_flipSet_empty
import Theorems.Thm_AaronsonAmbainis_flipSet_empty


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution : PackingBound ↔ PackingBoundNonempty := by
  constructor
  · intro h ι _ _ d f hbd hdeg x κ hκ hpack
    have h1 := h ι d f hbd hdeg x (fun S => if S.Nonempty then κ S else 0)
      (fun S => by
        show 0 ≤ (if S.Nonempty then κ S else 0)
        split_ifs with hS
        · exact hκ S hS
        · exact le_refl 0)
      (fun i => by
        refine le_of_eq_of_le (Finset.sum_congr rfl fun S hS => ?_) (hpack i)
        have hS' : S.Nonempty := ⟨i, (Finset.mem_filter.mp hS).2⟩
        show (if S.Nonempty then κ S else 0) = κ S
        exact if_pos hS')
    rw [Finset.sum_filter]
    refine le_of_eq_of_le (Finset.sum_congr rfl fun S _ => ?_) h1
    show (if S.Nonempty then κ S * |f x - f (flipSet x S)| else 0)
      = (if S.Nonempty then κ S else 0) * |f x - f (flipSet x S)|
    split_ifs with hS
    · rfl
    · exact (zero_mul _).symm
  · intro h ι _ _ d f hbd hdeg x κ hκ hpack
    have h1 := h ι d f hbd hdeg x κ (fun S _ => hκ S) hpack
    refine le_of_eq_of_le ?_ h1
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S _
    split_ifs with hS
    · rfl
    · have hS' : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      rw [hS', AaronsonAmbainis.Bridge.flipSet_empty, sub_self, abs_zero, mul_zero]
end AaronsonAmbainis.Bridge
