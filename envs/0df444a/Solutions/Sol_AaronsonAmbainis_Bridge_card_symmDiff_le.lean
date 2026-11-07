-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.card_symmDiff_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:21:27.256655+00:00
-- url     : https://prove2.me/submissions/d6d7a58f-daf3-49e9-97e8-fcba137be92e

import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Definitions.Def_AaronsonAmbainis_Bridge_Algebra

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (S T : Finset ι) : (symmDiff S T).card ≤ S.card + T.card := by
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le S T)
  intro i hi
  rw [Finset.mem_symmDiff] at hi
  rw [Finset.mem_union]
  rcases hi with ⟨h, _⟩ | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h
end AaronsonAmbainis.Bridge
