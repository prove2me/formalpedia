-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.exists_isLowest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:20:27.026658+00:00
-- url     : https://prove2.me/submissions/6340d764-de73-4f9c-8b4b-e494d6503dab

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetLow_Unit

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
namespace AaronsonAmbainis.DetLow
theorem _root_.solution {ι : Type} [Fintype ι] (q : MvPolynomial ι ℤ) (hq : q ≠ 0) :
    ∃ m, IsLowest q m := by
  have hne : q.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hq (support_eq_empty.mp h)
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image q.support (fun m => ∑ i, m i) hne
  exact ⟨m, hm, hmin⟩
end AaronsonAmbainis.DetLow
