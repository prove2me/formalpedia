-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.exists_lowest_le_bdry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:24:52.881334+00:00
-- url     : https://prove2.me/submissions/5c6d7c04-d74f-4265-9e40-4b9d116b8232

import Definitions.Def_AaronsonAmbainis_DetLow_Main
import Definitions.Def_AaronsonAmbainis_DetLow_Corollary
import Theorems.Thm_AaronsonAmbainis_DetLow_exists_isLowest
import Theorems.Thm_AaronsonAmbainis_DetLow_lowestBound


set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
namespace AaronsonAmbainis.DetLow
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool) :
    ∃ m : ι →₀ ℕ, IsLowest (agMatrix g).det m ∧ ∀ j, m j ≤ bdry g j := by
  obtain ⟨hne, hb⟩ := lowestBound ι g
  obtain ⟨m, hm⟩ := exists_isLowest _ hne
  exact ⟨m, hm, hb m hm⟩
end AaronsonAmbainis.DetLow
