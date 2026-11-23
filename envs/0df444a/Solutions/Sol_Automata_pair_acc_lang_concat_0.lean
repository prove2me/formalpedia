-- Prove2me | solution 1 for Automata.pair_acc_lang_concat_0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:45:30.358807+00:00
-- url     : https://prove2.me/submissions/1b5f83a0-e909-4efc-bac5-b3151e780546

import Definitions.Def_AutomataTheory_Automata_Hist
import Definitions.Def_AutomataTheory_Languages_RegLang
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Pair
import Theorems.Thm_Automata_pair_path_concat

set_option autoImplicit true
open Function Set Filter Stream'
attribute [local implicit_reducible] Stream'
open Automata
attribute [local instance_reducible] NA.addHist
variable {A : Type}
variable {M : NA A} {acc : Set M.State}
namespace Automata
theorem _root_.solution {s s' t: M.State} {al0 al1 : List A}
    (h0 : al0 ∈ M.PairAccLang acc s t) (h1 : al1 ∈ M.PairLang t s') : al0 ++ al1 ∈ M.PairAccLang acc s s' := by
  obtain ⟨ss0, h_path0, n, h_n, h_acc⟩ := h0
  obtain ⟨ss1, h_path1⟩ := h1
  use (fun k ↦ if k < al0.length + 1 then ss0 k else ss1 (k - al0.length))
  constructor
  · exact pair_path_concat h_path0 h_path1
  · use n ; grind
end Automata
