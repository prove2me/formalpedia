-- Prove2me | solution 1 for Automata.pair_acc_lang_concat_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:45:40.710804+00:00
-- url     : https://prove2.me/submissions/7728a432-5866-40da-bb0c-ffe00020a772

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
    (h0 : al0 ∈ M.PairLang s t) (h1 : al1 ∈ M.PairAccLang acc t s') : al0 ++ al1 ∈ M.PairAccLang acc s s' := by
  obtain ⟨ss0, h_path0⟩ := h0
  obtain ⟨ss1, h_path1, n, h_n, h_acc⟩ := h1
  use (fun k ↦ if k < al0.length + 1 then ss0 k else ss1 (k - al0.length))
  constructor
  · exact pair_path_concat h_path0 h_path1
  · use (n + al0.length)
    simp +instances [Function.comp_apply, (show n + al0.length < al0.length + al1.length + 1 by omega)]
    rcases (show n > 0 ∨ n = 0 by omega) with h_n' | rfl
    · grind
    · obtain ⟨rfl⟩ := h_path1.1
      simp +instances [Function.comp_apply, h_path0.2.1, h_acc]
end Automata
