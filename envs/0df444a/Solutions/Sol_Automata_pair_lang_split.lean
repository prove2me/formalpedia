-- Prove2me | solution 1 for Automata.pair_lang_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:45:13.765471+00:00
-- url     : https://prove2.me/submissions/f89f4996-fdf7-4381-85e2-0ded0c6677fb

import Definitions.Def_AutomataTheory_Automata_Hist
import Definitions.Def_AutomataTheory_Languages_RegLang
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Pair
import Theorems.Thm_Automata_pair_path_split

set_option autoImplicit true
open Function Set Filter Stream'
attribute [local implicit_reducible] Stream'
open Automata
attribute [local instance_reducible] NA.addHist
variable {A : Type}
variable {M : NA A} {acc : Set M.State}
namespace Automata
theorem _root_.solution {s s' : M.State} {al0 al1 : List A}
    (h : al0 ++ al1 ∈ M.PairLang s s') : ∃ t, al0 ∈ M.PairLang s t ∧ al1 ∈ M.PairLang t s' := by
  obtain ⟨ss, h_path⟩ := h
  have ⟨h_path0, h_path1⟩ := pair_path_split h_path
  use (ss al0.length) ; constructor
  · use ss
  · use (ss.drop al0.length)
end Automata
