-- Prove2me | solution 1 for Automata.pair_acc_lang_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:45:19.870319+00:00
-- url     : https://prove2.me/submissions/24890606-0c31-46b1-aa5d-adca47945af5

import Definitions.Def_AutomataTheory_Automata_Hist
import Definitions.Def_AutomataTheory_Languages_RegLang
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Pair
import Theorems.Thm_Automata_pair_path_split
import Theorems.Thm_P2M_Stream__get_drop__05b839498f63


set_option autoImplicit true
open Function Set Filter Stream'
attribute [local implicit_reducible] Stream'
open Automata
attribute [local instance_reducible] NA.addHist
variable {A : Type}
variable {M : NA A} {acc : Set M.State}
namespace Automata
theorem _root_.solution {s s' : M.State} {al0 al1 : List A}
    (h : al0 ++ al1 ∈ M.PairAccLang acc s s') :
    ∃ t, (al0 ∈ M.PairAccLang acc s t ∧ al1 ∈ M.PairLang t s') ∨
         (al0 ∈ M.PairLang s t ∧ al1 ∈ M.PairAccLang acc t s') := by
  obtain ⟨ss, h_path, n, h_n, h_acc⟩ := h
  obtain ⟨h_path0, h_path1⟩ := pair_path_split h_path
  use (ss al0.length)
  rcases Classical.em (n < al0.length + 1) with h_n' | h_n'
  · left ; constructor
    · use ss ; simp +instances [Function.comp_apply, NA.PairAccPath, h_path0]
      exact ⟨n, by omega, h_acc⟩
    · use (ss.drop al0.length)
  · right ; constructor
    · use ss
    · use (ss.drop al0.length) ; simp +instances [Function.comp_apply, NA.PairAccPath, h_path1]
      use (n - al0.length) ; simp +instances [Function.comp_apply, get_drop']
      grind
end Automata
