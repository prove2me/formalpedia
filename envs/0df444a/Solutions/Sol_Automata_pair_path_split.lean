-- Prove2me | solution 1 for Automata.pair_path_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:29:21.914308+00:00
-- url     : https://prove2.me/submissions/4c367048-af34-4467-8d8d-582362cbdb14

import Definitions.Def_AutomataTheory_Automata_Hist
import Definitions.Def_AutomataTheory_Languages_RegLang
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Pair
import Theorems.Thm_P2M_Stream__get_drop__05b839498f63


set_option autoImplicit true
open Function Set Filter Stream'
attribute [local implicit_reducible] Stream'
open Automata
attribute [local instance_reducible] NA.addHist
variable {A : Type}
variable {M : NA A} {acc : Set M.State}
namespace Automata
theorem _root_.solution {s s' : M.State} {al0 al1 : List A} {ss : Stream' M.State}
    (h : M.PairPath s s' (al0 ++ al1) ss) :
    M.PairPath s (ss al0.length) al0 ss ∧ M.PairPath (ss al0.length) s' al1 (ss.drop al0.length) := by
  obtain ⟨rfl, rfl, h_next⟩ := h
  constructor
  · simp +instances [Function.comp_apply, NA.PairPath]
    grind
  · simp +instances [Function.comp_apply, NA.PairPath, get_drop', Nat.add_comm]
    intro k h_k ; specialize h_next (al0.length + k) (by simpa)
    grind
end Automata
