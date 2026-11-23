-- Prove2me | solution 1 for Automata.pair_path_fin_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:30:56.741915+00:00
-- url     : https://prove2.me/submissions/d03868aa-5706-41cc-8651-f3bd15a02bf7

import Definitions.Def_AutomataTheory_Automata_Hist
import Definitions.Def_AutomataTheory_Languages_RegLang
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Pair

set_option autoImplicit true
open Function Set Filter Stream'
attribute [local implicit_reducible] Stream'
open Automata
attribute [local instance_reducible] NA.addHist
variable {A : Type}
variable {M : NA A} {acc : Set M.State}
attribute [local instance_reducible] NA.SingleInit
namespace Automata
theorem _root_.solution [Inhabited A] {s s' : M.State} {al : List A} {ss : Stream' M.State} :
    M.PairPath s s' al ss ↔ (M.SingleInit s).FinRun al.length al.padDefault ss ∧ ss al.length = s' := by
  constructor
  · rintro ⟨rfl, rfl, h_next⟩
    simp +instances [Function.comp_apply, NA.FinRun, NA.SingleInit, List.padDefault]
    intro k h_k ; simp +instances [Function.comp_apply, h_k, h_next]
  · rintro ⟨⟨h_init, h_next⟩, rfl⟩
    simp +instances [Function.comp_apply, NA.SingleInit] at h_init h_next
    simp +instances [Function.comp_apply, NA.PairPath, h_init]
    intro k h_k ; specialize h_next k h_k
    simp +instances [Function.comp_apply, List.padDefault, h_k] at h_next ; exact h_next
end Automata
