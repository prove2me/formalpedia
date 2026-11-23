-- Prove2me | solution 1 for Automata.pair_path_concat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:20:12.700887+00:00
-- url     : https://prove2.me/submissions/898ab1e2-9894-4d24-afc5-fd09da217177

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
namespace Automata
theorem _root_.solution {s s' t: M.State} {al0 al1 : List A} {ss0 ss1 : Stream' M.State}
    (h0 : M.PairPath s t al0 ss0) (h1 : M.PairPath t s' al1 ss1) :
    M.PairPath s s' (al0 ++ al1) (fun k ↦ if k < al0.length + 1 then ss0 k else ss1 (k - al0.length)) := by
  obtain ⟨rfl, rfl, h_next0⟩ := h0
  obtain ⟨h_s1, rfl, h_next1⟩ := h1
  simp +instances [Function.comp_apply, NA.PairPath] ; constructor
  · grind
  intro k h_k
  rcases (show k < al0.length ∨ k = al0.length ∨ k > al0.length by omega) with h_k' | h_k' | h_k'
  · grind
  · simp +instances [Function.comp_apply, h_k', ← h_s1]
    grind
  · specialize h_next1 (k - al0.length) (by omega)
    grind
end Automata
