-- Prove2me | solution 1 for Automata.na_hist_fin_run_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:39:25.728347+00:00
-- url     : https://prove2.me/submissions/b0df8b32-aa5d-4f08-b078-824af7dc0df5

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Automata_Hist

set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
open Automata
variable {A H : Type}
attribute [local instance_reducible] NA.addHist
variable {M : NA A} {hist_init : Set H} {hist_next : M.State × H → A → Set H}
namespace Automata
theorem _root_.solution {n : ℕ} {as : Stream' A} {ss : Stream' M.State}
    (h_init : hist_init.Nonempty) (h_next : ∀ s a, (hist_next s a).Nonempty)
    (h : M.FinRun n as ss) : ∃ hs : Stream' H, (M.addHist hist_init hist_next).FinRun n as (fun k ↦ (ss k, hs k)) := by
  obtain ⟨hs0, h_hs0⟩ := h_init
  choose hs' h_hs' using h_next
  let hs := MakeHist as ss hs0 hs'
  use hs ; constructor
  · simp +instances [NA.addHist, MakeHist, h.1, hs]
    exact h_hs0
  · intro k h_k
    simp +instances [NA.addHist, MakeHist, hs, h.2 k h_k]
    apply h_hs'
end Automata
