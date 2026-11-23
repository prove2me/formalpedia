-- Prove2me | solution 1 for Automata.da_fin_run_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:13:45.19977+00:00
-- url     : https://prove2.me/submissions/c942388a-18dc-42be-a5b0-3a7eeeb61a30

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Det

set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
open Automata
variable {A : Type}
attribute [local instance_reducible] DA.toNA
variable {M : DA A}
namespace Automata
theorem _root_.solution {n : ℕ} {as : Stream' A} {ss : Stream' M.State}
    (h : M.toNA.FinRun n as ss) : ∀ k < n + 1, ss k = M.DetRun as k := by
  rcases h with ⟨h_init, h_next⟩
  intro k h_k ; induction' k with k h_ind
  · simp +instances [DA.toNA] at h_init
    simpa +instances [DA.DetRun]
  · have h_next' := h_next k (by omega)
    simp +instances [DA.toNA] at h_next'
    have h_ss_k := h_ind (by omega)
    simpa +instances [DA.DetRun, ← h_ss_k]
end Automata
