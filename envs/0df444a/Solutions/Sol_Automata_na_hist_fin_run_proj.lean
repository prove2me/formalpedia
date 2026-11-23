-- Prove2me | solution 1 for Automata.na_hist_fin_run_proj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:38:22.710968+00:00
-- url     : https://prove2.me/submissions/a0f8cc94-93ce-443a-8742-84659bd778f2

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
theorem _root_.solution {n : ℕ} {as : Stream' A} {ss : Stream' (M.State × H)}
    (h : (M.addHist hist_init hist_next).FinRun n as ss) : M.FinRun n as (Prod.fst ∘ ss) := by
  constructor
  · have h' := h.1
    simp +instances [NA.addHist] at h'
    exact h'.1
  · intro k h_k
    have h' := h.2 k h_k
    simp +instances [NA.addHist] at h'
    exact h'.1
end Automata
