-- Prove2me | solution 1 for Automata.na_hist_inf_run_proj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:39:22.898526+00:00
-- url     : https://prove2.me/submissions/495ea00c-e548-47ba-883a-9dfdb4880563

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
theorem _root_.solution {as : Stream' A} {ss : Stream' (M.State × H)}
    (h : (M.addHist hist_init hist_next).InfRun as ss) : M.InfRun as (Prod.fst ∘ ss) := by
  constructor
  · have h' := h.1
    simp +instances [NA.addHist] at h'
    exact h'.1
  · intro k
    have h' := h.2 k
    simp +instances [NA.addHist] at h'
    exact h'.1
end Automata
