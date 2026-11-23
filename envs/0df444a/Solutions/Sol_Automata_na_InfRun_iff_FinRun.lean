-- Prove2me | solution 1 for Automata.na_InfRun_iff_FinRun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:21:46.142437+00:00
-- url     : https://prove2.me/submissions/73e7eb7d-8069-4f57-97da-7e27a880d83a

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Automata_Basic

set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {A : Type} {M : NA A}
namespace Automata
theorem _root_.solution {as : Stream' A} {ss : Stream' M.State} :
    M.InfRun as ss ↔ ∀ n, M.FinRun n as ss := by
  constructor
  · rintro ⟨h_init, h_next⟩ n
    constructor
    · exact h_init
    intro k h_k
    exact h_next k
  · intro h_run
    constructor
    · exact (h_run 0).1
    intro k
    apply (h_run (k + 1)).2 k ; omega
end Automata
