-- Prove2me | solution 1 for Automata.na_FinRun_modulo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:18:21.163954+00:00
-- url     : https://prove2.me/submissions/2195cf1a-11f6-4ad9-a0c6-e8dc44af49eb

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Automata_Basic

set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {A : Type} {M : NA A}
namespace Automata
theorem _root_.solution {n : ℕ} {as as' : Stream' A} {ss ss' : Stream' M.State}
    (ha : ∀ k < n, as k = as' k) (hs : ∀ k < n + 1, ss k = ss' k) (hr : M.FinRun n as ss) : M.FinRun n as' ss' := by
  rcases hr with ⟨h_init, h_next⟩ ; constructor
  · simpa [← hs]
  intro k h_k ; specialize h_next k h_k
  simpa [← ha k h_k, ← hs k (by omega), ← hs (k + 1) (by omega)]
end Automata
