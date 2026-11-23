-- Prove2me | solution 1 for Automata.na_prod_fin_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:41:28.653471+00:00
-- url     : https://prove2.me/submissions/3ef6d0b2-fb03-42dc-8d1d-13e13b6baa8b

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Automata_Prod

set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {I A : Type}
variable {M : I → NA A}
namespace Automata
theorem _root_.solution {n : ℕ} {as : Stream' A} {ss : Stream' (NA.Prod M).State} :
    (NA.Prod M).FinRun n as ss ↔ ∀ i, (M i).FinRun n as (fun k ↦ ss k i) := by
  constructor
  · rintro ⟨h_init, h_next⟩ i
    constructor
    · apply h_init
    · intro k h_k ; exact h_next k h_k i
  · intro h_all
    constructor
    · intro i ; exact (h_all i).1
    · intro k h_k i ; exact (h_all i).2 k h_k
end Automata
