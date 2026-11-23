-- Prove2me | solution 1 for Automata.na_prod_inf_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:41:36.292801+00:00
-- url     : https://prove2.me/submissions/f3e0cd40-21b0-4c8b-881e-90d0245e8215

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Automata_Prod

set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {I A : Type}
variable {M : I → NA A}
namespace Automata
theorem _root_.solution {as : Stream' A} {ss : Stream' (NA.Prod M).State} :
    (NA.Prod M).InfRun as ss ↔ ∀ i, (M i).InfRun as (fun k ↦ ss k i) := by
  constructor
  · rintro ⟨h_init, h_next⟩ i
    constructor
    · apply h_init
    · intro k ; apply h_next
  · intro h_all
    constructor
    · intro i ; exact (h_all i).1
    · intro k i ; exact (h_all i).2 k
end Automata
