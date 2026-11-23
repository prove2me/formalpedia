-- Prove2me | solution 1 for Automata.det_muller_accept_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:37:46.53894+00:00
-- url     : https://prove2.me/submissions/0a222479-a5e3-4e3c-8ef1-046d28b02b46

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Det

set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
open Automata
variable {A : Type}
namespace Automata
theorem _root_.solution (M : DA A) (accSet : Set (Set M.State)) (as : Stream' A) :
    M.MullerAccept accSetᶜ as ↔ ¬ M.MullerAccept accSet as := by
  simp +instances [DA.MullerAccept]
end Automata
