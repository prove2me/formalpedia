-- Prove2me | solution 1 for Automata.da_run_from_on_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:19:13.700808+00:00
-- url     : https://prove2.me/submissions/84fe9165-bf16-40e2-be5c-0f72655bbb65

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
theorem _root_.solution (M : DA A) (s : M.State) (al1 al2 : List A) :
    M.RunFromOn s (al1 ++ al2) = M.RunFromOn (M.RunFromOn s al1) al2 := by
  simp +instances only [DA.RunFromOn, List.foldl_append]
end Automata
