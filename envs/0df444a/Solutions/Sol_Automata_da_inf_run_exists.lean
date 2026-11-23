-- Prove2me | solution 1 for Automata.da_inf_run_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:17:06.906989+00:00
-- url     : https://prove2.me/submissions/64015783-767c-479c-b740-0c9532f1b2e7

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
theorem _root_.solution (as : Stream' A) :
    M.toNA.InfRun as (M.DetRun as) := by
  constructor <;> simp +instances [DA.toNA, DA.DetRun]
end Automata
