-- Prove2me | solution 1 for Automata.da_fin_run_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:22:44.694011+00:00
-- url     : https://prove2.me/submissions/32da0329-3222-47f6-8266-68d3c0dc8379

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Det
import Theorems.Thm_Automata_da_inf_run_exists
import Theorems.Thm_Automata_na_InfRun_iff_FinRun


set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
open Automata
variable {A : Type}
attribute [local instance_reducible] DA.toNA
variable {M : DA A}
namespace Automata
theorem _root_.solution (n : ℕ) (as : Stream' A) :
    M.toNA.FinRun n as (M.DetRun as) :=
  na_InfRun_iff_FinRun.mp (da_inf_run_exists as) n
end Automata
