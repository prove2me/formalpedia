-- Prove2me | solution 1 for Automata.da_run_on_to_det_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:37:35.500801+00:00
-- url     : https://prove2.me/submissions/6a09ce99-a93e-473a-9911-e0061997ecb5

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Det
import Theorems.Thm_Automata_da_run_on_of_det_run
import Theorems.Thm_P2M_Stream__extract_padDefault_dee05ba3940c


set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
open Automata
variable {A : Type}
attribute [local instance_reducible] DA.toNA
variable {M : DA A}
namespace Automata
theorem _root_.solution [Inhabited A] (M : DA A) (al : List A) :
    M.RunOn al = M.DetRun al.padDefault al.length := by
  simp +instances [← da_run_on_of_det_run M al.padDefault al.length, extract_padDefault]
end Automata
