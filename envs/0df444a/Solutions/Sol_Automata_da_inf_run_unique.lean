-- Prove2me | solution 1 for Automata.da_inf_run_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:25:17.338461+00:00
-- url     : https://prove2.me/submissions/153ccbb1-97e7-4a12-9d66-5acf6bb08332

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
theorem _root_.solution {as : Stream' A} {ss : Stream' M.State}
    (h : M.toNA.InfRun as ss) : ss = M.DetRun as := by
  ext k ; simp +instances [get.eq_1] ; induction' k with k h_ind
  · simpa +instances [DA.toNA, DA.DetRun] using h.1
  · simpa +instances [DA.DetRun, DA.toNA, h_ind] using h.2 k
end Automata
