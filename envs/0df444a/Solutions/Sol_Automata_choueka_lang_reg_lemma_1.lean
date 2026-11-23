-- Prove2me | solution 1 for Automata.choueka_lang_reg_lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:40:57.337163+00:00
-- url     : https://prove2.me/submissions/bb89fc61-7687-4c01-8c0e-34fcd365f052

import Definitions.Def_AutomataTheory_Languages_RegLang
import Definitions.Def_AutomataTheory_Mathlib_InfGraphRamsey
import Definitions.Def_AutomataTheory_Languages_ChouekaLemma
import Theorems.Thm_Automata_da_acc_lang_iff_run_acc


set_option autoImplicit true
open Function Set Filter Stream'
open scoped Computability
open Classical
attribute [local implicit_reducible] Stream'
open Automata
attribute [local instance_reducible] DA.toNA
variable {A : Type}
namespace Automata
theorem _root_.solution [Inhabited A] {M : DA A} [Finite M.State] (s : M.State) :
    RegLang { al | M.RunOn al = s } := by
  use M.toNA, {s} ; constructor
  · simpa +instances [DA.toNA]
  ext al ; simp +instances [da_acc_lang_iff_run_acc]
end Automata
