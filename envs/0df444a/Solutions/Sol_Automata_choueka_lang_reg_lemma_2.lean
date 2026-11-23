-- Prove2me | solution 1 for Automata.choueka_lang_reg_lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:47:24.723803+00:00
-- url     : https://prove2.me/submissions/28917eb0-b33b-4ba7-a383-ab9240e60f86

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
theorem _root_.solution [Inhabited A] {M : DA A} [Finite M.State] (s t : M.State) :
    RegLang { al | M.RunFromOn s al = t } := by
  use (DA.mk (A := A) M.State s M.next).toNA, {t} ; constructor
  · simpa +instances [DA.toNA]
  ext al ; simp +instances [da_acc_lang_iff_run_acc, DA.RunOn, DA.RunFromOn]
end Automata
