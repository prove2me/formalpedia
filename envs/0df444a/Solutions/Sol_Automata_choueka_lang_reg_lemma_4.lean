-- Prove2me | solution 1 for Automata.choueka_lang_reg_lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:50:05.344373+00:00
-- url     : https://prove2.me/submissions/a733b4fd-9ac7-4383-83ea-ead8535b1ecd

import Definitions.Def_AutomataTheory_Languages_RegLang
import Definitions.Def_AutomataTheory_Mathlib_InfGraphRamsey
import Definitions.Def_AutomataTheory_Languages_ChouekaLemma
import Theorems.Thm_Automata_choueka_lang_reg_lemma_1
import Theorems.Thm_Automata_choueka_lang_reg_lemma_2
import Theorems.Thm_reg_lang_biUnion
import Theorems.Thm_reg_lang_compl
import Theorems.Thm_reg_lang_epsilon
import Theorems.Thm_reg_lang_inter


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
    RegLang { al | al ≠ [] ∧ M.RunOn al = M.RunFromOn s al } := by
  have h1 : { al | al ≠ [] ∧ M.RunOn al = M.RunFromOn s al } =
      {[]}ᶜ ∩ ⋃ t, { al | M.RunOn al = t } ∩ { al | M.RunFromOn s al = t } := by aesop
  rw [h1] ; apply reg_lang_inter
  · apply reg_lang_compl ; exact reg_lang_epsilon
  · rw [← biUnion_univ] ; apply reg_lang_biUnion
    intro t _ ; apply reg_lang_inter
    · apply choueka_lang_reg_lemma_1
    · apply choueka_lang_reg_lemma_2
end Automata
