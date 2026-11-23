-- Prove2me | solution 1 for Automata.choueka_lang_reg_lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:50:04.734803+00:00
-- url     : https://prove2.me/submissions/6123c5b4-5573-4f7e-b2e1-954c6fa1071d

import Definitions.Def_AutomataTheory_Languages_RegLang
import Definitions.Def_AutomataTheory_Mathlib_InfGraphRamsey
import Definitions.Def_AutomataTheory_Languages_ChouekaLemma
import Theorems.Thm_Automata_choueka_lang_reg_lemma_1
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
    RegLang { al | al ≠ [] ∧ M.RunOn al = s } := by
  have h1 : { al | al ≠ [] ∧ M.RunOn al = s } = {[]}ᶜ ∩ { al | M.RunOn al = s } := by grind
  rw [h1] ; apply reg_lang_inter
  · apply reg_lang_compl ; exact reg_lang_epsilon
  · apply choueka_lang_reg_lemma_1
end Automata
