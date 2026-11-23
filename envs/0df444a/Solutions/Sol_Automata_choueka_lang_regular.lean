-- Prove2me | solution 1 for Automata.choueka_lang_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:51:01.96081+00:00
-- url     : https://prove2.me/submissions/065d187d-f35c-429f-ba9a-d98a63542d18

import Definitions.Def_AutomataTheory_Languages_RegLang
import Definitions.Def_AutomataTheory_Mathlib_InfGraphRamsey
import Definitions.Def_AutomataTheory_Languages_ChouekaLemma
import Theorems.Thm_Automata_choueka_lang_decomp_lemma
import Theorems.Thm_Automata_choueka_lang_reg_lemma_3
import Theorems.Thm_Automata_choueka_lang_reg_lemma_4
import Theorems.Thm_reg_lang_biUnion
import Theorems.Thm_reg_lang_compl
import Theorems.Thm_reg_lang_concat
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
theorem _root_.solution [Inhabited A] {M : DA A} [Finite M.State] {acc : Set M.State} :
    RegLang (M.ChouekaLang acc) := by
  rw [choueka_lang_decomp_lemma] ; apply reg_lang_biUnion
  intro s _ ; apply reg_lang_concat
  · apply choueka_lang_reg_lemma_3
  · apply reg_lang_inter
    · apply choueka_lang_reg_lemma_4
    · apply reg_lang_compl ; apply reg_lang_concat
      · apply choueka_lang_reg_lemma_4
      · apply reg_lang_compl ; exact reg_lang_epsilon
end Automata
