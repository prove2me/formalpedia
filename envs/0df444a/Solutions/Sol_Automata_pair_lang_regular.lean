-- Prove2me | solution 1 for Automata.pair_lang_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:46:32.595167+00:00
-- url     : https://prove2.me/submissions/26b410cf-b841-4535-a3cb-8588cb72138b

import Definitions.Def_AutomataTheory_Automata_Hist
import Definitions.Def_AutomataTheory_Languages_RegLang
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Pair
import Theorems.Thm_Automata_pair_path_fin_run
import Theorems.Thm_P2M_Stream__extract_padDefault_dee05ba3940c
import Theorems.Thm_P2M_Stream__get_extract__ebf059d6908b
import Theorems.Thm_P2M_Stream__padDefault_elt_left_6b3d9f3e4cf6


set_option autoImplicit true
open Function Set Filter Stream'
attribute [local implicit_reducible] Stream'
open Automata
attribute [local instance_reducible] NA.addHist
variable {A : Type}
variable {M : NA A} {acc : Set M.State}
attribute [local instance_reducible] NA.SingleInit
namespace Automata
theorem _root_.solution [Inhabited A] [h_fin : Finite M.State] {s s' : M.State} :
    RegLang (M.PairLang s s') := by
  use (M.SingleInit s), {s'} ; constructor
  · assumption
  ext al ; constructor
  · rintro ⟨n, as, ⟨ss, ⟨h_init, h_next⟩, rfl⟩, rfl⟩
    use ss ; apply pair_path_fin_run.mpr
    simp +instances [Function.comp_apply, NA.FinRun, h_init, length_extract]
    intro k h_k
    have h1 : k < (as.extract 0 n).length := by simp +instances [Function.comp_apply, length_extract, h_k]
    simp (disch := omega) [padDefault_elt_left h1, get_extract', h_next]
  · rintro ⟨ss, h_path⟩
    use al.length, al.padDefault ; simp +instances [Function.comp_apply, extract_padDefault]
    use ss ; exact pair_path_fin_run.mp h_path
end Automata
