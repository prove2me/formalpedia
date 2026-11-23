-- Prove2me | solution 1 for Automata.acc_lang_inter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:42:58.649321+00:00
-- url     : https://prove2.me/submissions/a0fe6ce3-1f84-4e05-a170-82e4271fff69

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Automata_Prod
import Theorems.Thm_Automata_na_prod_fin_run
import Theorems.Thm_P2M_Stream__extract_padDefault_dee05ba3940c
import Theorems.Thm_P2M_Stream__get_extract__ebf059d6908b
import Theorems.Thm_P2M_Stream__padDefault_elt_left_6b3d9f3e4cf6


set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {I A : Type} (M : I → NA A) (acc : (i : I) → Set ((M i).State))
namespace Automata
theorem _root_.solution [Inhabited A] :
    (NA.Prod M).AcceptedLang (NA.Prod_Acc M acc) = ⋂ i : I, (M i).AcceptedLang (acc i) := by
  ext al ; simp [NA.AcceptedLang, NA.FinAccept] ; constructor
  · rintro ⟨n, as, ⟨ss, h_run, h_acc⟩, h_al⟩ i
    use n, as ; simp [h_al]
    use (fun k ↦ ss k i) ; constructor
    · exact na_prod_fin_run.mp h_run i
    · exact h_acc i
  · intro h_all
    have h_all' : ∀ i, ∃ ss_i, (M i).FinRun al.length al.padDefault ss_i ∧ ss_i (al.length) ∈ acc i := by
      intro i ; obtain ⟨n, as, ⟨ss_i, h_run_i, h_acc_i⟩, h_al⟩ := h_all i
      have h_n : n = al.length := by simp [← h_al, length_extract]
      obtain rfl := h_n
      use ss_i ; simp [h_acc_i]
      constructor
      · exact h_run_i.1
      intro k h_k
      have h1 : k < (as.extract 0 al.length).length := by simp [length_extract, h_k]
      have h2 : al.padDefault k = as k := by
        rw [← h_al] ; simp (disch := omega) [padDefault_elt_left, get_extract']
      simp [h2, h_run_i.2 k h_k]
    use al.length, al.padDefault ; simp [extract_padDefault]
    choose ss_i h_ss_i using h_all'
    use (fun k i ↦ ss_i i k) ; constructor
    · apply na_prod_fin_run.mpr
      intro i ; simpa using (h_ss_i i).1
    · intro i ; exact (h_ss_i i).2
end Automata
