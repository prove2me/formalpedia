-- Prove2me | solution 1 for Automata.da_acc_lang_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:37:40.368051+00:00
-- url     : https://prove2.me/submissions/ffd62ef5-6cca-47ef-a36f-648b35663bd4

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Det
import Theorems.Thm_Automata_da_fin_run_exists
import Theorems.Thm_Automata_da_fin_run_unique
import Theorems.Thm_Automata_na_FinRun_fixSuffix
import Theorems.Thm_P2M_Stream__extract_padDefault_dee05ba3940c
import Theorems.Thm_P2M_Stream__get_extract__ebf059d6908b


set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
open Automata
variable {A : Type} {M : DA A} {acc : Set M.State}
namespace Automata
theorem _root_.solution [Inhabited A] :
    M.toNA.AcceptedLang accᶜ = (M.toNA.AcceptedLang acc)ᶜ := by
  ext al
  constructor
  · rintro ⟨n, as, ⟨ss, h_run, h_acc⟩, h_al⟩
    rintro ⟨n', as', ⟨ss', h_run', h_acc'⟩, h_al'⟩
    have h_len : al.length = n := by simp +instances [← h_al, length_extract]
    have h_len' : al.length = n' := by simp +instances [← h_al', length_extract]
    obtain ⟨rfl⟩ := show n' = n by rw [← h_len, ← h_len']
    have h_run_n := na_FinRun_fixSuffix h_run
    have h_run_n' := na_FinRun_fixSuffix h_run'
    have h_as_eq : fixSuffix as' n default = fixSuffix as n default := by
      ext k ; simp +instances [get.eq_1] ; rcases Classical.em (k < n) with h_k | h_k <;> simp +instances [fixSuffix, h_k]
      have h_as_k : as k = al.get ⟨k, (by omega)⟩ := by simp +instances (disch := omega) [← h_al, get_extract']
      have h_as_k' : as' k = al.get ⟨k, (by omega)⟩ := by simp +instances (disch := omega) [← h_al', get_extract']
      rw [h_as_k, h_as_k']
    rw [h_as_eq] at h_run_n'
    have h_ss_n := da_fin_run_unique h_run_n n (by omega)
    have h_ss_n' := da_fin_run_unique h_run_n' n (by omega)
    simp +instances [fixSuffix] at h_ss_n h_ss_n'
    rw [h_ss_n] at h_acc ; rw [h_ss_n'] at h_acc'
    contradiction
  · intro h_compl
--    let as := fun k ↦ if h : k < al.length then al[k] else default
    let as := al.padDefault
    have h_al : as.extract 0 al.length = al := by simp +instances [as, extract_padDefault]
    use al.length, as ; simp +instances [h_al]
    let ss := M.DetRun as
    have h_run : M.toNA.FinRun al.length as ss := by exact da_fin_run_exists al.length as
    use ss ; constructor
    · exact h_run
    intro h_acc
    have : al ∈ (M.toNA.AcceptedLang acc) := by
      use al.length, as ; simp +instances [h_al] ; use! ss
    contradiction
end Automata
