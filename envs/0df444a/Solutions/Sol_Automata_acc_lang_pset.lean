-- Prove2me | solution 1 for Automata.acc_lang_pset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:45:22.552809+00:00
-- url     : https://prove2.me/submissions/00ff15d2-1b14-4d8f-9bba-dc1e6c20ac7a

import Definitions.Def_AutomataTheory_Automata_Det
import Definitions.Def_AutomataTheory_Automata_PSet
import Theorems.Thm_Automata_na_pset_run
import Theorems.Thm_Automata_da_fin_run_exists
import Theorems.Thm_Automata_da_fin_run_unique


set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
open Automata
attribute [local instance_reducible] NA.PSet
variable {A : Type} (M : NA A) (acc : Set M.State)
namespace Automata
theorem _root_.solution :
    M.PSet.toNA.AcceptedLang (M.PSet_Acc acc) = M.AcceptedLang acc := by
  ext al ; simp only [NA.AcceptedLang, NA.FinAccept] ; constructor
  · rintro ⟨n, as, ⟨ss', h_run', h_acc'⟩, h_al⟩
    have h_sn' := da_fin_run_unique h_run' n (by omega)
    rw [na_pset_run] at h_sn'
    simp +instances [h_sn', NA.PSet_Acc] at h_acc'
    obtain ⟨sn, ⟨ss, h_run, h_sn⟩, h_acc⟩ := h_acc'
    use n, as ; simp +instances [h_al]
    use ss ; simp +instances [h_run, h_sn, h_acc]
  · rintro ⟨n, as, ⟨ss, h_run, h_sn⟩, h_al⟩
    use n, as ; simp +instances [h_al]
    use (M.PSet.DetRun as) ; constructor
    · apply da_fin_run_exists
    · rw [na_pset_run, NA.PSet_Acc]
      use (ss n) ; simp +instances [h_sn] ; use ss
end Automata
