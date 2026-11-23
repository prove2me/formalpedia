-- Prove2me | solution 1 for Automata.da_acc_lang_iff_run_acc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:38:43.020807+00:00
-- url     : https://prove2.me/submissions/3a4e1bf2-ee14-48cb-b7ee-6a019f662882

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Det
import Theorems.Thm_Automata_da_fin_run_exists
import Theorems.Thm_Automata_da_fin_run_unique
import Theorems.Thm_Automata_da_run_on_of_det_run
import Theorems.Thm_Automata_da_run_on_to_det_run
import Theorems.Thm_P2M_Stream__extract_padDefault_dee05ba3940c


set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
open Automata
variable {A : Type}
attribute [local instance_reducible] DA.toNA
variable {M : DA A}
namespace Automata
theorem _root_.solution [Inhabited A] (M : DA A) (acc : Set M.State) (al : List A) :
    al ∈ M.toNA.AcceptedLang acc ↔ M.RunOn al ∈ acc := by
  constructor
  · rintro ⟨n, as, ⟨ss, h_run, h_acc⟩, rfl⟩
    have h0 := da_fin_run_unique h_run n (by omega)
    have h1 := da_run_on_of_det_run M as n
    simp +instances [h1, ← h0, h_acc]
  · intro h_acc
    use al.length, al.padDefault ; simp +instances [extract_padDefault]
    use (M.DetRun al.padDefault) ; constructor
    · exact da_fin_run_exists (M := M) al.length al.padDefault
    · simp +instances [← da_run_on_to_det_run, h_acc]
end Automata
