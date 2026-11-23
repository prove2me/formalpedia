-- Prove2me | solution 1 for Automata.det_muller_accept_boolean_form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:38:04.03989+00:00
-- url     : https://prove2.me/submissions/ccfbd9af-d581-4539-b7db-7be44d79d91d

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Det
import Theorems.Thm_Automata_da_inf_run_exists
import Theorems.Thm_Automata_da_inf_run_unique
import Theorems.Thm_Automata_da_acc_omega_lang

set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
open Automata
variable {A : Type}
namespace Automata
theorem _root_.solution (M : DA A) (accSet : Set (Set M.State)) :
    {as | M.MullerAccept accSet as} =
    ⋃ acc ∈ accSet, (⋂ s ∈ acc, (M.toNA.AcceptedLang {s})↗ω) ∩ (⋂ s ∈ accᶜ, ((M.toNA.AcceptedLang {s})↗ω)ᶜ) := by
  ext as
  have hs (s : M.State) :
      as ∈ (M.toNA.AcceptedLang {s})↗ω ↔ s ∈ InfOcc (M.DetRun as) := by
    have heq := congrArg (fun L : Set (Stream' A) => as ∈ L)
      (da_acc_omega_lang (M := M) (acc := {s}))
    refine (Iff.of_eq heq.symm).trans ?_
    constructor
    · rintro ⟨ss, h_run, h_inf⟩
      obtain ⟨rfl⟩ := da_inf_run_unique h_run
      exact h_inf
    · intro h_inf
      exact ⟨M.DetRun as, da_inf_run_exists as, h_inf⟩
  change InfOcc (M.DetRun as) ∈ accSet ↔ _
  simp only [Set.mem_iUnion, Set.mem_iInter, Set.mem_inter_iff, Set.mem_compl_iff, hs]
  constructor
  · intro h
    exact ⟨InfOcc (M.DetRun as), h, fun s hs => hs, fun s hs => hs⟩
  · rintro ⟨acc, hacc, hf, hb⟩
    have heq : acc = InfOcc (M.DetRun as) := Set.Subset.antisymm hf (by
      intro s hs
      by_contra hn
      exact hb s hn hs)
    exact heq ▸ hacc
end Automata
