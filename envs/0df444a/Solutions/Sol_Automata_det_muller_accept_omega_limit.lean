-- Prove2me | solution 1 for Automata.det_muller_accept_omega_limit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:37:51.899563+00:00
-- url     : https://prove2.me/submissions/7a720977-2218-4553-87e7-2a25c336630f

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Det
import Theorems.Thm_Automata_da_inf_run_exists
import Theorems.Thm_Automata_da_inf_run_unique
import Theorems.Thm_Automata_da_acc_omega_lang
import Theorems.Thm_frequently_iff_strict_mono
import Theorems.Thm_frequently_in_finite_set


set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
open Automata
variable {A : Type}
namespace Automata
theorem _root_.solution (M : DA A) [Finite M.State] (acc : Set M.State) :
    ∃ accSet, {as | M.MullerAccept accSet as} = (M.toNA.AcceptedLang acc)↗ω := by
  use {acc' | (acc' ∩ acc).Nonempty} ; ext as
  simp +instances [← da_acc_omega_lang, DA.MullerAccept] ; constructor
  · rintro ⟨s, h_inf, h_acc⟩
    use (M.DetRun as) ; constructor
    · exact da_inf_run_exists as
    obtain ⟨φ, h_mono, h_s⟩ := frequently_iff_strict_mono.mp h_inf
    apply frequently_iff_strict_mono.mpr
    exact ⟨φ, h_mono, fun m => (h_s m).symm ▸ h_acc⟩
  · rintro ⟨ss, h_run, h_acc⟩
    obtain ⟨rfl⟩ := da_inf_run_unique h_run
    have : Finite M.toNA.State := by assumption
    obtain ⟨s, h_s, h_inf⟩ := frequently_in_finite_set.mp h_acc
    exact ⟨s, h_inf, h_s⟩
end Automata
