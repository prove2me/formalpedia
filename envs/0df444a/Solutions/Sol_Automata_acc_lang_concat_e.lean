-- Prove2me | solution 1 for Automata.acc_lang_concat_e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:35:12.563796+00:00
-- url     : https://prove2.me/submissions/8c34f284-6dea-4b60-a4a8-58996e5f01cd

import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Automata_Concat
import Theorems.Thm_Automata_na_concat_fin_run_0

set_option autoImplicit true
open Function Set Filter Sum Stream'
open Classical
open Automata
variable {A : Type} {M0 M1 : NA A} {acc0 : Set M0.State} {acc1 : Set M1.State}
namespace Automata
theorem _root_.solution :
    (M0.Concat acc0 M1).AcceptedLang (inl '' acc0) = M0.AcceptedLang acc0 := by
  ext al ; constructor
  · rintro ⟨m, as, ⟨ss, h_run, h_acc⟩, h_al⟩
    have h_m : ∃ s0, ss m = inl s0 := by
      obtain ⟨s0, _, h_s0⟩ := h_acc
      use s0 ; simp +instances [h_s0]
    obtain ⟨ss0, h_run0,h_ss0⟩ := na_concat_fin_run_0.mp ⟨h_run, h_m⟩
    use m, as ; simp +instances [h_al]
    use ss0 ; simp +instances [h_run0]
    obtain ⟨sm, h_sm_acc, h_sm⟩ := h_acc
    rw [h_ss0 m (by omega)] at h_sm
    have h_sm := Sum.inl.inj h_sm
    simpa +instances [← h_sm]
  · rintro ⟨m, as, ⟨ss0, h_run0, h_acc0⟩, h_al⟩
    use m, as ; simp +instances [h_al]
    let ss : Stream' (M0.Concat acc0 M1).State := inl ∘ ss0
    use ss ; constructor
    · suffices (M0.Concat acc0 M1).FinRun m as ss ∧ (∃ s0, ss m = inl s0) by tauto
      apply na_concat_fin_run_0.mpr
      exact ⟨ss0, h_run0, fun k h_k => rfl⟩
    · exact ⟨ss0 m, h_acc0, rfl⟩
end Automata
