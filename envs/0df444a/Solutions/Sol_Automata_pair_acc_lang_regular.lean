-- Prove2me | solution 1 for Automata.pair_acc_lang_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:53:50.117802+00:00
-- url     : https://prove2.me/submissions/1dd3b9ac-c345-48ec-88e9-361c2042486d

import Definitions.Def_AutomataTheory_Automata_Hist
import Definitions.Def_AutomataTheory_Languages_RegLang
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Pair
import Theorems.Thm_Automata_pair_path_fin_run
import Theorems.Thm_Automata_na_FinRun_modulo
import Theorems.Thm_Automata_na_hist_fin_run_exists
import Theorems.Thm_Automata_na_hist_fin_run_proj
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
    RegLang (M.PairAccLang acc s s') := by
  let M' := (M.SingleInit s).addHist {False} (fun s a ↦ {s.2 ∨ s.1 ∈ acc})
  use M', {p | p.1 = s' ∧ (p.2 ∨ s' ∈ acc) } ; constructor
  · simp +instances [Function.comp_apply, M', NA.SingleInit] ; exact Finite.instProd
  ext al ; constructor
  · rintro ⟨n, as, ⟨ss', h_run', rfl, h_acc⟩, rfl⟩
    have h_run := na_hist_fin_run_proj h_run'
    use (Prod.fst ∘ ss')
    constructor
    · apply pair_path_fin_run.mpr ; simp +instances [Function.comp_apply, length_extract]
      apply na_FinRun_modulo (hr := h_run)
      · intro k h_k
        have h1 : k < (as.extract 0 n).length := by simp +instances [Function.comp_apply, length_extract, h_k]
        simp (disch := omega) [padDefault_elt_left h1, get_extract']
      · simp
    simp
    obtain (h_acc | h_acc) := h_acc.symm
    · use n ; simp +instances [Function.comp_apply, h_acc, length_extract]
    by_contra! h_contra
    suffices h : ∀ k < n + 1, ¬ (ss' k).2 by simp +instances [Function.comp_apply, h n (by omega)] at h_acc
    intro k h_k ; induction' k with k h_ind
    · have h_init := h_run'.1
      simp +instances [Function.comp_apply, M', NA.addHist] at h_init
      simp +instances [Function.comp_apply, h_init]
    specialize h_ind (by omega)
    specialize h_contra k (by simp +instances [Function.comp_apply, length_extract] ; omega)
    have h_next := h_run'.2 k (by omega)
    simp +instances [Function.comp_apply, M', NA.addHist, h_ind, h_contra] at h_next
    simp +instances [Function.comp_apply, h_next]
  · rintro ⟨ss, h_path, k0, h_k0, h_k0_acc⟩
    use al.length, al.padDefault ; simp +instances [Function.comp_apply, extract_padDefault]
    obtain ⟨h_run, rfl⟩ := pair_path_fin_run.mp h_path
    have h_ne_init : Set.Nonempty {False} := by simp
    have h_ne_next : ∀ (s : (M.SingleInit s).State × Prop) (a : A), Set.Nonempty {s.2 ∨ s.1 ∈ acc} := by simp
    obtain ⟨hist, h_run'⟩ := na_hist_fin_run_exists h_ne_init h_ne_next h_run
    use (fun k ↦ (ss k, hist k)) ; simp +instances [Function.comp_apply, M', h_run']
    obtain (rfl | h_k0) := show k0 = al.length ∨ k0 < al.length by omega
    · simp +instances [Function.comp_apply, h_k0_acc]
    suffices h : ∀ k > k0, k < al.length + 1 → hist k by simp +instances [Function.comp_apply, h al.length h_k0]
    intro k h_k
    obtain ⟨j, rfl⟩ := show ∃ j, k = k0 + j + 1 by use (k - k0 - 1) ; omega
    clear h_k ; induction' j with j h_ind
    · have h_next := h_run'.2 k0 h_k0
      simp +instances [Function.comp_apply, NA.addHist, h_k0_acc] at h_next
      simp +instances [Function.comp_apply, h_next]
    intro h_j
    specialize h_ind (by omega)
    have h_next := h_run'.2 (k0 + j + 1) (by omega)
    simp +instances [Function.comp_apply, NA.addHist, h_ind] at h_next
    simp +instances [Function.comp_apply, h_next, (show k0 + (j + 1) + 1 = k0 + j + 1 + 1 by omega)]
end Automata
