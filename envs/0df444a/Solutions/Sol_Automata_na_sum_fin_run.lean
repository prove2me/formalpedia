-- Prove2me | solution 1 for Automata.na_sum_fin_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:43:35.50881+00:00
-- url     : https://prove2.me/submissions/549e3325-2086-4a69-8a4c-83b5028d3de6

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Automata_Sum

set_option autoImplicit true
open Function Set Filter Stream'
attribute [local implicit_reducible] Stream'
open Automata
variable {I A : Type}
attribute [local instance_reducible] NA.Sum
variable {M : I → NA A}
namespace Automata
theorem _root_.solution {n : ℕ} {as : Stream' A} {ss : Stream' (NA.Sum M).State} :
    (NA.Sum M).FinRun n as ss ↔ ∃ i ss_i, (M i).FinRun n as ss_i ∧ ∀ k < n + 1, ss k = ⟨i, ss_i k⟩ := by
  constructor
  · rintro ⟨h_init, h_next⟩
    have := h_init
    simp +instances [NA.Sum, NA.init] at this
    rcases this with ⟨i, s0, h_s0_init, h_s0_ss⟩
    have h_ss_exists : ∀ k < n + 1, ∃ sk : (M i).State, ss k = Sigma.mk i sk := by
      intro k h_n ; induction' k with k h_k
      · use s0 ; simp +instances [h_s0_ss]
      obtain ⟨sk, h_sk⟩ := h_k (by omega : k < n + 1)
      have h_next_k := h_next k
      simp +instances [NA.Sum, h_sk] at h_next_k
      obtain ⟨sk', h_sk'⟩ := h_next_k (by omega : k < n)
      use sk' ; simp +instances [h_sk'.2]
    choose ss_i h_ss_i using h_ss_exists
    use i, (fun k ↦ if h : k < n + 1 then ss_i k h else ss_i 0 (by omega))
    constructor
    · constructor
      · simp +instances [h_ss_i 0 (by omega : 0 < n + 1)] at h_init
        simp +instances [NA.Sum] at h_init
        obtain ⟨i, s', h_s', rfl, h_eq⟩ := h_init
        rw [heq_eq_eq] at h_eq
        simp +instances [h_eq] at h_s'
        simpa
      · intro k h_k
        have h_next_k := h_next k h_k
        rw [h_ss_i k (by omega : k < n + 1), h_ss_i (k + 1) (by omega : k + 1 < n + 1)] at h_next_k
        simp +instances [NA.Sum] at h_next_k
        simpa +instances [h_k, (by omega : k < n + 1)]
    · intro k h_k
      simp +instances [h_k, h_ss_i k h_k]
  · rintro ⟨i, ss_i, h_run, h_ss⟩
    constructor
    · simp +instances [NA.Sum, h_ss 0 (by omega : 0 < n + 1)]
      use i, (ss_i 0)
      simp ; exact h_run.1
    · intro k h_k
      have h_run_k := h_run.2 k h_k
      simpa +instances [NA.Sum, h_ss k (by omega : k < n + 1), h_ss (k + 1) (by omega : k + 1 < n + 1)]
end Automata
