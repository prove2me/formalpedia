-- Prove2me | solution 1 for Automata.na_sum_inf_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:43:45.944719+00:00
-- url     : https://prove2.me/submissions/141dac18-06e2-46ee-98dd-2e7815d5f20c

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
theorem _root_.solution {as : Stream' A} {ss : Stream' (NA.Sum M).State} :
    (NA.Sum M).InfRun as ss ↔ ∃ i ss_i, (M i).InfRun as ss_i ∧ ss = (Sigma.mk i) ∘ ss_i := by
  constructor
  · rintro ⟨h_init, h_next⟩
    have := h_init
    simp +instances [NA.Sum, NA.init] at this
    rcases this with ⟨i, s0, h_s0_init, h_s0_ss⟩
    have h_ss_exists : ∀ k, ∃ sk : (M i).State, ss k = Sigma.mk i sk := by
      intro k ; induction' k with k h_k
      · use s0 ; rw [h_s0_ss]
      rcases h_k with ⟨sk, h_sk⟩
      have h_next_k := h_next k
      simp +instances [NA.Sum, h_sk] at h_next_k
      rcases h_next_k with ⟨sk', h_sk'⟩
      use sk' ; simp +instances [h_sk'.2]
    choose ss_i h_ss_i using h_ss_exists
    use i, ss_i
    constructor
    · constructor
      · rw [h_ss_i 0, NA.init] at h_init
        simp +instances [NA.Sum] at h_init
        obtain ⟨i, s', h_s', rfl, h_eq⟩ := h_init
        rw [heq_eq_eq] at h_eq
        rwa [h_eq] at h_s'
      · intro k
        have h_next_k := h_next k
        rw [h_ss_i k, h_ss_i (k + 1)] at h_next_k
        simp +instances [NA.Sum] at h_next_k
        assumption
    · ext k ; simp +instances [get.eq_1] ; simp +instances [h_ss_i k]
  · rintro ⟨i, ss_i, h_run, h_ss⟩
    simp +instances [h_ss, NA.Sum]
    constructor
    · simp +instances [NA.init]
      use i, (ss_i 0)
      simp ; exact h_run.1
    · intro k
      simp +instances [NA.next]
      exact h_run.2 k
end Automata
