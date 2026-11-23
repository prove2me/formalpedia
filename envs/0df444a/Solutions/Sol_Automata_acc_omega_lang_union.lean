-- Prove2me | solution 1 for Automata.acc_omega_lang_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:44:32.352641+00:00
-- url     : https://prove2.me/submissions/2f67e64f-6c2c-4e33-995f-0f256f9ab4ca

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Automata_Sum
import Theorems.Thm_Automata_na_sum_inf_run

set_option autoImplicit true
open Function Set Filter Stream'
attribute [local implicit_reducible] Stream'
open Automata
attribute [local instance_reducible] NA.Sum
variable {I A : Type} (M : I → NA A) (acc : (i : I) → Set ((M i).State))
namespace Automata
theorem _root_.solution :
    (NA.Sum M).AcceptedOmegaLang (NA.Sum_Acc M acc) = ⋃ i : I, (M i).AcceptedOmegaLang (acc i) := by
  ext as ; simp +instances [NA.Sum_Acc, NA.AcceptedOmegaLang, NA.BuchiAccept]
  constructor
  · rintro ⟨ss, h_run, h_inf⟩
    obtain ⟨i, ss_i, h_run_i, h_ss_i⟩ := na_sum_inf_run.mp h_run
    use i, ss_i
    constructor
    · assumption
    · let p k := ∃ i', ∃ si' ∈ acc i', ⟨i', si'⟩ = ss k
      let q k := ss_i k ∈ acc i
      have h_p : ∃ᶠ k in atTop, p k := by assumption
      have h_pq : ∀ k, p k → q k := by
        rintro k ⟨i', si', h_si'_acc, h_si'_ss⟩
        simp +instances [h_ss_i] at h_si'_ss
        rw [Sigma.mk.inj_iff] at h_si'_ss
        obtain ⟨rfl, h_si'_eq⟩ := h_si'_ss
        rw [heq_eq_eq] at h_si'_eq
        simpa +instances [q, ← h_si'_eq]
      exact Frequently.mono h_p h_pq
  · rintro ⟨i, ss_i, h_run_i, h_inf_i⟩
    use ((Sigma.mk i) ∘ ss_i)
    constructor
    · apply na_sum_inf_run.mpr
      use i, ss_i
    · let p k := ss_i k ∈ acc i
      let q k := ∃ i', ∃ si' ∈ acc i', ⟨i', si'⟩ = ((Sigma.mk i ∘ ss_i) k : (NA.Sum M).State)
      have h_p : ∃ᶠ k in atTop, p k := by assumption
      have h_pq : ∀ k, p k → q k := by
        simp +instances [p, q] ; intro k h
        use i, (ss_i k)
      exact Frequently.mono h_p h_pq
end Automata
