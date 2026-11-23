-- Prove2me | solution 1 for Automata.acc_lang_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:44:21.643+00:00
-- url     : https://prove2.me/submissions/f4fe1e9b-877f-47ef-9ed0-c120467e51c6

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Automata_Sum
import Theorems.Thm_Automata_na_sum_fin_run

set_option autoImplicit true
open Function Set Filter Stream'
attribute [local implicit_reducible] Stream'
open Automata
attribute [local instance_reducible] NA.Sum
variable {I A : Type} (M : I → NA A) (acc : (i : I) → Set ((M i).State))
namespace Automata
theorem _root_.solution :
    (NA.Sum M).AcceptedLang (NA.Sum_Acc M acc) = ⋃ i : I, (M i).AcceptedLang (acc i) := by
  ext al ; simp +instances [NA.Sum_Acc, NA.AcceptedLang, NA.FinAccept]
  constructor
  · rintro ⟨n, as, ⟨ss, h_run, h_acc⟩, h_al⟩
    obtain ⟨i, ss_i, h_run_i, h_ss_i⟩ := na_sum_fin_run.mp h_run
    use i, n, as
    constructor
    · use ss_i
      constructor
      · assumption
      obtain ⟨i', si', h_si', h_last⟩ := h_acc
      simp +instances [h_ss_i] at h_last
      rw [Sigma.mk.inj_iff] at h_last
      obtain ⟨rfl, h_si'_eq⟩ := h_last
      rw [heq_eq_eq] at h_si'_eq
      simpa +instances [← h_si'_eq]
    · assumption
  · rintro ⟨i, n, as, ⟨ss_i, h_run, h_last⟩, h_al⟩
    use n, as
    constructor
    · use ((Sigma.mk i) ∘ ss_i)
      constructor
      · apply na_sum_fin_run.mpr
        use i, ss_i
        simp +instances [h_run]
      · use i, ss_i (Fin.last n)
        simpa
    · assumption
end Automata
