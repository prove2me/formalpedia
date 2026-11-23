-- Prove2me | solution 1 for Automata.na_pset_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:44:24.715785+00:00
-- url     : https://prove2.me/submissions/708c4e4a-5e7b-4e98-8436-20549fb7eaaa

import Definitions.Def_AutomataTheory_Automata_Det
import Definitions.Def_AutomataTheory_Automata_PSet
import Theorems.Thm_Automata_na_pset_reach_init
import Theorems.Thm_Automata_na_pset_reach_next

set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
open Automata
variable {A : Type}
attribute [local instance_reducible] NA.PSet
variable {M : NA A}
namespace Automata
theorem _root_.solution (as : Stream' A) (k : ℕ) :
    M.PSet.DetRun as k = { s : M.State | ∃ ss, M.FinRun k as ss ∧ ss k = s } := by
  induction' k with k h_ind
  · rw [na_pset_reach_init as, Set.ext_iff]
    intro s ; constructor
    · intro h_init
      use (fun k ↦ s) ; simpa +instances [NA.FinRun]
    · rintro ⟨ss, ⟨h_init, h_next⟩, h_s⟩
      simpa +instances [← h_s]
  rw [na_pset_reach_next as k, h_ind, Set.ext_iff]
  intro s ; constructor <;> simp
  · rintro s' ⟨ss, ⟨h_init, h_next⟩, h_s'⟩ h_s
    use (fun j ↦ if j < k + 1 then ss j else s)
    simp ; constructor
    · simpa
    intro j h_j
    rcases (by omega : j < k ∨ j = k) with h_j' | h_j'
    · simp +instances [h_j, h_j', Nat.le_of_lt h_j'] ; exact h_next j h_j'
    · simpa +instances [h_j', h_s']
  · rintro ss ⟨h_init, h_next⟩ h_s
    use (ss k)
    simp +instances [← h_s, h_next k (by omega)]
    use ss ; simp ; constructor
    · exact h_init
    intro j h_j
    exact h_next j (by omega)
end Automata
