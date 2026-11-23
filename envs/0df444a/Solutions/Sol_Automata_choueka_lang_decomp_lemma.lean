-- Prove2me | solution 1 for Automata.choueka_lang_decomp_lemma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:47:11.500811+00:00
-- url     : https://prove2.me/submissions/c56e93fc-3c64-4c9f-b3eb-be5c6b0d2265

import Definitions.Def_AutomataTheory_Languages_RegLang
import Definitions.Def_AutomataTheory_Mathlib_InfGraphRamsey
import Definitions.Def_AutomataTheory_Languages_ChouekaLemma
import Theorems.Thm_Automata_da_run_from_on_append


set_option autoImplicit true
open Function Set Filter Stream'
open scoped Computability
open Classical
attribute [local implicit_reducible] Stream'
open Automata
attribute [local instance_reducible] DA.toNA
variable {A : Type}
namespace Automata
theorem _root_.solution {M : DA A} {acc : Set M.State} :
    M.ChouekaLang acc =
    ⋃ s ∈ acc, { al | al ≠ [] ∧ M.RunOn al = s } *
      ( { al | al ≠ [] ∧ M.RunOn al = M.RunFromOn s al } ∩
        ( { al | al ≠ [] ∧ M.RunOn al = M.RunFromOn s al } * {[]}ᶜ )ᶜ ) := by
  ext al ; simp +instances [DA.ChouekaLang, -List.extract_eq_take_drop] ; constructor
  · rintro ⟨m, h_m0, h_m1, h_acc, h_run, h_run'⟩
    use (M.RunOn (al.extract 0 m)) ; simp +instances [h_acc, -List.extract_eq_take_drop]
    use (al.extract 0 m), (al.extract m al.length)
    have h1 := List.length_pos_iff.mp (show 0 < al.length by omega)
    have h2 : al.extract 0 m ++ al.extract m = al := by
      ext k a ; rcases (show k < m ∨ ¬ k < m by omega) with h_k | h_k <;>
        simp +instances (disch := omega) [List.getElem?_append, List.getElem?_take, h_k] ; grind
    simp +instances [-List.extract_eq_take_drop, h_m1, h1, h2,
      (show ¬ m = 0 by omega), (show ¬ al.length - m = 0 by omega)]
    constructor
    · simpa +instances [-List.extract_eq_take_drop, DA.RunOn, ← da_run_from_on_append, h2]
    · rintro ⟨al1, al2, ⟨h_al1, h_run1⟩, h_al2, h_alm⟩
      have := List.length_pos_iff.mpr h_al1
      have := List.length_pos_iff.mpr h_al2
      have : m + al1.length + al2.length = al.length := by
        rw [← h2, ← h_alm] ; simp +instances [List.length_append, add_assoc] ; omega
      simp +instances [-List.extract_eq_take_drop, DA.RunOn, ← da_run_from_on_append] at h_run1
      specialize h_run' (m + al1.length) (by omega) (by omega)
      have h3 : al.extract m (m + al1.length) = al1 := by
        rw [← h2, ← h_alm] ; ext k a
        rcases (show k < al1.length ∨ ¬ k < al1.length by omega) with h_k | h_k <;>
          simp +instances [List.getElem?_append, List.getElem?_drop, h_k]
        simp +instances [(show m + k - min m al.length = k by omega), h_k]
      have h4 : al.extract 0 (m + al1.length) = al.extract 0 m ++ al1 := by
        rw [← h2, ← h_alm] ; ext k a
        rcases (show k < m ∨ (¬ k < m ∧ k < m + al1.length) ∨ ¬ k < m + al1.length by omega) with h_k | h_k | h_k <;>
          simp +instances (disch := omega) [List.getElem?_append, List.getElem?_take, h_k]
        · simp +instances [(show k - m < al1.length by omega)]
        · simp +instances [(show ¬ k < m by omega)]
      rw [DA.RunOn, h3, h4] at h_run'
      contradiction
  · rintro ⟨s, h_al1_acc, al1, al2, ⟨h_al1_ne, rfl⟩, ⟨⟨h_al2_ne, h_al2_run⟩, h_al2'⟩, rfl⟩
    use al1.length
    have h_al1_pos := List.length_pos_iff.mpr h_al1_ne
    have h_al2_pos := List.length_pos_iff.mpr h_al2_ne
    have h1 : (al1 ++ al2).extract 0 al1.length = al1 := by simp +instances
    have h2 : (al1 ++ al2).extract al1.length (al1.length + al2.length) = al2 := by simp +instances
    simp +instances (disch := omega) [-List.extract_eq_take_drop, List.length_append, h_al1_pos, h_al2_pos, h1, h_al1_acc]
    constructor
    · simp +instances [h2, DA.RunOn, da_run_from_on_append] ; exact h_al2_run
    intro k h_k1 h_k2 h_contra
    suffices _ : al2 ∈ {al | (al = [] → False) ∧ M.RunOn al = M.RunFromOn (M.RunOn al1) al} * {[]}ᶜ by
      contradiction
    use al2.extract 0 (k - al1.length), al2.extract (k - al1.length) al2.length
    simp +instances [-List.extract_eq_take_drop, h_al2_ne, (show ¬ k - al1.length = 0 by omega),
      (show ¬al2.length - (k - al1.length) = 0 ∧ k - al1.length < al2.length by omega)]
    constructor
    · have h3 : (al1 ++ al2).extract al1.length k = al2.extract 0 (k - al1.length) := by simp +instances
      have h4 : (al1 ++ al2).extract 0 k = al1 ++ al2.extract 0 (k - al1.length) := by simp +instances [List.take_append] ; omega
      simp +instances [-List.extract_eq_take_drop, h3, h4, DA.RunOn, da_run_from_on_append] at h_contra
      exact h_contra
    · ext j a
      rcases (show j < k - al1.length ∨ ¬ j < k - al1.length by omega) with h_j | h_j <;>
        simp +instances (disch := omega) [List.getElem?_append, List.getElem?_take, List.getElem?_drop, h_j]
      simp +instances [List.getElem?_eq_some_iff] ; omega
end Automata
