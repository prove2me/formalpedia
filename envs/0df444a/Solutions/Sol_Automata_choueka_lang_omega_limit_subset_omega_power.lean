-- Prove2me | solution 1 for Automata.choueka_lang_omega_limit_subset_omega_power
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:50:01.684461+00:00
-- url     : https://prove2.me/submissions/f096a8fc-6a0b-4103-86e4-d90e27038503
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AutomataTheory_Languages_RegLang
import Definitions.Def_AutomataTheory_Mathlib_InfGraphRamsey
import Definitions.Def_AutomataTheory_Languages_ChouekaLemma
import Theorems.Thm_Automata_greater_subseq_lemma
import Theorems.Thm_Automata_da_acc_lang_iff_run_acc
import Theorems.Thm_Automata_da_run_from_on_append
import Theorems.Thm_P2M_Stream__append_extract_extract_2ca0e177dfc2
import Theorems.Thm_P2M_Stream__extract_extract1_6c8e1f1171b3
import Theorems.Thm_P2M_Stream__extract_extract2_13660c325975
import Theorems.Thm_frequently_iff_strict_mono


set_option autoImplicit true
open Function Set Filter Stream'
open scoped Computability
open Classical
attribute [local implicit_reducible] Stream'
open Automata
attribute [local instance_reducible] DA.toNA
variable {A : Type}
namespace Automata
theorem _root_.solution [Inhabited A] {M : DA A} {acc : Set M.State} :
    (M.ChouekaLang acc)↗ω ⊆ (M.toNA.AcceptedLang acc)^ω := by
  intro as ; simp +instances [instOmegaLimit, OmegaLimit, frequently_iff_strict_mono]
  intro φ h_φ_mono h_prefix
  have h_m_ex : ∀ n, ∃ m, 0 < m ∧ m < φ n ∧
      M.RunOn (as.extract 0 m) ∈ acc ∧ M.RunOn (as.extract m (φ n)) = M.RunOn (as.extract 0 (φ n)) ∧
      ∀ k, m < k → k < φ n → M.RunOn (as.extract m k) ≠ M.RunOn (as.extract 0 k) := by
    intro n
    obtain ⟨m, h_m0, h_m1, h_acc, h_run, h_run'⟩ := h_prefix n
    simp +instances [length_extract] at h_m1
    simp +instances [-List.extract_eq_take_drop, extract_extract2 (show m ≤ φ n by omega)] at h_acc
    simp +instances [-List.extract_eq_take_drop, extract_extract1] at h_run
    use m ; simp +instances [h_m0, h_m1, h_acc, h_run]
    intro k h_k h_k'
    specialize h_run' k h_k (by simp +instances [length_extract, h_k'])
    simp +instances [-List.extract_eq_take_drop, extract_extract2 (show k ≤ φ n by omega)] at h_run'
    exact h_run'
  choose φ' h_φ'_0 h_φ'_n h_acc h_run h_run' using h_m_ex
  have h_inj : Injective φ' := by
    intro n1 n2 h_φ' ; by_contra h_contra
    wlog h : n1 < n2 generalizing n1 n2 with h'
    · exact h' h_φ'.symm (by omega) (by omega)
    have := h_φ_mono h ; have := h_φ'_n n1 ; have := h_run n1
    have := h_run' n2 (φ n1) (by omega) (by omega)
    simp_all
  obtain ⟨σ, h_σ_mono, h_φ_φ'⟩ := greater_subseq_lemma φ φ' h_inj
  use (fun k ↦ if k = 0 then 0 else φ' (σ (k - 1))) ; simp +instances ; constructor
  · apply strictMono_nat_of_lt_succ ; intro n
    rcases (show n = 0 ∨ ¬ n = 0 by omega) with h_n | h_n <;> simp +instances [h_n]
    · exact h_φ'_0 (σ 0)
    have := h_φ'_n (σ (n - 1))
    have := h_φ_φ' (n - 1)
    grind
  · intro n
    simp +instances [da_acc_lang_iff_run_acc]
    rcases (show n = 0 ∨ ¬ n = 0 by omega) with h_n | h_n <;> simp +instances [h_n]
    · exact h_acc (σ 0)
    have h1 := h_φ'_n (σ (n - 1))
    have h2 := h_φ_φ' (n - 1) ; simp +instances [show n - 1 + 1 = n by omega] at h2
    have h3 := append_extract_extract (xs := as) (show φ' (σ (n - 1)) ≤ φ (σ (n - 1)) by omega)
      (show φ (σ (n - 1)) ≤ φ' (σ n) by omega)
    have h4 := h_run (σ (n - 1)) ; simp +instances [DA.RunOn] at h4
    simp +instances [← h3, DA.RunOn, da_run_from_on_append, h4]
    have h5 := append_extract_extract (xs := as) (show 0 ≤ φ (σ (n - 1)) by omega)
      (show φ (σ (n - 1)) ≤ φ' (σ n) by omega)
    simp +instances [← da_run_from_on_append, h5]
    exact h_acc (σ n)
end Automata
