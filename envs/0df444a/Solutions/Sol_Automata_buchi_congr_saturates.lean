-- Prove2me | solution 1 for Automata.buchi_congr_saturates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:49:50.047927+00:00
-- url     : https://prove2.me/submissions/ac958af7-3881-4f43-82c4-2945cbb01e62

import Definitions.Def_AutomataTheory_Automata_Pair
import Definitions.Def_AutomataTheory_Mathlib_InfGraphRamsey
import Definitions.Def_AutomataTheory_Congruences_BuchiCongr
import Theorems.Thm_Automata_pair_acc_lang_frequently_from_run
import Theorems.Thm_Automata_pair_acc_lang_frequently_to_run
import Theorems.Thm_Automata_pair_lang_fin_subseq
import Theorems.Thm_P2M_Stream__extract_drop_9b771096fa3e
import Theorems.Thm_P2M_Stream__get_drop__05b839498f63
import Theorems.Thm_P2M_Stream__get_extract__ebf059d6908b
import Theorems.Thm_base_zero_shift
import Theorems.Thm_base_zero_strict_mono
import Theorems.Thm_congruence_same_eqvcls_imp_eq
import Theorems.Thm_mem_ConcatInf_IterOmega


set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {A : Type}
variable {M : NA A} {acc : Set M.State}
namespace Automata
theorem _root_.solution : (M.BuchiCongr acc).Saturates (M.AcceptedOmegaLang acc) := by
  rintro p q ⟨as, h_congr, ss, ⟨h_init, h_next⟩, h_acc⟩ as' h_congr'
  obtain ⟨φ, h_mono, h_eqv_p, h_eqv_q⟩ := mem_ConcatInf_IterOmega h_congr
  obtain ⟨φ', h_mono', h_eqv_p', h_eqv_q'⟩ := mem_ConcatInf_IterOmega h_congr'
  have h_congr_p := congruence_same_eqvcls_imp_eq h_eqv_p h_eqv_p'
  have h_congr_q := fun m ↦ congruence_same_eqvcls_imp_eq (h_eqv_q m) (h_eqv_q' m)
  have h_pair_0 := pair_lang_fin_subseq h_next (show 0 ≤ φ 0 by omega)
  have h_pair_1 := fun m ↦ pair_lang_fin_subseq h_next (le_of_lt <| h_mono (show m < m + 1 by omega))
  have h_pair_0' := (h_congr_p (ss 0) (ss (φ 0))).1.mp <| h_pair_0
  have h_pair_1' := fun m ↦ (h_congr_q m (ss (φ m)) (ss (φ (m + 1)))).1.mp <| h_pair_1 m
  have h_inf := pair_acc_lang_frequently_from_run h_next h_acc h_mono
  have h_inf' : ∃ᶠ m in atTop, as'.extract (φ' m) (φ' (m + 1)) ∈ M.PairAccLang acc (ss (φ m)) (ss (φ (m + 1))) := by
    apply Frequently.mono h_inf ; intro m
    exact (h_congr_q m (ss (φ m)) (ss (φ (m + 1)))).2.mp
  obtain ⟨ss0', h_ss_0, h_ss_φ0, h_next0'⟩ := h_pair_0'
  simp (disch := omega) [length_extract, get_extract'] at h_ss_φ0 h_next0'
  have h_lem1 : ∀ m,  (as'.drop (φ' 0)).extract (φ' m - φ' 0) (φ' (m + 1) - φ' 0) = as'.extract (φ' m) (φ' (m + 1)) := by
    intro m
    have := StrictMono.monotone h_mono' (show 0 ≤ m by omega)
    have := StrictMono.monotone h_mono' (show 0 ≤ m + 1 by omega)
    simp [extract_drop, (show φ' 0 + (φ' m - φ' 0) = φ' m by omega),
      (show φ' 0 + (φ' (m + 1) - φ' 0) = φ' (m + 1) by omega)]
  obtain ⟨ss1', h_ss1', h_next1', h_acc1'⟩ := pair_acc_lang_frequently_to_run
    (acc := acc) (φ := (φ' · - φ' 0)) (as := as'.drop (φ' 0))
    (ss' := fun k ↦ ss (φ k)) (base_zero_strict_mono h_mono') (base_zero_shift φ')
    (by simp [h_lem1, h_pair_1']) (by simp [h_lem1, h_inf'])
  use (fun k ↦ if k < φ' 0 then ss0' k else ss1' (k - φ' 0))
  constructor
  · constructor
    · rcases (show φ' 0 = 0 ∨ φ' 0 > 0 by omega) with h_k | h_k
      · simp [h_k] ; grind
      · grind
    intro k
    rcases (show k + 1 < φ' 0 ∨ k + 1 = φ' 0 ∨ k + 1 > φ' 0 by omega) with h_k | h_k | h_k
    · grind
    · have h_k' : k < φ' 0 := by omega
      have h1 := h_ss1' 0
      simp at h1
      have h2 := h_next0' k h_k'
      simp [h_k, h_ss_φ0] at h2
      simp [h_k, h_k', h1, h2]
    · simp [(show ¬ k < φ' 0 by omega), (show ¬ k + 1 < φ' 0 by omega)]
      have h1 := h_next1' (k - φ' 0)
      simp [get_drop', (show φ' 0 + (k - φ' 0) = k by omega)] at h1
      simp [(show k + 1 - φ' 0 = k - φ' 0 + 1 by omega), h1]
  · simp [Filter.frequently_atTop] at h_acc1' ⊢
    intro k0
    obtain ⟨k1, h_k1, h_k1_acc⟩ := h_acc1' (k0 + φ' 0)
    use (k1 + φ' 0)
    simp [(show k0 ≤ k1 + φ' 0 by omega), h_k1_acc]
end Automata
