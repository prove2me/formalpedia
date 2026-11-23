-- Prove2me | solution 1 for Automata.choueka_lang_omega_power_subset_omega_limit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:52:02.933797+00:00
-- url     : https://prove2.me/submissions/be86c194-e5c4-4503-a1d0-e6625d7c866a

import Definitions.Def_AutomataTheory_Languages_RegLang
import Definitions.Def_AutomataTheory_Mathlib_InfGraphRamsey
import Definitions.Def_AutomataTheory_Languages_ChouekaLemma
import Theorems.Thm_Automata_ramsey_lemma
import Theorems.Thm_Automata_da_acc_lang_iff_run_acc
import Theorems.Thm_P2M_Stream__append_extract_drop_29d8f2c46a9f
import Theorems.Thm_P2M_Stream__append_extract_extract_2ca0e177dfc2
import Theorems.Thm_P2M_Stream__extract_drop_9b771096fa3e
import Theorems.Thm_P2M_Stream__extract_eq_nil_7f26d60de260
import Theorems.Thm_P2M_Stream__extract_extract2__d35761143a43
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
theorem _root_.solution [Inhabited A]
    {M : DA A} [Finite M.State] {acc : Set M.State}
    {V : Set (List A)} (h_lang : M.toNA.AcceptedLang acc = V∗) :
    V^ω ⊆ V∗ * (M.ChouekaLang acc)↗ω := by
  rintro as ⟨φ, h_φ_mono, h_φ_0, h_φ_V⟩
  have h_kstar : ∀ i j, i ≤ j → (as.extract (φ i) (φ (j))) ∈ V∗ := by
    intro i j h_ij ; simp +instances [instIterStar, IterStar]
    use (j - i) ; generalize h_n : j - i = n
    induction' n with n h_ind generalizing i j <;> simp +instances [instIterFin, IterFin]
    · simp +instances [extract_eq_nil, (show i = j by omega)]
    use (as.extract (φ i) (φ (j - 1))), (as.extract (φ (j - 1)) (φ j)) ; constructorm* _ ∧ _
    · exact h_ind i (j - 1) (by omega) (by omega)
    · specialize h_φ_V (j - 1)
      simp +instances [(show j - 1 + 1 = j by omega)] at h_φ_V
      exact h_φ_V
    · apply append_extract_extract <;>
        apply StrictMono.monotone h_φ_mono <;> omega
  let color (i j : ℕ) : M.State := M.RunOn (as.extract i j)
  have h_color : ∀ i j, i < j → color (φ i) (φ j) ∈ acc := by
    intro i j h_ij ; simp +instances [color, ← da_acc_lang_iff_run_acc, h_lang]
    apply h_kstar ; omega
  obtain ⟨s, h_acc, σ, h_σ_mono, h_σ_color⟩ := ramsey_lemma (acc.toFinite) h_φ_mono h_color
  simp +instances [color] at h_σ_color
  use (as.extract 0 (φ (σ 0))), (as.drop (φ (σ 0)))
  simp +instances [append_extract_drop] ; constructor
  · specialize h_kstar 0 (σ 0) (by omega)
    simp +instances [h_φ_0] at h_kstar
    exact h_kstar
  apply frequently_iff_strict_mono.mpr
  simp +instances [extract_drop]
  let p k j := φ (σ k) < j ∧ j ≤ φ (σ (k + 1)) ∧ M.RunOn (as.extract (φ (σ k)) j) = M.RunOn (as.extract (φ (σ 0)) j)
  have h_p_ex : ∀ k, ∃ j, p k j := by
    intro k ; use (φ (σ (k + 1)))
    simp +instances [p, h_φ_mono <| h_σ_mono (show k < k + 1 by omega)]
    have := h_σ_color k (k + 1) (by omega)
    have := h_σ_color 0 (k + 1) (by omega)
    simp_all
  let ξ k := Nat.find (h_p_ex k)
  have h_ξ_spec : ∀ k, p k (ξ k) := by intro k ; exact Nat.find_spec (h_p_ex k)
  have h_ξ_min : ∀ k j, j < ξ k → ¬ p k j := by intro k j h_j ; exact Nat.find_min (h_p_ex k) h_j
  use (fun k ↦ ξ (k + 1) - φ (σ 0)) ; constructor
  · intro j k h_jk ; simp +instances
    obtain ⟨_, _, _⟩ := h_ξ_spec (j + 1)
    obtain ⟨_, _, _⟩ := h_ξ_spec (k + 1)
    have := h_φ_mono <| h_σ_mono (show 0 < j + 1 by omega)
    have := StrictMono.monotone h_φ_mono <| StrictMono.monotone h_σ_mono (show j + 1 + 1 ≤ k + 1 by omega)
    omega
  intro k ; use (φ (σ (k + 1)) - φ (σ 0))
  have h_k1_0 := h_φ_mono <| h_σ_mono (show 0 < k + 1 by omega)
  obtain ⟨h_k1_ξ, h_k1_ξ', h_k1_run⟩ := h_ξ_spec (k + 1)
  have h1 : φ (σ (k + 1)) - φ (σ 0) < ξ (k + 1) - φ (σ 0) := by omega
  have h2 : φ (σ 0) + (ξ (k + 1) - φ (σ 0)) = ξ (k + 1) := by omega
  have h3 : φ (σ 0) + (φ (σ (k + 1)) - φ (σ 0)) = φ (σ (k + 1)) := by omega
  simp +instances [-List.extract_eq_take_drop, length_extract, h_k1_0, h1]
  rw [h2]
  simp +instances [-List.extract_eq_take_drop, extract_extract2' (le_of_lt h1), extract_extract2']
  rw [h2, h3]
  simp +instances [-List.extract_eq_take_drop, h_k1_run, h_σ_color 0 (k + 1) (by omega), h_acc]
  intro j h_j1 h_j2
  have h_j_min := h_ξ_min (k + 1) (φ (σ 0) + j) (by omega)
  simp +instances [p] at h_j_min
  specialize h_j_min (by omega) (by omega)
  simp +instances [-List.extract_eq_take_drop, extract_extract2' (le_of_lt h_j2), h3, h_j_min]
end Automata
