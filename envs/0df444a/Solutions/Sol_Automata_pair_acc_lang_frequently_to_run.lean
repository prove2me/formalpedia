-- Prove2me | solution 1 for Automata.pair_acc_lang_frequently_to_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:45:47.143066+00:00
-- url     : https://prove2.me/submissions/e4a5fa19-c8d5-41d3-9c74-d0538e86d26a

import Definitions.Def_AutomataTheory_Automata_Hist
import Definitions.Def_AutomataTheory_Languages_RegLang
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Pair
import Theorems.Thm_P2M_Stream__get_extract__ebf059d6908b
import Theorems.Thm_segment_idem
import Theorems.Thm_segment_lower_bound
import Theorems.Thm_segment_range_val
import Theorems.Thm_segment_upper_bound
import Theorems.Thm_strict_mono_infinite


set_option autoImplicit true
open Function Set Filter Stream'
attribute [local implicit_reducible] Stream'
open Automata
attribute [local instance_reducible] NA.addHist
variable {A : Type}
variable {M : NA A} {acc : Set M.State}
namespace Automata
theorem _root_.solution {φ : Stream' ℕ} {as : Stream' A} (ss' : Stream' M.State)
    (h_mono : StrictMono φ) (h_zero : φ 0 = 0)
    (h_pair : ∀ m, as.extract (φ m) (φ (m + 1)) ∈ M.PairLang (ss' m) (ss' (m + 1)))
    (h_inf : ∃ᶠ m in atTop, as.extract (φ m) (φ (m + 1)) ∈ M.PairAccLang acc (ss' m) (ss' (m + 1))) :
    ∃ ss : Stream' M.State, (∀ m, ss (φ m) = ss' m) ∧
      (∀ k, ss (k + 1) ∈ M.next (ss k) (as (k))) ∧ (∃ᶠ k in atTop, ss k ∈ acc) := by
  have h_exists : ∀ m, ∃ ps, M.PairPath (ss' m) (ss' (m + 1)) (as.extract (φ m) (φ (m + 1))) ps ∧
    ( as.extract (φ m) (φ (m + 1)) ∈ M.PairAccLang acc (ss' m) (ss' (m + 1)) →
      M.PairAccPath acc (ss' m) (ss' (m + 1)) (as.extract (φ m) (φ (m + 1))) ps ) := by
    intro m
    rcases Classical.em (as.extract (φ m) (φ (m + 1)) ∈ M.PairAccLang acc (ss' m) (ss' (m + 1))) with h_acc | h_acc
    <;> simp +instances [Function.comp_apply, h_acc]
    · obtain ⟨ps, h_ps⟩ := h_acc
      use ps ; simp +instances [Function.comp_apply, h_ps, h_ps.1]
    · obtain ⟨ps, h_ps⟩ := h_pair m
      use ps
  choose ps h_ps using h_exists
  use (fun k ↦ ps (Segment φ k) (k - φ (Segment φ k)))
  constructorm* _ ∧ _
  · intro m
    have h0 := (h_ps (Segment φ (φ m))).1.1
    simp +instances [Function.comp_apply, segment_idem h_mono] at h0
    simp +instances [Function.comp_apply, segment_idem h_mono, h0]
  · intro k
    have := segment_lower_bound h_mono h_zero k
    have := segment_upper_bound h_mono h_zero k
    have h_next := (h_ps (Segment φ k)).1.2.2 (k - φ (Segment φ k))
    simp +instances [Function.comp_apply, length_extract, get_extract',
      (show φ (Segment φ k) + (k - φ (Segment φ k)) = k by omega),
      (show k - φ (Segment φ k) + 1 = k + 1 - φ (Segment φ k) by omega),
      (show k - φ (Segment φ k) < φ (Segment φ k + 1) - φ (Segment φ k) by omega)] at h_next
    rcases (show k + 1 < φ (Segment φ k + 1) ∨ k + 1 = φ (Segment φ k + 1) by omega) with h_k | h_k
    · have h1 := segment_range_val h_mono (by omega) h_k
      simp +instances [Function.comp_apply, h1, h_next]
    · have h1 := (h_ps (Segment φ k)).1.2.1
      simp +instances [Function.comp_apply, length_extract] at h1
      simp +instances [Function.comp_apply, h_k, h1] at h_next
      have h2 : Segment φ (k + 1) = Segment φ k + 1 := by simp +instances [Function.comp_apply, h_k, segment_idem h_mono]
      have h3 := (h_ps (Segment φ k + 1)).1.1
      simp +instances [Function.comp_apply, ← h_k, h2, h3, h_next]
  · have h_inf' : ∃ᶠ m in atTop, ∃ k < φ (m + 1) - φ m + 1, ps m k ∈ acc := by
      apply Frequently.mono h_inf
      intro m h_m
      obtain ⟨_, k, h_k, h_acc⟩ := (h_ps m).2 h_m
      simp +instances [Function.comp_apply, length_extract] at h_k
      exact ⟨k, by omega, h_acc⟩
    have h_φ_inf := Filter.frequently_atTop'.mp <| Nat.frequently_atTop_iff_infinite.mpr <| strict_mono_infinite h_mono
    apply Filter.frequently_atTop'.mpr
    intro k0
    obtain ⟨k1, h_k1, m1, rfl⟩ := h_φ_inf k0
    obtain ⟨m2, h_m2, k2, h_k2, h_acc⟩ := Filter.frequently_atTop'.mp h_inf' m1
    have := h_mono h_m2
    have : φ m2 < φ (m2 + 1) := by apply h_mono ; omega
    rcases (show k2 < φ (m2 + 1) - φ m2 ∨ k2 = φ (m2 + 1) - φ m2 by omega) with h_k2' | rfl
    · use (k2 + φ m2) ; constructor
      · omega
      have h1 := segment_range_val h_mono (show φ m2 ≤ k2 + φ m2 by omega) (by omega)
      simp +instances [Function.comp_apply, h1, h_acc]
    · use (φ (m2 + 1)) ; constructor
      · omega
      have h2 := (h_ps (m2)).1.2.1
      simp +instances [Function.comp_apply, length_extract] at h2
      simp +instances [Function.comp_apply, h2] at h_acc
      simp +instances [Function.comp_apply, segment_idem h_mono, (h_ps (m2 + 1)).1.1, h_acc]
end Automata
