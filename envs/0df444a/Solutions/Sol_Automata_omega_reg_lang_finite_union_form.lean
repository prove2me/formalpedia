-- Prove2me | solution 1 for Automata.omega_reg_lang_finite_union_form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:46:49.62627+00:00
-- url     : https://prove2.me/submissions/5edc0508-3a8c-4a0e-91b9-62e70a6e3fe7

import Definitions.Def_AutomataTheory_Automata_Hist
import Definitions.Def_AutomataTheory_Languages_RegLang
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Pair
import Theorems.Thm_P2M_Stream__append_extract_drop_29d8f2c46a9f
import Theorems.Thm_P2M_Stream__extract_drop_9b771096fa3e
import Theorems.Thm_P2M_Stream__get_append_left__364c5eb8ed49
import Theorems.Thm_P2M_Stream__get_append_right__3668139ab712
import Theorems.Thm_P2M_Stream__get_drop__05b839498f63
import Theorems.Thm_P2M_Stream__get_extract__ebf059d6908b
import Theorems.Thm_frequently_in_finite_set
import Theorems.Thm_segment_idem
import Theorems.Thm_segment_lower_bound
import Theorems.Thm_segment_range_val
import Theorems.Thm_segment_upper_bound
import Theorems.Thm_segment_zero
import Theorems.Thm_strict_mono_infinite


set_option autoImplicit true
open Function Set Filter Stream'
attribute [local implicit_reducible] Stream'
open Automata
attribute [local instance_reducible] NA.addHist
variable {A : Type}
variable {M : NA A} {acc : Set M.State}
attribute [local instance_reducible] NA.SingleInit
namespace Automata
theorem _root_.solution [h_fin : Finite M.State] :
    M.AcceptedOmegaLang acc = ⋃ s0 ∈ M.init, ⋃ sa ∈ acc, (M.PairLang s0 sa) * (M.PairLang sa sa)^ω := by
  ext as ; simp ; constructor
  · rintro ⟨ss, ⟨h_init, h_next⟩, h_acc⟩
    obtain ⟨sa, h_sa, h_acc⟩ := frequently_in_finite_set.mp h_acc
    use (ss 0) ; simp +instances [Function.comp_apply, h_init]
    use sa ; simp +instances [Function.comp_apply, h_sa]
    have h_inf := Nat.frequently_atTop_iff_infinite.mp h_acc
    let nth_sa := Nat.nth (fun k ↦ ss k = sa)
    have h_nth_sa : ∀ n, ss (nth_sa n) = sa := by exact Nat.nth_mem_of_infinite h_inf
    have h_mono : StrictMono nth_sa := by exact Nat.nth_strictMono h_inf
    use (as.extract 0 (nth_sa 0)), (as.drop (nth_sa 0))
    simp +instances [Function.comp_apply, append_extract_drop] ; constructor
    · use ss ; simp (disch := omega) [NA.PairPath, h_nth_sa, h_next, length_extract, get_extract']
    use (fun n ↦ nth_sa n - nth_sa 0) ; simp ; constructor
    · intro m n h_mn ; simp
      have h_nth_mn := h_mono h_mn
      have h_nth_0m := StrictMono.monotone h_mono (show 0 ≤ m by omega)
      have h_nth_0n := StrictMono.monotone h_mono (show 0 ≤ n by omega)
      omega
    intro n
    have h_nth_0n := StrictMono.monotone h_mono (show 0 ≤ n by omega)
    have h_nth_nn1 := h_mono (show n < n + 1 by omega)
    have h1 : nth_sa 0 + (nth_sa n - nth_sa 0) = nth_sa n := by omega
    have h2 : nth_sa 0 + (nth_sa (n + 1) - nth_sa 0) = nth_sa (n + 1) := by omega
    simp +instances [Function.comp_apply, extract_drop, h1, h2]
    use (ss.drop (nth_sa n))
    simp (disch := omega) [NA.PairPath, h_nth_sa, length_extract, get_drop', get_extract']
    intro k h_k ; specialize h_next (k + nth_sa n)
    have h3 : nth_sa n + (k + 1) = k + nth_sa n + 1 := by omega
    have h4 : nth_sa n + k = k + nth_sa n := by omega
    simp +instances [Function.comp_apply, h_next, h3, h4]
  · rintro ⟨s0, h_s0, sa, h_sa, al0, as1, ⟨ss0, h_path0⟩, ⟨nth_sa, h_mono, h_sa_0, h_path1⟩, rfl⟩
    choose nth_ss h_nth_ss using h_path1
    let seg k := Segment nth_sa (k - al0.length)
    let ss k := if k < al0.length then ss0 k else nth_ss (seg k) (k - nth_sa (seg k) - al0.length)
    use ss ; constructor
    · constructor
      · rcases (show al0.length > 0 ∨ al0.length = 0 by omega) with h_al0 | h_al0
        · simp +instances [Function.comp_apply, ss, h_al0, h_path0.1, h_s0]
        have h_seg_0 : seg 0 = 0 := by simp +instances [Function.comp_apply, seg, segment_zero h_mono h_sa_0]
        simp +instances [Function.comp_apply, ss, h_al0, h_seg_0, (h_nth_ss 0).1, ← h_path0.2.1, h_path0.1, h_s0]
      intro k
      rcases (show k + 1 < al0.length ∨ k + 1 = al0.length ∨ k ≥ al0.length by omega) with h_k | h_k | h_k
      · have h_k' : k < al0.length := by omega
        have h_next := h_path0.2.2 k h_k'
        simp +instances [Function.comp_apply, ss, h_k, h_k', h_next, get_append_left']
      · have h_k' : k < al0.length := by omega
        have h_next := h_path0.2.2 k h_k'
        simp +instances [Function.comp_apply, h_k, h_path0.2.1] at h_next
        simp +instances [Function.comp_apply, ss, h_k, h_k', seg, segment_zero h_mono h_sa_0, (h_nth_ss 0).1, h_next, get_append_left']
      · have h_k' : ¬ k < al0.length := by omega
        have h_k'' : ¬ k + 1 < al0.length := by omega
        have h_lo := segment_lower_bound h_mono h_sa_0 (k - al0.length)
        have h_hi := segment_upper_bound h_mono h_sa_0 (k - al0.length)
        simp +instances [Function.comp_apply, ss, h_k', h_k'', seg]
        have h_next := (h_nth_ss (Segment nth_sa (k - al0.length))).2.2
          <| (k - nth_sa (Segment nth_sa (k - al0.length)) - al0.length)
        simp (disch := omega) [length_extract, get_extract'] at h_next
        specialize h_next (by omega)
        have h1 : nth_sa (Segment nth_sa (k - al0.length)) + (k - nth_sa (Segment nth_sa (k - al0.length)) - al0.length)
          = k - al0.length := by omega
        have h2 : k - nth_sa (Segment nth_sa (k - al0.length)) - al0.length + 1
          = k + 1 - nth_sa (Segment nth_sa (k - al0.length)) - al0.length := by omega
        simp +instances [Function.comp_apply, h1, h2] at h_next
        rcases (show k + 1 - al0.length < nth_sa (Segment nth_sa (k - al0.length) + 1) ∨
                     k + 1 - al0.length = nth_sa (Segment nth_sa (k - al0.length) + 1) by omega) with h_k1 | h_k1
        · have h3 : Segment nth_sa (k + 1 - al0.length) = Segment nth_sa (k - al0.length) := by
            exact segment_range_val h_mono (hu := h_k1) (hl := by omega)
          simp +instances [Function.comp_apply, h3, h_next, get_append_right' h_k]
        · have h3 : k + 1 - nth_sa (Segment nth_sa (k - al0.length) + 1) - al0.length = 0 := by omega
          have h4 := (h_nth_ss (Segment nth_sa (k - al0.length) + 1)).1
          simp +instances [Function.comp_apply, h_k1, segment_idem h_mono, h3, h4]
          have h5 := (h_nth_ss (Segment nth_sa (k - al0.length))).2.1
          have h6 : k + 1 - al0.length - nth_sa (Segment nth_sa (k - al0.length))
            = k + 1 - nth_sa (Segment nth_sa (k - al0.length)) - al0.length := by omega
          simp +instances [Function.comp_apply, ← h_k1, h6, length_extract] at h5
          simp +instances [Function.comp_apply, h5] at h_next
          simp (disch := omega) [get_append_right', h_next]
    · let φ k := nth_sa k + al0.length
      have h_φ_mono : StrictMono φ := by
        intro m n h_mn ; simp +instances [Function.comp_apply, φ] ; apply h_mono h_mn
      have h_φ_range : range φ ⊆ {k | ss k ∈ acc} := by
        rintro k ⟨n, rfl⟩
        simp +instances [Function.comp_apply, φ, ss, seg, segment_idem h_mono, (h_nth_ss n).1, h_sa]
      apply Nat.frequently_atTop_iff_infinite.mpr
      apply Infinite.mono h_φ_range
      exact strict_mono_infinite h_φ_mono
end Automata
