-- Prove2me | solution 1 for Automata.pair_acc_lang_frequently_from_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:45:42.404269+00:00
-- url     : https://prove2.me/submissions/272195e3-29b3-474e-8fb7-b45116e2d28b

import Definitions.Def_AutomataTheory_Automata_Hist
import Definitions.Def_AutomataTheory_Languages_RegLang
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Pair
import Theorems.Thm_P2M_Stream__get_extract__ebf059d6908b
import Theorems.Thm_P2M_segment__lower_bound_1c7600654899
import Theorems.Thm_P2M_segment__lower_val_a0fd010b0c15
import Theorems.Thm_P2M_segment__upper_bound_c7d48b2c3975
import Theorems.Thm_strict_mono_infinite


set_option autoImplicit true
open Function Set Filter Stream'
attribute [local implicit_reducible] Stream'
open Automata
attribute [local instance_reducible] NA.addHist
variable {A : Type}
variable {M : NA A} {acc : Set M.State}
namespace Automata
theorem _root_.solution {as : Stream' A} {ss : Stream' M.State} {φ : Stream' ℕ}
    (h_next : ∀ k, ss (k + 1) ∈ M.next (ss k) (as k)) (h_acc : ∃ᶠ k in Filter.atTop, ss k ∈ acc) (h_mono : StrictMono φ) :
    ∃ᶠ m in Filter.atTop, as.extract (φ m) (φ (m + 1)) ∈ M.PairAccLang acc (ss (φ m)) (ss (φ (m + 1))) := by
  have h_acc' := frequently_atTop.mp h_acc
  have h_mono' := frequently_atTop.mp <| Nat.frequently_atTop_iff_infinite.mpr <| strict_mono_infinite h_mono
  apply frequently_atTop.mpr ; intro m
  obtain ⟨k, h_k, h_k_acc⟩ := h_acc' (φ m)
  let n := Segment' φ k
  use n ; constructor
  · exact segment'_lower_val h_mono h_k
  · use (fun k ↦ ss (k + φ n)) ; constructor
    · have : φ n < φ (n + 1) := h_mono (show n < n + 1 by omega)
      simp (disch := omega) [NA.PairPath, length_extract, get_extract', (show φ (n + 1) - φ n + φ n = φ (n + 1) by omega)]
      intro j h_j ; have := h_next (j + φ n)
      simpa +instances [Function.comp_apply, (show j + 1 + φ n = j + φ n + 1 by omega), (show φ n + j = j + φ n by omega)]
    · have : φ 0 ≤ φ m := by simp +instances [Function.comp_apply, StrictMono.le_iff_le h_mono]
      have h1 : φ 0 ≤ k := by omega
      have : φ n ≤ k := by exact segment'_lower_bound h_mono h1
      use (k - φ n)
      simp +instances [Function.comp_apply, h_k_acc, length_extract, (show k - φ n + φ n = k by omega)]
      have : k < φ (n + 1) := by exact segment'_upper_bound h_mono h1
      omega
end Automata
