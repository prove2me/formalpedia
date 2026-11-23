-- Prove2me | solution 1 for Automata.acc_lang_concat_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:35:18.32526+00:00
-- url     : https://prove2.me/submissions/f1d88ea1-dc84-47a8-bbde-77968de49468

import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Automata_Concat
import Theorems.Thm_Automata_na_concat_fin_run_1
import Theorems.Thm_P2M_Stream__append_extract_extract_2ca0e177dfc2
import Theorems.Thm_P2M_Stream__extract_append_zero_right_6dd07cb04cbe
import Theorems.Thm_P2M_Stream__extract_drop_9b771096fa3e
import Theorems.Thm_P2M_Stream__extract_eq_nil_iff_c45b6d031ac4
import Theorems.Thm_P2M_Stream__get_append_left__364c5eb8ed49
import Theorems.Thm_P2M_Stream__get_extract__ebf059d6908b


set_option autoImplicit true
open Function Set Filter Sum Stream'
open Classical
open Automata
variable {A : Type} {M0 M1 : NA A} {acc0 : Set M0.State} {acc1 : Set M1.State}
namespace Automata
theorem _root_.solution :
    (M0.Concat acc0 M1).AcceptedLang (inr '' acc1) =
    (M0.AcceptedLang acc0) * (M1.AcceptedLang acc1 \ {[]}) := by
  ext al ; constructor
  · rintro ⟨m, as, ⟨ss, h_run, h_acc⟩, rfl⟩
    have h_s1_ex : ∃ s1, ss m = inr s1 := by
      rcases h_acc with ⟨s1, _, h_s1⟩
      use s1 ; rw [h_s1]
    obtain ⟨n, h_n, ⟨ss0, h_run0, h_acc0, h_ss0⟩, ⟨ss1, h_run1, h_ss1⟩⟩ := na_concat_fin_run_1.mp ⟨h_run, h_s1_ex⟩
    use (as.extract 0 n), (as.extract n m)
    simp +instances (disch := omega) [append_extract_extract, extract_eq_nil_iff, h_n]
    constructor
    · use n, as ; simp +instances ; use ss0
    · use (m - n), (as.drop n) ; simp +instances (disch := omega) [extract_drop]
      use ss1 ; simp +instances [h_run1]
      obtain ⟨s1, h_acc1, h_s1⟩ := h_ss1 m (by omega) (by omega) ▸ h_acc
      simpa +instances [← inr.inj h_s1]
  . rintro ⟨al0, al1, h_al0, h_al1, rfl⟩
    obtain ⟨h_al1, h_al1_ne⟩ := h_al1
    simp +instances at h_al1_ne
    rcases h_al0 with ⟨n, as0, ⟨⟨ss0, ⟨h_init0, h_next0⟩, h_acc0⟩, rfl⟩⟩
    rcases h_al1 with ⟨m, as1, ⟨⟨ss1, ⟨h_init1, h_next1⟩, h_acc1⟩, rfl⟩⟩
    have h_m : 0 < m := by simp +instances [extract_eq_nil_iff] at h_al1_ne ; omega
    let as := (as0.extract 0 n) ++ₛ as1
    use (n + m), as ; constructor
    · let ss := fun k ↦ if k < n + 1 then inl (ss0 k) else inr (ss1 (k - n))
      use ss ; constructor
      · suffices (M0.Concat acc0 M1).FinRun (n + m) as ss ∧ (∃ s1, ss (n + m) = inr s1) by tauto
        apply na_concat_fin_run_1.mpr
        use n ; constructor <;> [skip ; constructor]
        · omega
        · refine ⟨ss0, ⟨h_init0, ?_⟩, h_acc0, ?_⟩
          · intro k h_k
            have h1 : k < (as0.extract 0 n).length := by simp +instances [length_extract, h_k]
            simpa +instances (disch := omega) [as, get_append_left' h1, get_extract'] using h_next0 k h_k
          · intro k h_k
            simp only [ss, if_pos h_k] <;> rfl
        · use ss1 ; simp +instances ; constructor <;> [constructor ; skip]
          · exact h_init1
          · intro k h_k
            have h1 : (as0.extract 0 n).length = n := by simp +instances [length_extract]
            rw [← h1] ; simp +instances [as, drop_append_stream]
            exact h_next1 k h_k
          · intro k h_k h_km
            simp only [ss, if_neg (by omega : ¬ k < n + 1)] <;> rfl
      · use (ss1 m)
        have h_ss_nm : ss (n + m) = inr (ss1 m) := by
          have h_m1 : ¬ n + m < n + 1 := by omega
          simp only [ss, if_neg h_m1, Nat.add_sub_cancel_left]
        simp +instances [h_acc1, h_ss_nm] <;> rfl
    · have h1 : (as0.extract 0 n).length ≤ n + m := by simp +instances [length_extract]
      simp +instances [as, extract_append_zero_right h1, length_extract]
end Automata
