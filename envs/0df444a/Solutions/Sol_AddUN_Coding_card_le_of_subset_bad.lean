-- Prove2me | solution 1 for AddUN.Coding.card_le_of_subset_bad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:40:00.878817+00:00
-- url     : https://prove2.me/submissions/2e63b1d9-83fb-4781-ae77-3622a56e15a6

module
public import Definitions.Def_AddUN_SecondMoment
public import Definitions.Def_AddUN_TheoremB
public import Definitions.Def_AddUN_Coding
public import Theorems.Thm_AddUN_Coding_card_block
public import Theorems.Thm_AddUN_Coding_disjoint_low_block
public import Theorems.Thm_AddUN_Coding_disjoint_block
public import Theorems.Thm_AddUN_Coding_theta_pos
public import Theorems.Thm_MeasureTheory_Determined_univ
public import Theorems.Thm_MeasureTheory_second_moment


set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory
open AddUN
open AddUN.Coding
namespace AddUN.Coding
theorem _root_.solution {K : Set (ℕ → Bool)} (hK : MeasurableSet K) {c : ℕ → Bool} {n : ℕ}
    (J : Finset ℕ) (hJ : (J : Set ℕ) ⊆ bad K c n) : J.card ≤ 2 ^ (3 * mu n + n) := by
  have hex : ∀ k, ∃ E : Set (ℕ → Bool), k ∈ J → MeasurableSet E ∧ Determined (low n) E ∧
      theta n ≤ cantorMeasure.real (K ∩ E) ∧
      cantorMeasure.real (K ∩ E ∩ hit c n k) <
        (1 / 2) ^ (mu n + n) / 2 * cantorMeasure.real (K ∩ E) := fun k ↦ by
    by_cases hk : k ∈ J
    · obtain ⟨E, hE⟩ := hJ hk
      exact ⟨E, fun _ ↦ hE⟩
    · exact ⟨univ, fun h ↦ absurd h hk⟩
  choose E hE using hex
  have key := second_moment hK J E (fun k ↦ block n k) (pattern c) (mu n + n) (low n)
    (theta_pos n) (fun k hk ↦ (hE k hk).1) (fun k hk ↦ (hE k hk).2.1)
    (fun k _ ↦ disjoint_low_block n k) (fun k _ k' _ h ↦ disjoint_block h)
    (fun k _ ↦ card_block n k) (fun k hk ↦ (hE k hk).2.2.1) (fun k hk ↦ (hE k hk).2.2.2.le)
  have e : ((1 : ℝ) / 2) ^ (mu n + n) * theta n ^ 2 = 16 * (1 / 2) ^ (3 * mu n + n) := by
    unfold theta
    rw [mul_pow, ← pow_mul, show 3 * mu n + n = mu n + n + mu n * 2 by ring, pow_add (1 / 2 : ℝ)]
    ring
  rw [mul_assoc, e] at key
  have hk2 : ((1 : ℝ) / 2) ^ (3 * mu n + n) * 2 ^ (3 * mu n + n) = 1 := by
    rw [← mul_pow]
    norm_num
  have hpos : (0 : ℝ) < 2 ^ (3 * mu n + n) := by positivity
  have hle : (J.card : ℝ) ≤ 2 ^ (3 * mu n + n) := by
    calc (J.card : ℝ) = J.card * (1 / 2) ^ (3 * mu n + n) * 2 ^ (3 * mu n + n) := by
          rw [mul_assoc, hk2, mul_one]
      _ ≤ 1 / 4 * 2 ^ (3 * mu n + n) := mul_le_mul_of_nonneg_right (by linarith) hpos.le
      _ ≤ 2 ^ (3 * mu n + n) := by linarith
  exact_mod_cast hle
end AddUN.Coding
