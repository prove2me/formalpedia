-- Prove2me | solution 1 for AddUN.exists_slalom_decode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:42:17.806449+00:00
-- url     : https://prove2.me/submissions/1ad0cc44-ddbe-487b-916d-adbd4967e156

module
public import Definitions.Def_AddUN_SecondMoment
public import Definitions.Def_AddUN_TheoremB
public import Definitions.Def_AddUN_Coding
public import Theorems.Thm_AddUN_Coding_lt_mu
public import Theorems.Thm_AddUN_Coding_stage_coord
public import Theorems.Thm_AddUN_Coding_hit_subset_marker
public import Theorems.Thm_AddUN_Coding_apply_of_mem_hit
public import Theorems.Thm_AddUN_Coding_theta_pos
public import Theorems.Thm_AddUN_Coding_card_le_of_subset_bad
public import Theorems.Thm_AddUN_Coding_finite_bad
public import Theorems.Thm_AddUN_Coding_branch_succ_of_mem
public import Theorems.Thm_AddUN_Coding_branch_succ_of_notMem
public import Theorems.Thm_AddUN_Coding_branch_succ_subset
public import Theorems.Thm_AddUN_Coding_branch_spec
public import Theorems.Thm_MeasureTheory_Determined_inter
public import Theorems.Thm_MeasureTheory_Determined_mono
public import Theorems.Thm_MeasureTheory_IsUniversallyNull_mono
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip


attribute [local simp] AddUN.Coding.stage_coord

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory
open AddUN
open Coding
namespace AddUN
theorem _root_.solution {K : Set (ℕ → Bool)} (hK : IsCompact K) (hKpos : cantorMeasure K ≠ 0)
    (c : ℕ → Bool) :
    ∃ S : ℕ → Finset ℕ, (∀ n, (S n).card ≤ 2 ^ (3 * mu n + n)) ∧
      ∀ f : ℕ → ℕ, (∃ᶠ n in atTop, f n ∉ S n) → ∃ w ∈ K, decode f w = c := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  refine ⟨fun n ↦ (finite_bad hKm c n).toFinset,
    fun n ↦ card_le_of_subset_bad hKm (c := c) (n := n) _ (by simp), fun f hf ↦ ?_⟩
  have hf' : ∃ᶠ n in atTop, f n ∉ bad K c n := hf.mono fun n hn ↦ by simpa using hn
  -- The first stage.
  have hKr : 0 < cantorMeasure.real K := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hKpos (measure_ne_top _ _)
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, theta n₀ ≤ cantorMeasure.real K := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < cantorMeasure.real K / 4 by positivity)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    have h1 : ((1 : ℝ) / 2) ^ mu n ≤ (1 / 2) ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (lt_mu n).le
    refine ⟨n, ?_⟩
    unfold theta
    linarith
  have hspec := fun m ↦ branch_spec (c := c) (f := f) hn₀ m
  -- A point in every set of the branch.
  obtain ⟨w, hw⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun m ↦ K ∩ branch K c f n₀ m)
    (fun m ↦ inter_subset_inter_right K (branch_succ_subset m))
    (fun m ↦ by
      by_contra hem
      have h0 := (hspec m).2.2
      rw [not_nonempty_iff_eq_empty.1 hem, measureReal_empty] at h0
      exact absurd (theta_pos (n₀ + m)) (not_lt.2 h0))
    (by simpa [branch] using hK) (fun m ↦ hK.isClosed.inter (hspec m).1)
  rw [mem_iInter] at hw
  refine ⟨w, (hw 0).1, ?_⟩
  -- From the stage `n₀` on, every marker of `w` on the branch is followed by the code.
  have h1 : ∀ m, w ∈ marker (n₀ + m) (f (n₀ + m)) → w ∈ hit c (n₀ + m) (f (n₀ + m)) := by
    intro m hmark
    have hm := (hw (m + 1)).2
    by_cases hb : f (n₀ + m) ∈ bad K c (n₀ + m)
    · rw [branch_succ_of_mem hb] at hm
      by_contra hhit
      exact hm.2 ⟨hmark, hhit⟩
    · rw [branch_succ_of_notMem hb] at hm
      exact hm.2
  have h2 : ∀ m, f (n₀ + m) ∉ bad K c (n₀ + m) → w ∈ hit c (n₀ + m) (f (n₀ + m)) := by
    intro m hb
    have hm := (hw (m + 1)).2
    rw [branch_succ_of_notMem hb] at hm
    exact hm.2
  ext i
  unfold decode
  cases hci : c i
  · rw [decide_eq_false_iff_not]
    intro hev
    obtain ⟨n, ⟨hnb, hn⟩, hnev⟩ :=
      ((hf'.and_eventually (eventually_ge_atTop (max n₀ (i + 1)))).and_eventually hev).exists
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (le_of_max_le_left hn)
    have hin : i < n₀ + m := le_of_max_le_right hn
    have hhit := h2 m hnb
    have := hnev ⟨hin, hit_subset_marker _ _ _ hhit⟩
    rw [apply_of_mem_hit hhit hin, hci] at this
    exact Bool.false_ne_true this
  · simp only [decide_eq_true_eq]
    filter_upwards [eventually_ge_atTop n₀] with n hn hmark
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [apply_of_mem_hit (h1 m hmark.2) hmark.1, hci]
end AddUN
