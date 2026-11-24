-- Prove2me | solution 1 for AddUN.Coding.branch_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:40:23.225787+00:00
-- url     : https://prove2.me/submissions/ff631190-bc38-4002-acda-dce888ed2597

module
public import Definitions.Def_AddUN_SecondMoment
public import Definitions.Def_AddUN_TheoremB
public import Definitions.Def_AddUN_Coding
public import Theorems.Thm_AddUN_Coding_stage_coord
public import Theorems.Thm_AddUN_Coding_low_mono
public import Theorems.Thm_AddUN_Coding_isClopen_marker
public import Theorems.Thm_AddUN_Coding_isClopen_hit
public import Theorems.Thm_AddUN_Coding_determined_marker
public import Theorems.Thm_AddUN_Coding_determined_hit
public import Theorems.Thm_AddUN_Coding_real_marker
public import Theorems.Thm_AddUN_Coding_theta_succ_add_le
public import Theorems.Thm_AddUN_Coding_theta_succ_le
public import Theorems.Thm_AddUN_Coding_branch_succ_of_mem
public import Theorems.Thm_AddUN_Coding_branch_succ_of_notMem
public import Theorems.Thm_MeasureTheory_Determined_diff
public import Theorems.Thm_MeasureTheory_Determined_inter
public import Theorems.Thm_MeasureTheory_Determined_mono
public import Theorems.Thm_MeasureTheory_Determined_univ
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
open AddUN.Coding
variable {K : Set (ℕ → Bool)} {c : ℕ → Bool} {f : ℕ → ℕ} {n₀ : ℕ}
namespace AddUN.Coding
theorem _root_.solution (hn₀ : theta n₀ ≤ cantorMeasure.real K) (m : ℕ) :
    IsClosed (branch K c f n₀ m) ∧ Determined (low (n₀ + m)) (branch K c f n₀ m) ∧
      theta (n₀ + m) ≤ cantorMeasure.real (K ∩ branch K c f n₀ m) := by
  induction m with
  | zero => exact ⟨isClosed_univ, Determined.univ, by simpa [branch] using hn₀⟩
  | succ m ih =>
    obtain ⟨hc, hd, hθ⟩ := ih
    have hd' : Determined (low (n₀ + m + 1)) (branch K c f n₀ m) :=
      hd.mono (low_mono (Nat.le_succ _))
    by_cases hb : f (n₀ + m) ∈ bad K c (n₀ + m)
    · rw [branch_succ_of_mem hb]
      refine ⟨hc.sdiff ((isClopen_marker _ _).diff (isClopen_hit _ _ _)).isOpen,
        hd'.diff ((determined_marker _ _).diff (determined_hit _ _ _)), ?_⟩
      have hsub : K ∩ branch K c f n₀ m ⊆
          K ∩ (branch K c f n₀ m \ (marker (n₀ + m) (f (n₀ + m)) \
            hit c (n₀ + m) (f (n₀ + m)))) ∪ marker (n₀ + m) (f (n₀ + m)) := by
        intro w hw
        by_cases hA : w ∈ marker (n₀ + m) (f (n₀ + m)) \ hit c (n₀ + m) (f (n₀ + m))
        · exact Or.inr hA.1
        · exact Or.inl ⟨hw.1, hw.2, hA⟩
      have h1 := (measureReal_mono (μ := cantorMeasure) hsub).trans (measureReal_union_le _ _)
      rw [real_marker] at h1
      have h2 := theta_succ_add_le (n₀ + m)
      change theta (n₀ + m + 1) ≤ _
      linarith
    · rw [branch_succ_of_notMem hb]
      refine ⟨hc.inter (isClopen_hit _ _ _).isClosed, hd'.inter (determined_hit _ _ _), ?_⟩
      have hnb : (1 / 2) ^ (mu (n₀ + m) + (n₀ + m)) / 2 *
          cantorMeasure.real (K ∩ branch K c f n₀ m) ≤
          cantorMeasure.real (K ∩ branch K c f n₀ m ∩ hit c (n₀ + m) (f (n₀ + m))) :=
        not_lt.1 fun h ↦ hb ⟨_, hc.measurableSet, hd, hθ, h⟩
      rw [← inter_assoc]
      change theta (n₀ + m + 1) ≤ _
      refine (theta_succ_le (n₀ + m)).trans (le_trans ?_ hnb)
      exact mul_le_mul_of_nonneg_left hθ (by positivity)
end AddUN.Coding
