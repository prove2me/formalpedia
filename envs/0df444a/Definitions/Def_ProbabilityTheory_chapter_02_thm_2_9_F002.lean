-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_02_thm_2_9_F002
-- name    : ProbabilityTheory_chapter_02_thm_2_9_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T18:39:24.85823+00:00
-- url     : https://prove2.me/theorems/2eda587b-6089-43e4-935f-24d57225cf1d
-- title:
--   Chapter 2, thm_2_9: supporting Lean bundle F002
-- statement:
--   Supporting Lean declarations for Chapter 2, source module `thm_2_9`: `vitali_subset_I`, `translate_subset_Ico`, `translate_subset_I`, `measure_vitali_invariant`, `sum_vitali_eq_union`, and 1 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_9.lean

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_9_F000
import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_9_F001
import Mathlib.Data.Rat.Denumerable
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.Tactic

noncomputable section Vitali_set

namespace Vitali_set

open Classical   
open Rat
open Set

lemma vitali_subset_I : VitaliSet ⊆ I := by

  rintro x ⟨c, rfl⟩

  exact (@Quotient.out _ vitaliSetoid c).2

lemma translate_subset_Ico (A : Set ℝ) (d : ℝ) : translate A d ⊆ Ico 0 1 := by
  rintro x ⟨y, _, rfl⟩
  rw [Set.mem_Ico]
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

lemma translate_subset_I (A : Set ℝ) (d : ℝ) : translate A d ⊆ I := by
  intro x hx
  have := translate_subset_Ico A d hx
  exact Ico_subset_Icc_self this

private lemma vitali_seq_disjoint_source_local : Pairwise (fun i j => Disjoint (VitaliSeq i) (VitaliSeq j)) := by
  intro i j hij
  rw [Set.disjoint_iff_inter_eq_empty]
  ext x
  -- Expand definitions to expose the elements v1, v2 and the fractional part logic
  simp only [VitaliSeq, translate, mem_inter_iff, mem_image, Set.mem_empty_iff_false, iff_false]

  intro h_inter
  rcases h_inter with ⟨h_i, h_j⟩
  -- Unpack the first witness (from VitaliSeq i)
  rcases h_i with ⟨v1, hv1_mem, hx1⟩
  -- Unpack the second witness (from VitaliSeq j)
  rcases h_j with ⟨v2, hv2_mem, hx2⟩

  -- 1. Combine the fractional equations
  have h_fract_eq : Int.fract (v1 + q_seq i) = Int.fract (v2 + q_seq j) := by rw [hx1, ← hx2]
  rw [Int.fract_eq_fract] at h_fract_eq
  rcases h_fract_eq with ⟨k, hk⟩

  have h_fract_eq : Int.fract (v1 + q_seq i) = Int.fract (v2 + q_seq j)
    := by rw [hx1, ← hx2]
  rw [Int.fract_eq_fract] at h_fract_eq
  rcases h_fract_eq with ⟨k, hk⟩

  -- 2. Rearrange: v1 - v2 = qj - qi + k. This implies v1 ~ v2.
  have h_diff : v1 - v2 = q_seq j - q_seq i + k := by linarith
  have h_rel : vitali_rel v1 v2 := by
    use (q_bij j).val - (q_bij i).val + k
    rw [h_diff]; simp [q_seq]

  -- 3. Since v1 and v2 are representatives from the quotient,
  -- v1 ~ v2 implies they are the same representative.
  have h_v_eq : v1 = v2 := by
    -- Retrieve the quotient classes c1, c2 now
    rcases hv1_mem with ⟨c1, rfl⟩
    rcases hv2_mem with ⟨c2, rfl⟩

    -- v1 corresponds to representative of c1, v2 to c2.
    -- v1 ~ v2 means Quotient.mk v1 = Quotient.mk v2
    -- The Setoid is defined on I, so we use the subtype elements.
    let v1_sub : I := @Quotient.out _ vitaliSetoid c1
    let v2_sub : I := @Quotient.out _ vitaliSetoid c2

    -- The relation h_rel is exactly the equivalence relation for the subtype elements
    have h_equiv : v1_sub ≈ v2_sub := h_rel

    -- Therefore their classes are equal
    have h_mk_eq : Quotient.mk vitaliSetoid v1_sub = Quotient.mk vitaliSetoid v2_sub :=
      Quotient.sound h_equiv

    -- Since they are output of Quotient.out, their class is just c1 (and c2)
    rw [Quotient.out_eq c1] at h_mk_eq
    rw [Quotient.out_eq c2] at h_mk_eq

    -- So c1 = c2, which implies v1 = v2
    rw [h_mk_eq]

  subst h_v_eq

  -- 4. Now the equation is qj - qi + k = 0
  have h_k_eq : q_seq j - q_seq i + k = 0 := by linarith [hk]

  -- 5. Bound k. Since q_seq ∈ [0, 1), the difference is in (-1, 1). Integer k must be 0.
  have h_k_zero : k = 0 := by
    -- Explicitly state bounds for q_seq in ℝ
    have hi : 0 ≤ q_seq i ∧ q_seq i < 1 := by
      have h := (q_bij i).2
      simp [q_seq]; norm_cast
    have hj : 0 ≤ q_seq j ∧ q_seq j < 1 := by
      have h := (q_bij j).2
      simp [q_seq]; norm_cast

    have h_bound : -1 < (k : ℝ) ∧ (k : ℝ) < 1 := by
      -- Use linarith with explicit hypotheses
      rcases hi with ⟨hi_lo, hi_hi⟩
      rcases hj with ⟨hj_lo, hj_hi⟩
      -- Rearrange h_k_eq to k = qi - qj for clarity (optional, linarith should catch it)
      have : (k : ℝ) = q_seq i - q_seq j := by linarith [h_k_eq]
      rw [this]
      constructor <;> linarith

    norm_cast at h_bound
    rcases h_bound with ⟨h_gt, h_lt⟩
    -- Convert integer strict inequalities to non-strict
    change -1 < k at h_gt
    -- Convert strict inequalities to non-strict to help linarith
    -- k < 1 ↔ k ≤ 0
    rw [← zero_add 1, Int.lt_add_one_iff] at h_lt
    -- -1 < k ↔ 0 ≤ k
    rw [← Int.add_one_le_iff] at h_gt
    norm_num at h_gt
    linarith


  -- 6. If k=0, then qj = qi. Since q_bij is injective, j = i.
  rw [h_k_zero] at h_k_eq
  -- Simplify `↑0` to `0` and remove it
  simp only [Int.cast_zero, add_zero, sub_eq_zero] at h_k_eq

  -- Now h_k_eq is `q_seq j = q_seq i`.
  have h_idx : i = j := by
    unfold q_seq at h_k_eq
    -- Remove the coercion from Rat to Real
    norm_cast at h_k_eq
    -- Use injectivity of the sequence bijection
    apply q_bij.injective
    apply Subtype.ext
    exact h_k_eq.symm

  -- Contradiction
  exact hij h_idx

lemma measure_vitali_invariant (m : Set ℝ → ENNReal) (h : IsVitaliMeasure m) (n : ℕ) :
    m (VitaliSeq n) = m VitaliSet := by

  rcases h with ⟨_, _, _, _, h_trans, _⟩
  apply h_trans
  exact vitali_subset_I

lemma sum_vitali_eq_union (m : Set ℝ → ENNReal) (h : IsVitaliMeasure m) :
    (∑' n, m (VitaliSeq n)) = m (⋃ n, VitaliSeq n) := by
  rcases h with ⟨_, _, _, h_add, _, _⟩
  apply (h_add VitaliSeq _ _).symm
  · intro n; exact translate_subset_I _ _
  · exact vitali_seq_disjoint_source_local

lemma measure_singleton_zero (m : Set ℝ → ENNReal) (h : IsVitaliMeasure m)
    (x : ℝ) (hx : x ∈ I) :
  m {x} = 0 := by
  rcases h with ⟨_, _, _, _, _, h_len⟩
  rw [← Set.Icc_self, h_len x x hx.1 le_rfl hx.2]
  simp
end Vitali_set


