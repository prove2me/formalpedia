-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_3_F001
-- name    : ProbabilityTheory_chapter_01_thm_1_3_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T18:45:50.845226+00:00
-- url     : https://prove2.me/theorems/49ddef52-6e0e-45f6-953b-68c0536037d9
-- title:
--   Chapter 1, thm_1_3: supporting Lean bundle F001
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_3`: `rsIntegralWitness_integrator_add`, `rsIntegrable_integrator_add`, `rsIntegral_integrator_add`, `thm_1_3`, `sourceHypotheses_integrator_const_mul`, and 8 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_3.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_3_F000
import Mathlib.Tactic

open scoped BigOperators Pointwise
open Finset
open Set

noncomputable section

section Thm_1_3_helper

end Thm_1_3_helper

section Theorem_1_3

private theorem taggedCommonLimit_integrator_add_source_local {a b : ℝ} {f α₁ α₂ : ℝ → ℝ}
    {L₁ L₂ : ℝ}
    (h₁ : TaggedCommonLimit a b f α₁ L₁)
    (h₂ : TaggedCommonLimit a b f α₂ L₂) :
    TaggedCommonLimit a b f (fun x => α₁ x + α₂ x) (L₁ + L₂) := by
  rcases h₁ with ⟨hs₁, hlim₁⟩
  rcases h₂ with ⟨hs₂, hlim₂⟩
  refine ⟨sourceHypotheses_integrator_add hs₁ hs₂, ?_⟩
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlim₁ (eps / 2) hhalf with ⟨δ₁, hδ₁, H₁⟩
  rcases hlim₂ (eps / 2) hhalf with ⟨δ₂, hδ₂, H₂⟩
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro P tags htags hmesh
  have hmesh₁ : P.mesh < δ₁ := lt_of_lt_of_le hmesh (min_le_left δ₁ δ₂)
  have hmesh₂ : P.mesh < δ₂ := lt_of_lt_of_le hmesh (min_le_right δ₁ δ₂)
  have hP₁ := H₁ P tags htags hmesh₁
  have hP₂ := H₂ P tags htags hmesh₂
  have hadd :
      taggedSum P tags f (fun x => α₁ x + α₂ x) - (L₁ + L₂) =
        (taggedSum P tags f α₁ - L₁) + (taggedSum P tags f α₂ - L₂) := by
    rw [taggedSum_integrator_add]
    ring
  calc
    |taggedSum P tags f (fun x => α₁ x + α₂ x) - (L₁ + L₂)| =
        |(taggedSum P tags f α₁ - L₁) + (taggedSum P tags f α₂ - L₂)| := by
      rw [hadd]
    _ ≤ |taggedSum P tags f α₁ - L₁| + |taggedSum P tags f α₂ - L₂| :=
      abs_add_le _ _
    _ < eps := by
      have hlt :
          |taggedSum P tags f α₁ - L₁| + |taggedSum P tags f α₂ - L₂| <
            eps / 2 + eps / 2 := add_lt_add hP₁ hP₂
      simpa using hlt

private theorem upperLowerCommonLimit_integrator_add_source_local {a b : ℝ} {f α₁ α₂ : ℝ → ℝ}
    {L₁ L₂ : ℝ}
    (h₁ : UpperLowerCommonLimit a b f α₁ L₁)
    (h₂ : UpperLowerCommonLimit a b f α₂ L₂) :
    UpperLowerCommonLimit a b f (fun x => α₁ x + α₂ x) (L₁ + L₂) := by
  rcases h₁ with ⟨hs₁, hlim₁⟩
  rcases h₂ with ⟨hs₂, hlim₂⟩
  refine ⟨sourceHypotheses_integrator_add hs₁ hs₂, ?_⟩
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlim₁ (eps / 2) hhalf with ⟨δ₁, hδ₁, H₁⟩
  rcases hlim₂ (eps / 2) hhalf with ⟨δ₂, hδ₂, H₂⟩
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro P hmesh
  have hmesh₁ : P.mesh < δ₁ := lt_of_lt_of_le hmesh (min_le_left δ₁ δ₂)
  have hmesh₂ : P.mesh < δ₂ := lt_of_lt_of_le hmesh (min_le_right δ₁ δ₂)
  have hP₁ := H₁ P hmesh₁
  have hP₂ := H₂ P hmesh₂
  constructor
  · have hadd :
        upperSum P f (fun x => α₁ x + α₂ x) - (L₁ + L₂) =
          (upperSum P f α₁ - L₁) + (upperSum P f α₂ - L₂) := by
      rw [upperSum_integrator_add]
      ring
    calc
      |upperSum P f (fun x => α₁ x + α₂ x) - (L₁ + L₂)| =
          |(upperSum P f α₁ - L₁) + (upperSum P f α₂ - L₂)| := by rw [hadd]
      _ ≤ |upperSum P f α₁ - L₁| + |upperSum P f α₂ - L₂| := abs_add_le _ _
      _ < eps := by
        have hlt :
            |upperSum P f α₁ - L₁| + |upperSum P f α₂ - L₂| <
              eps / 2 + eps / 2 := add_lt_add hP₁.1 hP₂.1
        simpa using hlt
  · have hadd :
        lowerSum P f (fun x => α₁ x + α₂ x) - (L₁ + L₂) =
          (lowerSum P f α₁ - L₁) + (lowerSum P f α₂ - L₂) := by
      rw [lowerSum_integrator_add]
      ring
    calc
      |lowerSum P f (fun x => α₁ x + α₂ x) - (L₁ + L₂)| =
          |(lowerSum P f α₁ - L₁) + (lowerSum P f α₂ - L₂)| := by rw [hadd]
      _ ≤ |lowerSum P f α₁ - L₁| + |lowerSum P f α₂ - L₂| := abs_add_le _ _
      _ < eps := by
        have hlt :
            |lowerSum P f α₁ - L₁| + |lowerSum P f α₂ - L₂| <
              eps / 2 + eps / 2 := add_lt_add hP₁.2 hP₂.2
        simpa using hlt

noncomputable def rsIntegralWitness_integrator_add {f α₁ α₂ : ℝ → ℝ} {a b : ℝ}
    (h₁ : RSIntegrable f α₁ a b)
    (h₂ : RSIntegrable f α₂ a b) :
    RSIntegralWitness f (fun x => α₁ x + α₂ x) a b where
  value := rsIntegral f α₁ a b h₁ + rsIntegral f α₂ a b h₂
  source_limit :=
    upperLowerCommonLimit_integrator_add_source_local
      (rsIntegral_source_spec h₁) (rsIntegral_source_spec h₂)
  tagged_limit :=
    taggedCommonLimit_integrator_add_source_local
      (rsIntegral_spec h₁) (rsIntegral_spec h₂)

noncomputable def rsIntegrable_integrator_add {f α₁ α₂ : ℝ → ℝ} {a b : ℝ}
    (h₁ : RSIntegrable f α₁ a b)
    (h₂ : RSIntegrable f α₂ a b) :
    RSIntegrable f (fun x => α₁ x + α₂ x) a b :=
  ⟨rsIntegralWitness_integrator_add h₁ h₂⟩






end Theorem_1_3

section integrator_scalar_multiply

lemma sourceHypotheses_integrator_const_mul {a b : ℝ} {f α : ℝ → ℝ} {k : ℝ}
    (hk : 0 ≤ k) (h : SourceHypotheses a b f α) :
    SourceHypotheses a b f (fun x => k * α x) := by
  rcases h with ⟨hab, hAbove, hBelow, hmono⟩
  refine ⟨hab, hAbove, hBelow, ?_⟩
  intro x hx y hy hxy

  exact mul_le_mul_of_nonneg_left (hmono hx hy hxy) hk
lemma upperSum_integrator_const_mul {a b : ℝ} (P : Partition a b)
    (f α : ℝ → ℝ) (k : ℝ) :
    upperSum P f (fun x => k * α x) = k * upperSum P f α := by
  unfold upperSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring
lemma lowerSum_integrator_const_mul {a b : ℝ} (P : Partition a b)
    (f α : ℝ → ℝ) (k : ℝ) :
    lowerSum P f (fun x => k * α x) = k * lowerSum P f α := by
  unfold lowerSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring
lemma taggedSum_integrator_const_mul {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    (f α : ℝ → ℝ) (k : ℝ) :
    taggedSum P tags f (fun x => k * α x) = k * taggedSum P tags f α := by
  unfold taggedSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring
theorem upperLowerCommonLimit_integrator_const_mul {a b k : ℝ} {f α : ℝ → ℝ}
    {L : ℝ} (hk : 0 ≤ k)
    (h : UpperLowerCommonLimit a b f α L) :
    UpperLowerCommonLimit a b f (fun x => k * α x) (k * L) := by
  rcases h with ⟨hs, hlim⟩
  refine ⟨sourceHypotheses_integrator_const_mul hk hs, ?_⟩
  intro eps heps
  let C : ℝ := |k| + 1
  have hCpos : 0 < C := by
    dsimp [C]
    linarith [abs_nonneg k]
  have hscale : 0 < eps / C := div_pos heps hCpos
  rcases hlim (eps / C) hscale with ⟨δ, hδ, H⟩
  refine ⟨δ, hδ, ?_⟩
  intro P hmesh
  have hP := H P hmesh
  constructor
  · have hEq : upperSum P f (fun x => k * α x) - k * L = k * (upperSum P f α - L) := by
      rw [upperSum_integrator_const_mul P f α k]
      ring
    rw [hEq, abs_mul]
    have hmul₁ : |k| * |upperSum P f α - L| ≤ |k| * (eps / C) :=
      mul_le_mul_of_nonneg_left (le_of_lt hP.1) (abs_nonneg k)
    have hmul₂ : |k| * (eps / C) < C * (eps / C) := mul_lt_mul_of_pos_right (lt_add_one |k|) hscale
    have hCmul : C * (eps / C) = eps := by field_simp [ne_of_gt hCpos]
    exact lt_of_le_of_lt hmul₁ (by simpa [hCmul] using hmul₂)
  · have hEq : lowerSum P f (fun x => k * α x) - k * L = k * (lowerSum P f α - L) := by
      rw [lowerSum_integrator_const_mul P f α k]
      ring
    rw [hEq, abs_mul]
    have hmul₁ : |k| * |lowerSum P f α - L| ≤ |k| * (eps / C) :=
      mul_le_mul_of_nonneg_left (le_of_lt hP.2) (abs_nonneg k)
    have hmul₂ : |k| * (eps / C) < C * (eps / C) := mul_lt_mul_of_pos_right (lt_add_one |k|) hscale
    have hCmul : C * (eps / C) = eps := by field_simp [ne_of_gt hCpos]
    exact lt_of_le_of_lt hmul₁ (by simpa [hCmul] using hmul₂)
theorem taggedCommonLimit_integrator_const_mul {a b k : ℝ} {f α : ℝ → ℝ}
    {L : ℝ} (hk : 0 ≤ k)
    (h : TaggedCommonLimit a b f α L) :
    TaggedCommonLimit a b f (fun x => k * α x) (k * L) := by
  rcases h with ⟨hs, hlim⟩
  refine ⟨sourceHypotheses_integrator_const_mul hk hs, ?_⟩
  intro eps heps
  let C : ℝ := |k| + 1
  have hCpos : 0 < C := by
    dsimp [C]
    linarith [abs_nonneg k]
  have hscale : 0 < eps / C := div_pos heps hCpos
  rcases hlim (eps / C) hscale with ⟨δ, hδ, H⟩
  refine ⟨δ, hδ, ?_⟩
  intro P tags htags hmesh
  have hP := H P tags htags hmesh
  have hEq : taggedSum P tags f (fun x => k * α x) - k * L = k * (taggedSum P tags f α - L) := by
    rw [taggedSum_integrator_const_mul P tags f α k]
    ring
  rw [hEq, abs_mul]
  have hmul₁ : |k| * |taggedSum P tags f α - L| ≤ |k| * (eps / C) :=
    mul_le_mul_of_nonneg_left (le_of_lt hP) (abs_nonneg k)
  have hmul₂ : |k| * (eps / C) < C * (eps / C) := mul_lt_mul_of_pos_right (lt_add_one |k|) hscale
  have hCmul : C * (eps / C) = eps := by field_simp [ne_of_gt hCpos]
  exact lt_of_le_of_lt hmul₁ (by simpa [hCmul] using hmul₂)

noncomputable def rsIntegralWitness_integrator_const_mul {f α : ℝ → ℝ} {a b k : ℝ}
    (hk : 0 ≤ k) (h : RSIntegrable f α a b) :
    RSIntegralWitness f (fun x => k * α x) a b where
  value := k * rsIntegral f α a b h
  source_limit := upperLowerCommonLimit_integrator_const_mul hk (rsIntegral_source_spec h)
  tagged_limit := taggedCommonLimit_integrator_const_mul hk (rsIntegral_spec h)






end integrator_scalar_multiply


