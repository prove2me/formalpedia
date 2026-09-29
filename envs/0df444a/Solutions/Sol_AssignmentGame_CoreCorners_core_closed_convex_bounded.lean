-- Prove2me | solution 1 for AssignmentGame.CoreCorners.core_closed_convex_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T02:02:06.695987+00:00
-- url     : https://prove2.me/submissions/81181460-0bf8-4232-b743-d682a192b2b4

import Mathlib
import Definitions.Def_AssignmentGame_CoreCorners_Game

open AssignmentGame.CoreCorners
open Finset

theorem solution {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ)
    (ha : ∀ i j, 0 ≤ a i j) :
    IsClosed (core a) ∧ Convex ℝ (core a) ∧ Bornology.IsBounded (core a) := by
  classical
  have hcont : ∀ (A : Finset M) (B : Finset N),
      Continuous fun p : (M → ℝ) × (N → ℝ) => ∑ i ∈ A, p.1 i + ∑ j ∈ B, p.2 j := by
    intro A B
    refine Continuous.add ?_ ?_
    · exact continuous_finset_sum A fun i _ => (continuous_apply i).comp continuous_fst
    · exact continuous_finset_sum B fun j _ => (continuous_apply j).comp continuous_snd
  have hworth_nonneg : ∀ (A : Finset M) (B : Finset N), 0 ≤ worth a A B := by
    intro A B
    have h := Finset.le_sup' (f := fun P : Finset (M × N) => ∑ p ∈ P, a p.1 p.2)
      (empty_mem_matchings A B)
    simpa [worth] using h
  refine ⟨?_, ?_, ?_⟩
  · have heq : core a = {p : (M → ℝ) × (N → ℝ) |
        ∑ i, p.1 i + ∑ j, p.2 j = worth a univ univ}
        ∩ ⋂ (A : Finset M), ⋂ (B : Finset N),
          {p : (M → ℝ) × (N → ℝ) | worth a A B ≤ ∑ i ∈ A, p.1 i + ∑ j ∈ B, p.2 j} := by
      ext p
      simp only [core, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [heq]
    exact (isClosed_eq (hcont univ univ) continuous_const).inter
      (isClosed_iInter fun A => isClosed_iInter fun B =>
        isClosed_le continuous_const (hcont A B))
  · rintro p ⟨hp1, hp2⟩ q ⟨hq1, hq2⟩ s t hs ht hst
    refine ⟨?_, ?_⟩
    · have hx : ∑ i, (s • p + t • q).1 i + ∑ j, (s • p + t • q).2 j
          = s * (∑ i, p.1 i + ∑ j, p.2 j) + t * (∑ i, q.1 i + ∑ j, q.2 j) := by
        simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
      rw [hx, hp1, hq1, ← add_mul, hst, one_mul]
    · intro A B
      have hx : ∑ i ∈ A, (s • p + t • q).1 i + ∑ j ∈ B, (s • p + t • q).2 j
          = s * (∑ i ∈ A, p.1 i + ∑ j ∈ B, p.2 j)
            + t * (∑ i ∈ A, q.1 i + ∑ j ∈ B, q.2 j) := by
        simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
      rw [hx]
      have h1 := hp2 A B
      have h2 := hq2 A B
      have h3 : worth a A B = s * worth a A B + t * worth a A B := by
        rw [← add_mul, hst, one_mul]
      rw [h3]
      exact add_le_add (mul_le_mul_of_nonneg_left h1 hs) (mul_le_mul_of_nonneg_left h2 ht)
  · rw [isBounded_iff_forall_norm_le]
    refine ⟨worth a univ univ, ?_⟩
    rintro p ⟨hp1, hp2⟩
    have hu : ∀ i : M, 0 ≤ p.1 i := by
      intro i
      have h := hp2 {i} ∅
      simp only [Finset.sum_singleton, Finset.sum_empty, add_zero] at h
      exact le_trans (hworth_nonneg {i} ∅) h
    have hv : ∀ j : N, 0 ≤ p.2 j := by
      intro j
      have h := hp2 ∅ {j}
      simp only [Finset.sum_singleton, Finset.sum_empty, zero_add] at h
      exact le_trans (hworth_nonneg ∅ {j}) h
    have hsum1 : ∑ i, p.1 i ≤ worth a univ univ := by
      have : (0 : ℝ) ≤ ∑ j, p.2 j := Finset.sum_nonneg fun j _ => hv j
      linarith
    have hsum2 : ∑ j, p.2 j ≤ worth a univ univ := by
      have : (0 : ℝ) ≤ ∑ i, p.1 i := Finset.sum_nonneg fun i _ => hu i
      linarith
    have hW : 0 ≤ worth a univ univ := hworth_nonneg univ univ
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · rw [pi_norm_le_iff_of_nonneg hW]
      intro i
      rw [Real.norm_eq_abs, abs_of_nonneg (hu i)]
      exact le_trans (Finset.single_le_sum (fun k _ => hu k) (Finset.mem_univ i)) hsum1
    · rw [pi_norm_le_iff_of_nonneg hW]
      intro j
      rw [Real.norm_eq_abs, abs_of_nonneg (hv j)]
      exact le_trans (Finset.single_le_sum (fun k _ => hv k) (Finset.mem_univ j)) hsum2
