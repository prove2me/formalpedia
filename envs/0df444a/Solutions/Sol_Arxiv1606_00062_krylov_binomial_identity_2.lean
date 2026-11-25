-- Prove2me | solution 2 for Arxiv1606_00062.krylov_binomial_identity
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T19:51:21.505955+00:00
-- url     : https://prove2.me/submissions/7ad470d8-c9b5-4ce7-9321-c7c9938ba1d0

import Mathlib
import Definitions.Def_Arxiv1606_00062_Basic

open MeasureTheory Filter Topology
open Arxiv1606_00062

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

lemma binom_apply (A : V →L[ℂ] V) (g : V) (n : ℕ) :
    ((1 - A) ^ n) g = ∑ l ∈ Finset.range (n + 1), ((n.choose l : ℂ) * (-1) ^ l) • (A ^ l) g := by
  have h := (Commute.neg_left (Commute.one_right A)).add_pow n
  rw [show (1 : V →L[ℂ] V) - A = -A + 1 by abel, h]
  simp only [one_pow, mul_one, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [neg_pow]
  rcases Nat.even_or_odd l with h | h
  · simp [h.neg_one_pow, ContinuousLinearMap.mul_apply, ← Nat.cast_smul_eq_nsmul ℂ]
  · simp [h.neg_one_pow, ContinuousLinearMap.mul_apply, ← Nat.cast_smul_eq_nsmul ℂ]

lemma mem_span_of_binom (A : V →L[ℂ] V) (g : V) (m n : ℕ) (hn : n < m) :
    ((1 - A) ^ n) g ∈ Submodule.span ℂ ((fun l : ℕ => (A ^ l) g) '' {l | l < m}) := by
  rw [binom_apply]
  refine Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, ?_, rfl⟩)
  have := Finset.mem_range.mp hl
  show l < m; omega

theorem solution (T : V →L[ℂ] V) (g : V) :
    (∀ n : ℕ, ((1 - T) ^ n) g =
      ∑ l ∈ Finset.range (n + 1), ((n.choose l : ℂ) * (-1) ^ l) • msIter T g l) ∧
    (∀ m : ℕ, krylovSpace T g m = Submodule.span ℂ (msIter T g '' {l | l < m})) := by
  refine ⟨fun n => binom_apply T g n, fun m => ?_⟩
  apply le_antisymm
  · rw [krylovSpace, Submodule.span_le]
    rintro _ ⟨n, hn, rfl⟩
    exact mem_span_of_binom T g m n hn
  · rw [krylovSpace, Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    have := mem_span_of_binom (1 - T) g m l hl
    simpa [msIter] using this

