-- Prove2me | solution 1 for Arxiv1606_00062.krylov_binomial_identity
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T19:50:25.5058+00:00
-- url     : https://prove2.me/submissions/89cd5d97-9bd0-480a-9cb2-54113699c6a3

import Mathlib
import Definitions.Def_Arxiv1606_00062_Basic

open Filter Topology Set

namespace S69K

lemma binom {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (T : V →L[ℂ] V) (g : V) (n : ℕ) :
    ((1 - T) ^ n) g = ∑ l ∈ Finset.range (n + 1), ((n.choose l : ℂ) * (-1) ^ l) • (T ^ l) g := by
  rw [sub_eq_neg_add, (Commute.one_right (-T)).add_pow, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [one_pow, mul_one, ContinuousLinearMap.mul_apply, ContinuousLinearMap.natCast_apply, map_nsmul,
    ← Nat.cast_smul_eq_nsmul ℂ]
  rcases Nat.even_or_odd l with h | h
  · simp [h.neg_one_pow, h.neg_pow]
  · simp [h.neg_one_pow, h.neg_pow, smul_smul]

end S69K

open Arxiv1606_00062 in
theorem solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] (T : V →L[ℂ] V) (g : V) :
    (∀ n : ℕ, ((1 - T) ^ n) g =
      ∑ l ∈ Finset.range (n + 1), ((n.choose l : ℂ) * (-1) ^ l) • msIter T g l) ∧
    (∀ m : ℕ, krylovSpace T g m = Submodule.span ℂ (msIter T g '' {l | l < m})) := by
  refine ⟨fun n => S69K.binom T g n, fun m => ?_⟩
  unfold krylovSpace
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨n, hn, rfl⟩
    simp only
    rw [S69K.binom]
    refine Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine ⟨l, ?_, rfl⟩
    have := Finset.mem_range.mp hl
    show l < m
    have : n < m := hn
    omega
  · rw [Submodule.span_le]
    rintro _ ⟨n, hn, rfl⟩
    have h := S69K.binom (1 - T) g n
    rw [sub_sub_cancel] at h
    simp only [msIter, SetLike.mem_coe]
    rw [h]
    refine Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine ⟨l, ?_, rfl⟩
    have := Finset.mem_range.mp hl
    show l < m
    have : n < m := hn
    omega
