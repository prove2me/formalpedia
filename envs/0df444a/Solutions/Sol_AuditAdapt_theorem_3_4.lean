-- Prove2me | solution 1 for AuditAdapt.theorem_3_4
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-21T04:03:52.436804+00:00
-- url     : https://prove2.me/submissions/5294418b-2f3d-4957-94bf-427453ec2264

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_AuditAdapt_stateLaw
import Definitions.Def_AuditAdapt_totalCost
import Definitions.Def_AuditAdapt_openLoopMarginal
import Definitions.Def_AuditAdapt_trCov
import Definitions.Def_AuditAdapt_jointMinusProduct
import Theorems.Thm_AuditAdapt_pdl_open_loop_marginal
import Theorems.Thm_AuditAdapt_same_state_marginal

namespace AuditAdapt

open FoundationsRL.RLBasics

private lemma weighted_sum_sub {S A : Type*} [Fintype S] [Fintype A]
    (d : S → ℝ) (z f : S → A → ℝ) (p : A → ℝ) :
    (∑ s : S, d s * ∑ a : A, f s a * (z s a - p a)) =
      (∑ s : S, d s * ∑ a : A, f s a * z s a) -
        ∑ s : S, d s * ∑ a : A, f s a * p a := by
  classical
  simp only [mul_sub, Finset.sum_sub_distrib]

private lemma weighted_sum_swap {S A : Type*} [Fintype S] [Fintype A]
    (d : S → ℝ) (f : S → A → ℝ) (p : A → ℝ) :
    (∑ s : S, d s * ∑ a : A, f s a * p a) =
      ∑ a : A, (∑ s : S, d s * f s a) * p a := by
  classical
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro s _
  ring

private lemma sum_sum_weighted {S A : Type*} [Fintype S] [Fintype A]
    (d : S → ℝ) (z f : S → A → ℝ) :
    (∑ s : S, ∑ a : A, d s * z s a * f s a) =
      ∑ s : S, d s * ∑ a : A, f s a * z s a := by
  classical
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

private lemma trCov_eq_weighted {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    {H : ℕ} (M : EpisodicMDP S A H) (π : Policy S A H) (t : ℕ) (f : S → A → ℝ) :
    trCov M π t f =
      ∑ s : S, stateLaw M π t s *
        ∑ a : A, f s a * (π t s a - marginal M π t a) := by
  classical
  unfold trCov
  rw [weighted_sum_sub, weighted_sum_swap]

private lemma jointMinusProduct_eq_weighted {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq S] {H : ℕ} (M : EpisodicMDP S A H) (π : Policy S A H) (t : ℕ)
    (f : S → A → ℝ) :
    jointMinusProduct M π t f =
      ∑ s : S, stateLaw M π t s *
        ∑ a : A, f s a * (π t s a - marginal M π t a) := by
  classical
  unfold jointMinusProduct
  rw [weighted_sum_sub, sum_sum_weighted, sum_sum_weighted]

private lemma trCov_eq_jointMinusProduct {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq S] {H : ℕ} (M : EpisodicMDP S A H) (π : Policy S A H) (t : ℕ)
    (f : S → A → ℝ) :
    trCov M π t f = jointMinusProduct M π t f := by
  rw [trCov_eq_weighted, jointMinusProduct_eq_weighted]

private lemma jointMinusProduct_sub_state {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq S] {H : ℕ} (M : EpisodicMDP S A H) (π : Policy S A H)
    (hπ : IsPolicy H π) (t : ℕ) (ht : t < H) (f : S → A → ℝ) (g : S → ℝ) :
    jointMinusProduct M π t (fun s a => f s a - g s) =
      jointMinusProduct M π t f := by
  classical
  have hg := same_state_marginal M π hπ t ht g
  unfold jointMinusProduct
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [hg]
  ring

theorem _root_.solution {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] {H : ℕ}
    (M : EpisodicMDP S A H) (π : Policy S A H) (hπ : IsPolicy H π) :
    (totalCost M π - totalCost M (openLoopMarginal M π) =
        ∑ t ∈ Finset.range H, trCov M π t (Q M (openLoopMarginal M π) t)) ∧
    (totalCost M π - totalCost M (openLoopMarginal M π) =
        ∑ t ∈ Finset.range H, jointMinusProduct M π t (Q M (openLoopMarginal M π) t)) ∧
    (∀ g : ℕ → S → ℝ, ∀ t, t < H →
        trCov M π t (fun s a => Q M (openLoopMarginal M π) t s a - g t s) =
            trCov M π t (Q M (openLoopMarginal M π) t) ∧
        jointMinusProduct M π t (fun s a => Q M (openLoopMarginal M π) t s a - g t s) =
            jointMinusProduct M π t (Q M (openLoopMarginal M π) t)) := by
  classical
  constructor
  · rw [pdl_open_loop_marginal M π hπ]
    apply Finset.sum_congr rfl
    intro t _
    exact (trCov_eq_weighted M π t (Q M (openLoopMarginal M π) t)).symm
  constructor
  · rw [pdl_open_loop_marginal M π hπ]
    apply Finset.sum_congr rfl
    intro t _
    exact (jointMinusProduct_eq_weighted M π t (Q M (openLoopMarginal M π) t)).symm
  · intro g t ht
    have hbase :
        jointMinusProduct M π t
            (fun s a => Q M (openLoopMarginal M π) t s a - g t s) =
          jointMinusProduct M π t (Q M (openLoopMarginal M π) t) :=
      jointMinusProduct_sub_state M π hπ t ht
        (Q M (openLoopMarginal M π) t) (g t)
    constructor
    · calc
        trCov M π t (fun s a => Q M (openLoopMarginal M π) t s a - g t s) =
            jointMinusProduct M π t
              (fun s a => Q M (openLoopMarginal M π) t s a - g t s) :=
          trCov_eq_jointMinusProduct M π t
            (fun s a => Q M (openLoopMarginal M π) t s a - g t s)
        _ = jointMinusProduct M π t (Q M (openLoopMarginal M π) t) := hbase
        _ = trCov M π t (Q M (openLoopMarginal M π) t) :=
          (trCov_eq_jointMinusProduct M π t (Q M (openLoopMarginal M π) t)).symm
    · exact hbase

end AuditAdapt
