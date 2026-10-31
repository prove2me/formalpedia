-- Prove2me | Definitions.Def_StochasticRewardMatching_Decomposable_Instance
-- name    : StochasticRewardMatching_Decomposable_Instance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T21:13:24.879333+00:00
-- url     : https://prove2.me/theorems/b97813b9-f77e-4dfa-a185-c6aecd556920
-- title:
--   Finite vertex-weighted stochastic matching instances
-- statement:
--   A finite bipartite instance has resources indexed by Fin n, ordered arrivals indexed by Fin m, a set of present edges, nonnegative real resource rewards, and probabilities in [0,1] on present edges. No bound is imposed on n, m or rewards; either side may be empty. An absent edge is unavailable. Edge D is precisely the subtype of present edges. An outcome assigns a Boolean success bit to each present edge. Decomposability means that nonnegative endpoint factors multiply to each present edge probability; factors themselves need not be at most one. Values assigned to the probability function away from present edges are unused.
-- source:
--   Goyal and Udwani, Online Matching with Stochastic Rewards: Optimal Competitive Ratio via Path Based Formulation, supplied PDF marked arXiv:1905.12778v6 (10 May 2022), §§1–2, PDF/printed pp. 2–5, 8–9; metadata citation_basis: published. https://arxiv.org/abs/1905.12778v6

import Mathlib

open scoped BigOperators
open MeasureTheory
noncomputable section

namespace StochasticRewardMatching.Decomposable

structure Instance (n m : ℕ) where
  edges : Finset (Fin n × Fin m)
  reward : Fin n → ℝ
  probability : Fin n × Fin m → ℝ
  reward_nonneg : ∀ i, 0 ≤ reward i
  probability_mem : ∀ e ∈ edges, probability e ∈ Set.Icc (0 : ℝ) 1

abbrev Edge {n m : ℕ} (D : Instance n m) := {e // e ∈ D.edges}

abbrev Outcome {n m : ℕ} (D : Instance n m) := Edge D → Bool

def decomposable {n m : ℕ} (D : Instance n m) : Prop :=
  ∃ (a : Fin n → ℝ) (b : Fin m → ℝ),
    (∀ i, 0 ≤ a i) ∧ (∀ t, 0 ≤ b t) ∧
    ∀ e ∈ D.edges, D.probability e = a e.1 * b e.2

end StochasticRewardMatching.Decomposable


