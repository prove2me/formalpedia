-- Prove2me | Definitions.Def_HiringLP_ProbeTopK_WeightedRank
-- name    : HiringLP_ProbeTopK_WeightedRank
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:37.963879+00:00
-- url     : https://prove2.me/theorems/3f93aec4-4d4a-46fb-80af-367359dce160
-- title:
--   App. A.1, p. ec1 — weighted rank function of the k-uniform matroid, independent rounding, marginals
-- statement:
--   Let $n \ge 0$, let $w = (w_i)_{i \in [n]}$ be real weights and $k \in \mathbb{N}$. The **weighted rank function of the $k$-uniform matroid** with weights $w$ assigns to every $D \subseteq [n]$ the largest total weight of at most $k$ of its elements,
--
--   $$
--   w^*(D) = \max_{R \subseteq D,\ |R| \le k} \sum_{i \in R} w_i .
--   $$
--
--   The maximum is over a nonempty finite family, since $R = \emptyset$ is always admissible.
--
--   Two companion objects describe random subsets of $[n]$. For a vector $y \in \mathbb{R}^n$, the **independent rounding** of $y$ is the law under which each $i$ belongs to the random set independently with probability $y_i$; the probability of the outcome $S$ is
--
--   $$
--   \Pr[\text{set} = S] = \prod_{i \in S} y_i \prod_{i \notin S} (1-y_i).
--   $$
--
--   For a distribution $\mu$ on subsets of $[n]$, given by its weights $\mu(S)$, the **marginals** are $q_i = \Pr_{D \sim \mu}(i \in D) = \sum_{S \ni i} \mu(S)$.
--
--   These three objects are what the correlation gap of a set function compares: the expectation of $w^*$ under $\mu$ against its expectation under the independent rounding of $\mu$'s marginals.
--
--   **Formalization Note.** The ground set is `Fin n`, subsets are `Finset (Fin n)`, and the maximum is `Finset.sup'` over the powerset filtered to cardinality at most $k$. The independent-rounding weights are defined for every real vector; they form a probability distribution when $0 \le y_i \le 1$.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, pp. ec1–ec2 (PDF pp. 33–34), App. A.1

import Mathlib

namespace HiringLP.ProbeTopK

open Finset

/-- App. A.1, p. ec1: the weighted rank function of the `k`-uniform matroid on `Fin n` with weights `w`,
`w*(D) = max_{R ⊆ D, |R| ≤ k} Σ_{i ∈ R} w i`. The empty set is always a candidate, so the maximum is over
a nonempty finite family. -/
noncomputable def wrank {n : ℕ} (w : Fin n → ℝ) (k : ℕ) (D : Finset (Fin n)) : ℝ :=
  (D.powerset.filter (fun R => R.card ≤ k)).sup' ⟨∅, by simp⟩ (fun R => ∑ i ∈ R, w i)

/-- Probability that a random subset of `Fin n` equals `S` when each `i` is included independently with
probability `y i` (independent rounding of `y`). -/
def indepProb {n : ℕ} (y : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∏ i, if i ∈ S then y i else 1 - y i

/-- Marginals `q_i = P(i ∈ D)` of a distribution `μ` (given by its weights) on subsets of `Fin n`. -/
def marg {n : ℕ} (μ : Finset (Fin n) → ℝ) (i : Fin n) : ℝ :=
  ∑ S, μ S * if i ∈ S then 1 else 0

end HiringLP.ProbeTopK


