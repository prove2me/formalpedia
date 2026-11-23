-- Prove2me | Definitions.Def_UniformPrecSched_Makespan_Supplement_IntervalLP
-- name    : UniformPrecSched_Makespan_Supplement_IntervalLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:21:02.940507+00:00
-- url     : https://prove2.me/theorems/404484a9-e7c2-4ce0-81f5-8bc2a5ded2e2
-- title:
--   Interval-indexed relaxation (15)–(22) and its optimality
-- statement:
--   For a normalized instance let $\tau_\ell=2^\ell$ and use levels $\ell=1,\ldots,L$. The first interval includes its lower boundary at time 1. The variables $x_{kj\ell}$ are nonnegative and zero outside this finite horizon. Each job has total mass one. The objective is
--
--   $$\min\sum_j w_j C_j.$$
--
--   The constraints include cumulative class capacity through every level (17), the release difference $C_j-r_j$ (18), and the predecessor difference $C_j-C_{j'}$ for $j'\prec j$ (19). For every prefix the successor's completion mass is at most its predecessor's (20). Finally the weighted average of the left endpoints $\tau_{\ell-1}$ is at most $C_j$ (21). Optimality minimizes the displayed objective over all such feasible variables.
--
--   The horizon is the ceiling of $\log_2(\max_j r_j+\sum_jp_j/s_{\min})$, with at least one interval and empty maxima zero. These are the exact finite relaxation constraints, not independent assumptions that the desired fragment bound already holds.
-- source:
--   Chudak & Shmoys, Approximation algorithms for precedence-constrained scheduling problems on parallel machines that run at different speeds, authors' manuscript (preprint of J. Algorithms, 1999, DOI 10.1006/jagm.1998.0987), pp. 12–13 (PDF 12–13), (15)–(22)

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_Supplement_Weighted
import Definitions.Def_UniformPrecSched_Makespan_LP

namespace UniformPrecSched.Makespan.Supplement

variable {n m : ℕ}

/-- §4, p. 12, PDF 12: τ_l = 2^l. Source interval l=1 is [1,2]. -/
def dyadic (l : ℕ) : ℝ := (2 : ℝ) ^ l

/-- Variables use natural source levels; only 1,...,L can carry mass. -/
abbrev IntervalMass (I : Instance n m) := Fin (numSpeeds I) → Fin n → ℕ → ℝ

/-- Prefix mass of a job, summed over every speed class. -/
noncomputable def prefixMass (I : Instance n m) (x : IntervalMass I) (j : Fin n)
    (l : ℕ) : ℝ := ∑ k, ∑ t ∈ Finset.Icc 1 l, x k j t

/-- Equations (16)–(22), pp. 12–13, PDF 12–13. In (20) a successor's prefix
mass is at most its predecessor's. Outside the finite horizon x is zero. -/
def IntervalFeasible (I : Instance n m) (R : ReleaseWeights n) (L : ℕ)
    (x : IntervalMass I) (C : Fin n → ℝ) : Prop :=
  (∀ k j t, t = 0 ∨ L < t → x k j t = 0) ∧
  (∀ j, prefixMass I x j L = 1) ∧
  (∀ k l, 1 ≤ l → l ≤ L →
    (1 / (classSpeed I k * (classCount I k : ℝ))) *
      (∑ j, ∑ t ∈ Finset.Icc 1 l, I.p j * x k j t) ≤ dyadic l) ∧
  (∀ j, (∑ k, ∑ t ∈ Finset.Icc 1 L, I.p j / classSpeed I k * x k j t) ≤
    C j - R.r j) ∧
  (∀ j' j, I.prec j' j →
    (∑ k, ∑ t ∈ Finset.Icc 1 L, I.p j / classSpeed I k * x k j t) ≤ C j - C j') ∧
  (∀ j' j l, I.prec j' j → 1 ≤ l → l ≤ L →
    prefixMass I x j l ≤ prefixMass I x j' l) ∧
  (∀ j, (∑ t ∈ Finset.Icc 1 L, ∑ k, dyadic (t - 1) * x k j t) ≤ C j) ∧
  (∀ k j t, 0 ≤ x k j t)

/-- Objective (15): minimize Σ_j w_j C_j over the entire interval relaxation. -/
def IntervalOptimal (I : Instance n m) (R : ReleaseWeights n) (L : ℕ)
    (x : IntervalMass I) (C : Fin n → ℝ) : Prop :=
  IntervalFeasible I R L x C ∧ ∀ x' C', IntervalFeasible I R L x' C' →
    ∑ j, R.w j * C j ≤ ∑ j, R.w j * C' j

/-- Integer ceiling of the source horizon max r + Σ p/s_K, with at least one
interval. This is used after normalization. Empty jobs give horizon 1. -/
noncomputable def intervalHorizon (I : Instance n m) (R : ReleaseWeights n) : ℕ :=
  max 1 ⌈Real.logb 2
    (((List.ofFn R.r).foldr max 0) +
      (∑ j, I.p j) / Finset.univ.inf' (machines_nonempty I) I.s)⌉₊

end UniformPrecSched.Makespan.Supplement


