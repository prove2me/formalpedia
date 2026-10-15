-- Prove2me | Definitions.Def_BreakingSample_FiniteHorizon_Sampling
-- name    : BreakingSample_FiniteHorizon_Sampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:57.456483+00:00
-- url     : https://prove2.me/theorems/9c754b8f-6619-4a64-a895-3b3d90f9e80e
-- title:
--   §2.2, (6), p. 7 — generative-model data set for a finite-horizon MDP, the empirical kernels P̂_h and the probability of an event of the data
-- statement:
--   This module fixes the generative model of §2.2 for a finite-horizon MDP with kernels $P_1,\dots,P_H$ on a finite state space $\mathcal S$ and finite action space $\mathcal A$.
--
--   1. **Data.** For every triple $(s,a,h)\in\mathcal S\times\mathcal A\times[H]$ there are $N$ next states $s^i_h(s,a)$, $i=1,\dots,N$.
--   2. **Empirical kernels** (6):
--   $$\widehat P_h(s'\mid s,a)=\frac1N\sum_{i=1}^N\mathbb 1\{s^i_h(s,a)=s'\}.$$
--   3. **Law of the data.** All samples are independent and $s^i_h(s,a)\sim P_h(\cdot\mid s,a)$, so a data set $x$ has probability $\prod_h\prod_s\prod_a\prod_i P_h\big(x^i_h(s,a)\mid s,a\big)$.
--   4. **Probability of an event.** For an event $E$ of the data, $\mathbb P(E)$ is the sum of these weights over the data sets in $E$.
--
--   The empirical MDP $\widehat{\mathcal M}$ of §2.2 is $(\{\widehat P_h\},\{r_h\})$; every probability statement of Theorem 4 and its proof is about this law.
--
--   **Formalization Note** The data set is an element of the finite type of functions $[H]\times\mathcal S\times\mathcal A\times[N]\to\mathcal S$, so the probability is a finite sum and needs no measure theory. When every $P_h$ is a transition kernel the weights sum to $1$. For $N=0$ the empirical kernel is $0$ (Lean's division by zero); every theorem using it assumes $N>0$.
-- source:
--   arXiv:2005.12900v8, §2.2, (6), p. 7

import Mathlib

namespace BreakingSample.FiniteHorizon

/-- A data set of the generative model of §2.2 (arXiv:2005.12900v8, p. 7): for each triple `(s,a,h)`,
`N` next states `s^i_h(s,a)`, `i = 1, …, N` (here `x h s a i`, with `h : Fin H` and `i : Fin N`). -/
abbrev Samples (S A : Type*) (H N : ℕ) : Type _ := Fin H → S → A → Fin N → S

/-- The empirical kernel (6), p. 7: `P̂_h(s'|s,a) = (1/N) ∑ᵢ 1{s^i_h(s,a) = s'}`. -/
noncomputable def empKernel {S A : Type*} [DecidableEq S] {H N : ℕ} (x : Samples S A H N)
    (h : Fin H) (s : S) (a : A) (s' : S) : ℝ :=
  ((Finset.univ.filter (fun i => x h s a i = s')).card : ℝ) / N

/-- The probability of the data set `x` when all samples are independent and `s^i_h(s,a) ∼ P_h(·|s,a)`. -/
noncomputable def sampleWeight {S A : Type*} [Fintype S] [Fintype A] {H N : ℕ}
    (P : Fin H → S → A → S → ℝ) (x : Samples S A H N) : ℝ :=
  ∏ h, ∏ s, ∏ a, ∏ i, P h s a (x h s a i)

/-- The probability `ℙ(E)` of an event `E` of the data set. -/
noncomputable def sampleProb {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] {H : ℕ}
    (P : Fin H → S → A → S → ℝ) (N : ℕ) (E : Samples S A H N → Prop) : ℝ := by
  classical exact ∑ x : Samples S A H N, if E x then sampleWeight P x else 0

end BreakingSample.FiniteHorizon


