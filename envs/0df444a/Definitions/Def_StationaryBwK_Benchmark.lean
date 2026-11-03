-- Prove2me | Definitions.Def_StationaryBwK_Benchmark
-- name    : StationaryBwK_Benchmark
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:50:31.482205+00:00
-- url     : https://prove2.me/theorems/f041be40-091c-4a6f-a618-2ccf9905156c
-- title:
--   The best-fixed-distribution benchmark $\mathrm{OPT}_{FD}$ (display (1))
-- statement:
--   Fix a horizon of $T$ rounds, $K$ actions $[K]$, $d$ resources $[d]$ and a budget $B$ per resource. Let $r_t(a)$ be a (expected) reward and $c_{t,i}(a)$ an (expected) consumption of resource $i$ by action $a$ in round $t$. For a distribution $p\in\Delta([K])$ of actions write
--   $$\mathbb E_{a\sim p}[f(a)]=\sum_{a\in[K]}p(a)f(a),$$
--   where the expectation is over the action only. The **best fixed distribution in hindsight** is the value of the optimization problem
--   $$\mathrm{OPT}_{FD}=\max_{T^*\in[T],\ A^*\in\Delta([K])}\ \sum_{t=1}^{T^*}\mathbb E_{a\sim A^*}[r_t(a)]\quad\text{such that}\quad\sum_{t=1}^{T^*}\mathbb E_{a\sim A^*}[c_{t,i}(a)]\le B\quad\forall i\in[d].$$
--   A pair $(T^*,A^*)$ is an **optimal solution** if it is feasible and its value is at least that of every feasible pair. The definition also introduces the distribution that plays $p$ with probability $q$ and a designated null action $a_0$ otherwise, $q\,p+(1-q)\,\delta_{a_0}$.
--
--   This is the benchmark against which the reward of Algorithm 1 is measured in Theorem 5.2. In the paper $r$ and $c$ are the conditional expectations of one realized history, so $\mathrm{OPT}_{FD}$ is a random variable.
--
--   **Formalization Note** Rounds are the natural numbers $1,\dots,T$, distributions are points of `stdSimplex ℝ (Fin K)`, and $\mathrm{OPT}_{FD}$ is the supremum of the set of feasible values. That set is bounded above, and nonempty as soon as the null action consumes nothing and $B\ge0$; it then has a maximum.
-- source:
--   G. Fikioris and É. Tardos, Approximately Stationary Bandits with Knapsacks, arXiv:2302.14686v2 [cs.LG] (preprint, 8 Jul 2023), https://arxiv.org/abs/2302.14686v2, §4, display (1), p.7; proof of Theorem 5.2, p.18 (mixture with the null arm)

import Mathlib

namespace StationaryBwK

/-! # The best-fixed-distribution benchmark `OPT_FD`

Fikioris & Tardos, *Approximately Stationary Bandits with Knapsacks*, arXiv:2302.14686v2,
§4, display (1), p.7.

**Formalization Note.** Actions are `Fin K`, resources `Fin d`, rounds `t = 1, …, T` are natural
numbers (round `0` is unused), and a distribution of actions is a point of `stdSimplex ℝ (Fin K)`.
The benchmark is stated for deterministic sequences `r t a` and `c t i a`; the paper applies it to
the conditional expectations of one realized history (see `optFDRand`). -/

/-- `E_{a∼p}[f(a)] = Σ_a p(a) f(a)` (p.7): the expectation is over the action only. -/
def expect {K : ℕ} (p : Fin K → ℝ) (f : Fin K → ℝ) : ℝ :=
  ∑ a, p a * f a

/-- The objective of (1), p.7: `Σ_{t=1}^{T*} E_{a∼p}[r_t(a)]`. -/
def fdValue {K : ℕ} (r : ℕ → Fin K → ℝ) (Ts : ℕ) (p : Fin K → ℝ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 Ts, expect p (r t)

/-- The budget constraint of (1), p.7: `Σ_{t=1}^{T*} E_{a∼p}[c_{t,i}(a)] ≤ B` for all `i ∈ [d]`. -/
def FDFeasible {d K : ℕ} (B : ℝ) (c : ℕ → Fin d → Fin K → ℝ) (Ts : ℕ) (p : Fin K → ℝ) : Prop :=
  ∀ i : Fin d, ∑ t ∈ Finset.Icc 1 Ts, expect p (fun a => c t i a) ≤ B

/-- The values of the feasible points `(T*, A*) ∈ [T] × Δ([K])` of (1), p.7. -/
def fdValues {d K : ℕ} (T : ℕ) (B : ℝ) (r : ℕ → Fin K → ℝ) (c : ℕ → Fin d → Fin K → ℝ) :
    Set ℝ :=
  {v | ∃ Ts ∈ Finset.Icc 1 T, ∃ p ∈ stdSimplex ℝ (Fin K), FDFeasible B c Ts p ∧ v = fdValue r Ts p}

/-- `OPT_FD`, display (1), p.7: the supremum of `Σ_{t=1}^{T*} E_{a∼A*}[r_t(a)]` over `T* ∈ [T]` and
`A* ∈ Δ([K])` subject to `Σ_{t=1}^{T*} E_{a∼A*}[c_{t,i}(a)] ≤ B` for every resource `i`.

**Formalization Note.** The value set is always bounded above (finitely many `T*`, `p` in the
simplex). It is nonempty whenever the null action is available and `B ≥ 0`, which holds in every
statement of this mission; there the supremum is a maximum (`StationaryBwK.optFD_attained`). -/
noncomputable def optFD {d K : ℕ} (T : ℕ) (B : ℝ) (r : ℕ → Fin K → ℝ)
    (c : ℕ → Fin d → Fin K → ℝ) : ℝ :=
  sSup (fdValues T B r c)

/-- `(T*, A*)` is an optimal solution of (1), p.7: it is feasible, and its value is at least the
value of every feasible point. -/
def IsOptFDSolution {d K : ℕ} (T : ℕ) (B : ℝ) (r : ℕ → Fin K → ℝ) (c : ℕ → Fin d → Fin K → ℝ)
    (Ts : ℕ) (p : Fin K → ℝ) : Prop :=
  Ts ∈ Finset.Icc 1 T ∧ p ∈ stdSimplex ℝ (Fin K) ∧ FDFeasible B c Ts p ∧
    ∀ Ts' ∈ Finset.Icc 1 T, ∀ p' ∈ stdSimplex ℝ (Fin K), FDFeasible B c Ts' p' →
      fdValue r Ts' p' ≤ fdValue r Ts p

/-- The distribution that plays `p` with probability `q` and the null action `a₀` otherwise
(proof of Theorem 5.2, p.18). -/
def mixNull {K : ℕ} (q : ℝ) (p : Fin K → ℝ) (a₀ : Fin K) : Fin K → ℝ :=
  fun a => q * p a + if a = a₀ then 1 - q else 0

end StationaryBwK


