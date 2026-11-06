-- Prove2me | Definitions.Def_SKWeakPoincare_alg1Law
-- name    : SKWeakPoincare_alg1Law
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:35.080835+00:00
-- url     : https://prove2.me/theorems/a02d01f0-4bb6-4a6a-99a5-aec41425600b
-- title:
--   Algorithm 1: output law of simulated annealing with schedule $\beta_j=j\beta/\lceil\beta n\rceil$
-- statement:
--   Let $A$ be a zero-diagonal symmetric $n\times n$ matrix, $0\le\beta<1$ and $p\in\mathbb N$. **Algorithm 1** sets $L=\lceil\beta n\rceil$ and $\beta_j=j\beta/L$ for $0\le j\le L$, draws $x\in\{\pm1\}^n$ uniformly, and for $j=1,\dots,L$ performs $\lceil n^p\rceil$ heat-bath updates: choose $i\in[n]$ uniformly, set $h_i=\beta_j\sum_{\ell\ne i}A_{i\ell}x_\ell$, and replace $x_i$ by $+1$ with probability $(1+e^{-2h_i})^{-1}$ and by $-1$ otherwise. It returns $x$.
--
--   This module defines $L$ (`alg1Stages`), the schedule $\beta_j$ (`alg1Temp`) and the exact law of the returned configuration (`alg1Law`): the uniform law multiplied by $P_{\beta_1}^{n^p}\cdots P_{\beta_L}^{n^p}$, where $P_{\beta'}$ is the random-scan heat-bath Glauber kernel of the SK Gibbs measure $\mu_{\beta',A}$.
--
--   This is the sampler of the paper's main sampling theorem (Theorem 1.2).
--
--   **Formalization Note** The matrix is a disorder $W$ on the edges $i<j$ (`OAI.CriticalSK.Disorder`), and one heat-bath update is one step of `OAI.CriticalSK.discreteKernel (β_j • W)`, whose site update sets $x_i=+1$ with probability $e^{h_i}/(e^{h_i}+e^{-h_i})=(1+e^{-2h_i})^{-1}$. Since $p$ is a natural number, $\lceil n^p\rceil=n^p$. The published `annealRun` gives the law of the run. At $\beta=0$ there are no stages and the law is uniform.
-- source:
--   Hou–Liu–Yu, Simulated annealing and Weak Poincaré inequalities with inverse-polynomial accuracy for the Sherrington–Kirkpatrick model, arXiv:2610.09882, Algorithm 1, p.44; paragraph before it, p.43

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_annealRun

open OAI.CriticalSK SKAnnealing.Sampling

namespace SKWeakPoincare

/-- Number of temperature stages `L = ⌈βn⌉` of Algorithm 1.
Hou–Liu–Yu, arXiv:2610.09882, Algorithm 1, line 1, p. 44. -/
noncomputable def alg1Stages (β : ℝ) (n : ℕ) : ℕ :=
  ⌈β * n⌉₊

/-- The inverse-temperature schedule `β_j = jβ/L`, `0 ≤ j ≤ L`, of Algorithm 1 (line 1, p. 44).

**Formalization Note.** `L = alg1Stages β n` is `0` only when `β ≤ 0` or `n = 0`; then no stage is
run and the value of `β_j` is never used. -/
noncomputable def alg1Temp (β : ℝ) (n : ℕ) (j : ℕ) : ℝ :=
  (j : ℝ) * β / (alg1Stages β n : ℝ)

/-- **The output law of Algorithm 1** (simulated annealing from the uniform product distribution).
Hou–Liu–Yu, arXiv:2610.09882, Algorithm 1, p. 44: draw `x ∼ Unif({±1}^n)`; for `j = 1, …, L`
(`L = ⌈βn⌉`), repeat `⌈n^p⌉ = n^p` times: choose `i` uniformly from `[n]`, set
`h_i = β_j Σ_{ℓ≠i} A_{iℓ} x_ℓ`, and replace `x_i` by `+1` with probability `(1 + exp(−2h_i))^{-1}`,
by `−1` otherwise; return `x`.

**Formalization Note.** The disorder `W : Disorder n` (edges `i < j`) is the zero-diagonal
symmetric matrix `A`, and `β_j • W` is `β_j A`. One iteration of the inner loop is one step of
`OAI.CriticalSK.discreteKernel (β_j • W)` (site chosen uniformly, then the heat-bath update of
`OAI.CriticalSK.siteKernel`, whose probability of `x_i = +1` is `e^{h_i}/(e^{h_i} + e^{−h_i})`).
`annealRun` (DHMR26 bundle) returns the exact law of the final state: the uniform law times the
kernel powers in schedule order. `p` is a natural number, so `⌈n^p⌉ = n^p`. At `β = 0` there are
no stages and the law is uniform (the proof of Theorem 1.2 samples uniformly at `β = 0`). -/
noncomputable def alg1Law {n : ℕ} (W : Disorder n) (β : ℝ) (p : ℕ) : Spin n → ℝ :=
  annealRun (fun j => discreteKernel (alg1Temp β n j • W)) (n ^ p) (alg1Stages β n)

end SKWeakPoincare


