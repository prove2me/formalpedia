-- Prove2me | Definitions.Def_HiringLP_SimLower_PoissonRatio
-- name    : HiringLP_SimLower_PoissonRatio
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:08.622048+00:00
-- url     : https://prove2.me/theorems/e8a63f69-3e7c-4619-adfd-223117137882
-- title:
--   Theorem 3, p. 30 — E[min{Pois(λ), k}] and α^τ_k = sup_{0≤s≤1}(s − s/τ + E[min{Pois(sk),k}]/(τk))
-- statement:
--   For $\lambda\ge 0$ and $k\in\mathbb N$, the expectation of a Poisson random variable with mean $\lambda$ truncated at $k$ is
--   $$\mathbb E[\min\{\mathrm{Pois}(\lambda),k\}]=\sum_{j=0}^\infty\min\{j,k\}\,\frac{e^{-\lambda}\lambda^j}{j!}.$$
--
--   For $k\ge 1$ and $\tau\in(0,1)$ the guarantee of the mission's main theorem is
--   $$\alpha^\tau_k=\sup_{0\le s\le 1}\Big(s-\frac{s}{\tau}+\frac{\mathbb E[\min\{\mathrm{Pois}(sk),k\}]}{\tau k}\Big),$$
--   the supremum over $s\in[0,1]$ of the objective $s-s/\tau+\mathbb E[\min\{\mathrm{Pois}(sk),k\}]/(\tau k)$, which is also the bound of Lemma 13 for a fixed $s$.
--
--   At $s=0$ the objective is $0$, so $\alpha^\tau_k\ge 0$; at $s=1$ it equals $1-e^{-k}k^k/(k!\,\tau)$ by Proposition EC.2.
--
--   **Formalization Note** The Poisson expectation is written as the series of the Poisson pmf (Mathlib's `ProbabilityTheory.poissonPMFReal` takes $\lambda\in\mathbb R_{\ge0}$; the explicit series is the same pmf and avoids the coercion). The objective is continuous in $s$, so the supremum over the compact interval is attained (shown in the mission's sanity file).
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. 30, Theorem 3 (α^τ_k); p. 29, Lemma 13

import Mathlib

namespace HiringLP.SimLower

/-- `E[min{Pois(λ), k}] = Σ_{j ≥ 0} min{j, k} · e^{−λ} λʲ / j!`, the expectation of a Poisson random
variable with mean `λ` truncated at `k`, written as the series of the Poisson pmf. -/
noncomputable def expMinPois (lam : ℝ) (k : ℕ) : ℝ :=
  ∑' j : ℕ, min (j : ℝ) k * (Real.exp (-lam) * lam ^ j / (j.factorial : ℝ))

/-- The objective `s − s/τ + E[min{Pois(sk), k}]/(τk)` inside `α^τ_k` (pp. 29–30). -/
noncomputable def ratioObj (k : ℕ) (τ s : ℝ) : ℝ :=
  s - s / τ + expMinPois (s * k) k / (τ * k)

/-- `α^τ_k = sup_{0 ≤ s ≤ 1} (s − s/τ + E[min{Pois(sk), k}]/(τk))` (Theorem 3, p. 30). -/
noncomputable def alpha (k : ℕ) (τ : ℝ) : ℝ :=
  sSup (ratioObj k τ '' Set.Icc 0 1)

end HiringLP.SimLower


