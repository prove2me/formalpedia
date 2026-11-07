-- Prove2me | Definitions.Def_UnionVolEst_poissonQuantile
-- name    : UnionVolEst_poissonQuantile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:02:46.511325+00:00
-- url     : https://prove2.me/theorems/8c31ed5a-a707-4e03-a252-6dc3a05d3ea3
-- title:
--   Poisson quantile function (realizing $N\sim\mathrm{Pois}(\lambda)$ from a uniform number)
-- statement:
--   For $\lambda\ge0$ and $u\in\mathbb R$, $\mathrm{poissonQuantile}(\lambda,u)$ is the least $m\in\mathbb N$ with
--   $$
--   u \le \sum_{j=0}^{m} e^{-\lambda}\frac{\lambda^j}{j!},
--   $$
--   and $0$ if there is none. If $U$ is uniform on $[0,1]$, then $\mathrm{poissonQuantile}(\lambda,U)\sim\mathrm{Pois}(\lambda)$ (inverse-transform sampling). It realizes line 9 of Alpona, "Draw $N_i \sim \mathrm{Pois}(\tilde V_i\cdot p)$", when the intensity depends on the run so far.
--
--   **Formalization Note** This is a device of the oracle model, not an object of the paper.
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §4.3, Algorithm 1 line 9, p.15 (PDF p.17)

import Mathlib

open scoped NNReal

namespace UnionVolEst

open Classical in
/-- The Poisson quantile function used to realize line 9 of Algorithm 1 ("Draw `Nᵢ ∼ Pois(Ṽᵢ·p)`",
Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §4.3, printed p.15, PDF p.17) from a uniform random number: `poissonQuantile λ u` is the
least `m` with `u ≤ Pois(λ)({0, …, m}) = Σ_{j ≤ m} e^{−λ} λʲ/j!`, and `0` if there is none.

**Formalization Note** If `U` is uniform on `[0, 1]` then `poissonQuantile λ U` has law
`Pois(λ)` (the event "no such `m`" is contained in `{U = 1}` when `λ > 0` and is empty when
`λ = 0`, so it is null). This is the standard inverse-transform realization; it is a device of the
oracle model, not an object of the paper. -/
noncomputable def poissonQuantile (r : ℝ≥0) (u : ℝ) : ℕ :=
  if h : ∃ m : ℕ, u ≤ (ProbabilityTheory.poissonMeasure r).real (Set.Iic m) then
    Nat.find h
  else 0

end UnionVolEst


