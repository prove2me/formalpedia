-- Prove2me | Definitions.Def_StaticProphetSec_poisE
-- name    : StaticProphetSec_poisE
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:20.537379+00:00
-- url     : https://prove2.me/theorems/b2ea36a8-b94c-406f-8f38-317a4a93a72a
-- title:
--   The Poisson expectation $\mathbb E[f(\mathrm{Pois}(\lambda))]$
-- statement:
--   For $\lambda\ge0$ and $f:\mathbb N_0\to\mathbb R$,
--
--   $$\mathbb E[f(\mathrm{Pois}(\lambda))]=\sum_{j=0}^\infty f(j)\,e^{-\lambda}\frac{\lambda^j}{j!}.$$
--
--   At $\lambda=0$ the law is the point mass at $0$.
--
--   **Formalization Note** The mass of $j$ is Mathlib's `poissonMeasure`. The statements using this expectation apply it to bounded $f$, for which the series converges absolutely.
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, Lemma 7, p.29

import Mathlib

open scoped NNReal

namespace StaticProphetSec

/-- The expectation `E[f(Pois(λ))]` of a function of a Poisson variable with mean `λ ≥ 0`
(Arnosti & Ma, arXiv:2108.12893v2, Lemma 7, p.29).

**Formalization Note.** `ProbabilityTheory.poissonMeasure lam` assigns `{j}` the mass
`e^{-λ} λ^j / j!`; at `λ = 0` it is the point mass at `0`. The statements using `poisE` apply it
to bounded `f`, for which the series converges absolutely, so the junk value of `tsum` does not
arise. -/
noncomputable def poisE (f : ℕ → ℝ) (lam : ℝ≥0) : ℝ :=
  ∑' j, f j * (ProbabilityTheory.poissonMeasure lam).real {j}

end StaticProphetSec


