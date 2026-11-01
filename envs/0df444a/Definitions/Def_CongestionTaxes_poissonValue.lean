-- Prove2me | Definitions.Def_CongestionTaxes_poissonValue
-- name    : CongestionTaxes_poissonValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:31:45.356711+00:00
-- url     : https://prove2.me/theorems/479af170-11e3-4b73-81d3-3e9b1b575eb8
-- title:
--   Poisson expected cost $p(v)=\mathbb E_{P\sim\mathrm{Poi}(v)}[P\ell(P)]$
-- statement:
--   For a resource cost $\ell$ with $\ell(0)=0$ and $v\ge0$, the **Poisson expected cost** is
--
--   $$
--   p(v)=\mathbb E_{P\sim\mathrm{Poi}(v)}\bigl[P\ell(P)\bigr]=\Bigl(\sum_{i=0}^{\infty}i\,\ell(i)\,\frac{v^i}{i!}\Bigr)e^{-v}.
--   $$
--
--   It replaces the cost $c(x)=x\ell(x)$ in the convex relaxation (12) of the minimum-social-cost problem, and it defines the taxes of Definition 4.
--
--   **Formalization Note** The series is a Lean `tsum`, which takes the value $0$ when the series diverges; every statement using $p$ assumes either $\rho_\ell<\infty$, under which the series converges for all $v\ge0$ (Lemma 4), or the convergence of the series itself.
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, display (10), p.18; footnote 5, p.5

import Mathlib

namespace CongestionTaxes

/-- The **Poisson expected cost** `p(v) = E_{P∼Poi(v)}[P ℓ(P)] = (∑_{i=0}^∞ i ℓ(i) vⁱ / i!) e^{−v}`
(Paccagnan, Gairing, arXiv:2105.07480v2, display (10), p.18, and footnote 5, p.5), for a cost
`ℓ` extended by `ℓ(0) = 0`.

**Formalization Note** The series is a Lean `tsum`, which is `0` when the series is not summable.
Every statement that uses `p` assumes `ρ_ℓ < ∞`, under which the series converges for every
`v ≥ 0` (the well-definedness part of Lemma 4, p.28). The definition is the paper's series, not
Mathlib's Poisson measure; the two agree on `v ≥ 0`. Values at `v < 0` are never used. -/
noncomputable def poissonValue (ℓ : ℕ → ℝ) (v : ℝ) : ℝ :=
  (∑' i : ℕ, (i : ℝ) * ℓ i * v ^ i / (i.factorial : ℝ)) * Real.exp (-v)

end CongestionTaxes


