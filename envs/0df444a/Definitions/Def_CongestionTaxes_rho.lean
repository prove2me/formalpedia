-- Prove2me | Definitions.Def_CongestionTaxes_rho
-- name    : CongestionTaxes_rho
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:31:44.255481+00:00
-- url     : https://prove2.me/theorems/31672cdf-df0e-4113-8c06-9fad0682b239
-- title:
--   Hardness factor $\rho_\ell$
-- statement:
--   For a resource cost $\ell$ with $\ell(0)=0$, the **hardness factor** is
--
--   $$
--   \rho_\ell=\sup_{x\in\mathbb N}\frac{\mathbb E_{P\sim\mathrm{Poi}(x)}[P\ell(P)]}{x\ell(x)},\qquad \mathbb E_{P\sim\mathrm{Poi}(x)}[P\ell(P)]=\sum_{k=0}^\infty k\ell(k)\frac{x^ke^{-x}}{k!}.
--   $$
--
--   The supremum is over positive integers $x$, and $\rho_\ell=\infty$ is possible. For $\ell(x)=x$ one gets $\rho_\ell=2$. The paper shows that $\sup_{\ell\in\mathcal L}\rho_\ell$ is both the NP-hardness threshold for minimizing social cost and the price of anarchy achieved by its taxes.
--
--   **Formalization Note** The value lives in $[0,\infty]$ (`ℝ≥0∞`): the series is summed in extended nonnegative reals and equals $\infty$ when it diverges.
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, display (4), p.5; footnote 5, p.5

import Mathlib

open scoped ENNReal

namespace CongestionTaxes

/-- The **hardness factor** of a resource cost (Paccagnan, Gairing, arXiv:2105.07480v2,
display (4), p.5, with footnote 5):
`ρ_ℓ = sup_{x ∈ ℕ} E_{P∼Poi(x)}[P ℓ(P)] / (x ℓ(x))`, where
`E_{P∼Poi(x)}[P ℓ(P)] = ∑_{k=0}^∞ k ℓ(k) x^k e^{−x} / k!` and `ℓ(0) = 0`.

**Formalization Note** The supremum runs over the integers `x ≥ 1` (the paper's `ℕ`), not over
reals. The value is computed in `ℝ≥0∞`: the series is a sum of extended nonnegative reals, equal to
`⊤` when it diverges, so `ρ_ℓ = ∞` is representable (the paper allows it, p.5). Under Assumption 1
every term is nonnegative and `x ℓ(x) > 0`, so `ENNReal.ofReal` changes no value. -/
noncomputable def rho (ℓ : ℕ → ℝ) : ℝ≥0∞ :=
  ⨆ (x : ℕ) (_ : 1 ≤ x),
    (∑' k : ℕ, ENNReal.ofReal ((k : ℝ) * ℓ k * (x : ℝ) ^ k * Real.exp (-(x : ℝ)) /
        (k.factorial : ℝ))) / ENNReal.ofReal ((x : ℝ) * ℓ x)

end CongestionTaxes


