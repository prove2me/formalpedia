-- Prove2me | Definitions.Def_MultiUnitProphet_Poisson
-- name    : MultiUnitProphet_Poisson
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:12:36.044432+00:00
-- url     : https://prove2.me/theorems/e8c22f82-3a46-4207-b62d-f34701025d93
-- title:
--   Poisson values $\delta_k(X^\lambda)=\mathbb P[X^\lambda\le k-1]$ and $\mu_k(X^\lambda)=\frac1k\mathbb E[\min\{X^\lambda,k\}]$
-- statement:
--   For a Poisson random variable $X^\lambda$ with rate $\lambda\ge0$ and a supply $k$,
--
--   $$\delta_k(X^\lambda)=\mathbb P[X^\lambda\le k-1]=\sum_{j=0}^{k-1}e^{-\lambda}\frac{\lambda^j}{j!},\qquad \mu_k(X^\lambda)=\frac1k\,\mathbb E[\min\{X^\lambda,k\}]=\frac1k\sum_{j\ge0}\min\{j,k\}\,e^{-\lambda}\frac{\lambda^j}{j!}.$$
--
--   The rate $\lambda_k$ of eq. (1.1) balances the two, and the competitive ratio of Theorem 1 is $\phi_k=\delta_k(X^{\lambda_k})=\mu_k(X^{\lambda_k})$.
--
--   **Formalization Note** The rate is $\lambda\in\mathbb R_{\ge0}$. $\mu_k$ reuses the published series `HiringLP.SimLower.expMinPois`; $\delta_k$ writes out the same Poisson pmf.
-- source:
--   Chawla, Devanur & Lykouris, Static pricing for multi-unit prophet inequalities, arXiv:2007.07990v4, §1.1, eq. (1.1), p.2; (3.1)–(3.2), p.7; Theorem 1, p.8

import Mathlib
import Definitions.Def_HiringLP_SimLower_PoissonRatio

namespace MultiUnitProphet

open scoped NNReal

/-- **`δ_k(X^λ) = P[X^λ ≤ k − 1]` for a Poisson random variable `X^λ` with rate `λ`**
(Chawla, Devanur & Lykouris, arXiv:2007.07990v4, (3.1), p.7, applied in eq. (1.1), p.2 and
Theorem 1, p.8).

**Formalization Note.** `Σ_{j=0}^{k−1} e^{−λ} λ^j / j!`, the Poisson pmf written out (the same
series as `HiringLP.SimLower.expMinPois`); the rate is `λ : ℝ≥0`. -/
noncomputable def deltaPois (k : ℕ) (lam : ℝ≥0) : ℝ :=
  ∑ j ∈ Finset.range k, Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ j / (j.factorial : ℝ)

/-- **`µ_k(X^λ) = (1/k) E[min{X^λ, k}]` for a Poisson random variable `X^λ` with rate `λ`**
(arXiv:2007.07990v4, (3.2), p.7, applied in eq. (1.1), p.2 and Theorem 1, p.8).

**Formalization Note.** Uses the published `HiringLP.SimLower.expMinPois λ k =
Σ_{j ≥ 0} min{j, k} e^{−λ} λ^j / j!` at the real rate `(λ : ℝ) ≥ 0`. -/
noncomputable def muPois (k : ℕ) (lam : ℝ≥0) : ℝ :=
  HiringLP.SimLower.expMinPois (lam : ℝ) k / k

end MultiUnitProphet


