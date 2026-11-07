-- Prove2me | Definitions.Def_IntQuotHNP_Psi
-- name    : IntQuotHNP_Psi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:52:14.28055+00:00
-- url     : https://prove2.me/theorems/e155b1d2-41f9-466c-800f-79c7e3e29a10
-- title:
--   Eq. (7) — the factors $E_j(u)$ and the tail function $\Psi_X(u)$
-- statement:
--   For reals $X,p,u$ and a constant $C$,
--   $$
--   E_j(u)=\Bigl(\frac{X^2}{pu}\Bigr)^{j}+p^{-1/2},\qquad \Psi_X(u)=C\sum_{\kappa=1}^{N}\Bigl(\frac Xu\Bigr)^{\kappa}\prod_{j=1}^{\kappa-1}E_j(u)\;E_\kappa(u)^{N-\kappa}.
--   $$
--   This is the bound on the tail $\Pr[Z_{\mathrm{target}}>u]$.
--
--   **Formalization Note** The paper's $C_N$ is the argument $C$, so that Lemma 4.4 can assert a constant depending only on $N$ and Lemma 4.5 can bound $\Psi_X$ for it.
-- source:
--   Kang, Lee, Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number Problems, STOC 2027 submission (manuscript sha256 605f9dd3…), Lemma 4.4, eq. (7), p.23 (PDF p.24)

import Mathlib

namespace IntQuotHNP

/-- **The factor `E_j(u) = (X²/(pu))^j + p^{−1/2}`** of Lemma 4.4.
Kang, Lee, *Provable Recovery from Integer Quotients*, STOC 2027 submission (manuscript sha256
605f9dd3…), Lemma 4.4, p.23 (PDF p.24): "E_j(u) = (X²/(pu))^j + p^{−1/2} for j ∈ [N]".

**Formalization Note.** `p^{−1/2}` is `Real.rpow`. -/
noncomputable def E (X p : ℝ) (j : ℕ) (u : ℝ) : ℝ :=
  (X ^ 2 / (p * u)) ^ j + p ^ (-(1 / 2 : ℝ))

/-- **The tail function `Ψ_X(u)`** of Lemma 4.4, display (7).
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), Lemma 4.4, eq. (7), p.23
(PDF p.24): "Ψ_X(u) = C_N ∑_{κ=1}^N (X/u)^κ ∏_{j=1}^{κ−1} E_j(u) E_κ(u)^{N−κ}."

`Psi N C X p u = C · ∑_{κ=1}^{N} (X/u)^κ · (∏_{j=1}^{κ−1} E_j(u)) · E_κ(u)^{N−κ}`.

**Formalization Note.** The constant `C_N` of Lemma 4.4 is an argument `C`, so that Lemma 4.4 can
assert the existence of a constant depending only on `N` and Lemma 4.5 can bound `Ψ_X` for it. -/
noncomputable def Psi (N : ℕ) (C X p u : ℝ) : ℝ :=
  C * ∑ κ ∈ Finset.Icc 1 N,
    (X / u) ^ κ * (∏ j ∈ Finset.Ico 1 κ, E X p j u) * E X p κ u ^ (N - κ)

end IntQuotHNP


