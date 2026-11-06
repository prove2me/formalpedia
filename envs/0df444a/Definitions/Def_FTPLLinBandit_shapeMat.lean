-- Prove2me | Definitions.Def_FTPLLinBandit_shapeMat
-- name    : FTPLLinBandit_shapeMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:00:29.697024+00:00
-- url     : https://prove2.me/theorems/cfe71e01-11cb-4053-a26e-e6ca90cef4b4
-- title:
--   Shape matrix $\Sigma_t=\lambda I+\sum_{\tau<t}\hat\theta_\tau\hat\theta_\tau^\top$
-- statement:
--   For $\lambda\in\mathbb R$ and past estimates $\hat\theta_1,\dots,\hat\theta_{t-1}\in\mathbb R^d$, the **shape matrix** of round $t$ is
--   $$\Sigma_t=\lambda I+\sum_{\tau=1}^{t-1}\hat\theta_\tau\hat\theta_\tau^\top .$$
--   It is the shape of the elliptical perturbation $\rho_t=P_{\Sigma_t}$ (Figure 2), and the matrix against which Lemma 5 and the corollaries of Sections 6–7 measure the estimates; it is positive definite when $\lambda>0$.
--
--   **Formalization Note** The past is a list $\theta s$ of length $t$ indexed from $0$ ($\theta s_i$ is the paper's $\hat\theta_{i+1}$), so a list of length $t$ gives the paper's $\Sigma_{t+1}$.
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Figure 2, p.8; Lemma 5, p.11

import Mathlib

open Matrix

namespace FTPLLinBandit

/-- **The shape matrix `Σ_t = λI + ∑_{τ<t} θ̂_τ θ̂_τᵀ`.** Wei, arXiv:2610.17818, Figure 2,
Option 2, p.8 ("Σ_t = λI + ∑_{τ=1}^{t−1} θ̂_τ θ̂_τᵀ"); Lemma 5, p.11 ("set
Σ_t = λI + ∑_{j=1}^{t−1} θ̂_j θ̂_jᵀ").

For a finite list of past estimates `θs : Fin t → ℝ^d` (the paper's `θ̂_1, …, θ̂_{t−1}`),
`shapeMat λ θs = λ I + ∑_i θs_i θs_iᵀ`.

**Formalization Note.** The past estimates are indexed from `0`: `θs i` is the paper's
`θ̂_{i+1}`, so a list of length `t` gives the paper's `Σ_{t+1}`. Outer products act on coordinate
vectors `WithLp.ofLp`. -/
noncomputable def shapeMat {d t : ℕ} (lam : ℝ) (θs : Fin t → EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin d) (Fin d) ℝ :=
  lam • (1 : Matrix (Fin d) (Fin d) ℝ) +
    ∑ i, vecMulVec (WithLp.ofLp (θs i)) (WithLp.ofLp (θs i))

end FTPLLinBandit


