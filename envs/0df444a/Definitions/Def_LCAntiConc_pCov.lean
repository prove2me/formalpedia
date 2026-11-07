-- Prove2me | Definitions.Def_LCAntiConc_pCov
-- name    : LCAntiConc_pCov
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:46:58.284394+00:00
-- url     : https://prove2.me/theorems/06cc044b-1287-4903-8a6a-6ffb80b3e731
-- title:
--   Pseudo-covariance $\Sigma_{\tilde{\mathbb E}}=\tilde{\mathbb E}(v-\mu)(v-\mu)^\top$
-- statement:
--   The **pseudo-covariance** of a pseudo-expectation $\tilde{\mathbb E}$ with pseudo-mean $\mu=\tilde{\mathbb E}\,v$ is the $n\times n$ matrix
--
--   $$\Sigma_{\tilde{\mathbb E}}=\tilde{\mathbb E}\,(v-\mu)(v-\mu)^\top,\qquad (\Sigma_{\tilde{\mathbb E}})_{ij}=\tilde{\mathbb E}\big[(v_i-\mu_i)(v_j-\mu_j)\big].$$
--
--   For a pseudo-expectation on the sphere it is positive semidefinite with trace $1-\|\mu\|^2\le1$.
--
--   **Formalization Note** Applied only to pseudo-expectations of degree at least $2$.
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), Lemmas 4.3–4.4, p.18 (PDF p.20); Lemma 4.5, p.21 (PDF p.23)

import Mathlib

namespace LCAntiConc

/-- The pseudo-covariance `Σ_Ẽ = Ẽ (v - μ)(v - μ)ᵀ` of a pseudo-expectation, with `μ = Ẽ v`:
entry `(i, j)` is `Ẽ[(vᵢ - μᵢ)(vⱼ - μⱼ)]`.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), Lemma 4.3 ("Σ = Ẽ(μ - v)(μ - v)ᵀ"), and
Lemma 4.4 ("Σᵢ = Ẽᵢ(v - μᵢ)(v - μᵢ)ᵀ"), p.18 (PDF p.20); Lemma 4.5 (`Σ_{Ẽᵢ}`), p.21 (PDF p.23).

**Formalization Note** It is applied only to pseudo-expectations of degree at least `2`, where it
is determined by the pseudo-expectation. -/
noncomputable def pCov {n : ℕ} (L : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    L ((MvPolynomial.X i - MvPolynomial.C (L (MvPolynomial.X i))) *
      (MvPolynomial.X j - MvPolynomial.C (L (MvPolynomial.X j))))

end LCAntiConc


