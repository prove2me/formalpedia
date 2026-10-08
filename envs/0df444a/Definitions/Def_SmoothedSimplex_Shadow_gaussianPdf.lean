-- Prove2me | Definitions.Def_SmoothedSimplex_Shadow_gaussianPdf
-- name    : SmoothedSimplex_Shadow_gaussianPdf
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:46:04.074915+00:00
-- url     : https://prove2.me/theorems/e4b3e707-b2cf-4749-8648-34ed0ac35f0e
-- title:
--   §2.4 — density of the Gaussian of standard deviation $\sigma$ centered at $c$ in $\mathbb R^k$
-- statement:
--   For a point $c\in\mathbb R^k$ and $\sigma>0$, the **Gaussian density of standard deviation $\sigma$ centered at $c$** is
--
--   $$
--   \mu(x)=\Big(\frac{1}{\sqrt{2\pi}\,\sigma}\Big)^{k}\, e^{-\|x-c\|^{2}/2\sigma^{2}},\qquad x\in\mathbb R^k .
--   $$
--
--   It is the density of the random vector whose coordinates are independent normal variables $N(c_i,\sigma^2)$. Spielman and Teng perturb every constraint vector of a linear program by such a Gaussian, and the densities $\mu_i(a_i)$ appear explicitly in the integrands of the lemmas of their Section 4.
--
--   **Formalization Note** $\mathbb R^k$ is `EuclideanSpace ℝ (Fin k)`. The formula is used only with $\sigma>0$.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, §2.4, printed p. 19 (PDF p. 19); formula also on p. 54 (proof of Lemma 4.2.3)

import Mathlib

namespace SmoothedSimplex.Shadow

/-- The density of the Gaussian distribution of standard deviation `σ` centered at `c` in `ℝ^k`
(Spielman & Teng, *Smoothed Analysis of Algorithms*, arXiv:cs/0111050v7, §2.4, printed p. 19,
PDF p. 19; also the formula in the proof of Lemma 4.2.3, printed p. 54, PDF p. 54):
`μ(x) = (1/(√(2π) σ))^k · exp(−‖x − c‖² / (2σ²))`.

**Formalization Note.** `ℝ^k` is `EuclideanSpace ℝ (Fin k)`. The formula is meaningful for
`σ > 0`, which every statement using it assumes. -/
noncomputable def gaussianPdf {k : ℕ} (c : EuclideanSpace ℝ (Fin k)) (σ : ℝ)
    (x : EuclideanSpace ℝ (Fin k)) : ℝ :=
  (1 / (Real.sqrt (2 * Real.pi) * σ)) ^ k * Real.exp (-(‖x - c‖ ^ 2) / (2 * σ ^ 2))

end SmoothedSimplex.Shadow


