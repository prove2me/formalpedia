-- Prove2me | Definitions.Def_SpectralProjGrad_Shared_scaledProjGrad
-- name    : SpectralProjGrad_Shared_scaledProjGrad
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:58:16.483293+00:00
-- url     : https://prove2.me/theorems/85797bbb-def1-455d-a7c4-805bdae1f009
-- title:
--   Scaled projected gradient $g_t(x)=P(x-t\,g(x))-x$
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$, let $g(x)=\nabla f(x)$ be its gradient, and let $P:\mathbb R^n\to\mathbb R^n$ be a map (in every statement that uses it, the orthogonal projection onto the feasible set $\Omega$). For $t\in\mathbb R$ and $x\in\mathbb R^n$ the **scaled projected gradient** is
--
--   $$
--   g_t(x)=P\bigl(x-t\,g(x)\bigr)-x .
--   $$
--
--   For an iterate $x_k$ of SPG2 and $t=\alpha_k$ this is the spectral projected gradient direction $d_k$; the trial points of SPG1 are the points $x+g_\lambda(x)=P(x-\lambda g(x))$ on the projection arc; and for $t=1$ it is the continuous projected gradient used in the stopping test of Step 1.
--
--   Used by both missions of this paper: 01-spg2 (SPG2; p. 4, where $g_{\alpha_k}(x_k)$ is the search direction $d_k$ and $g_1$ the stopping test) and 02-spg1 (SPG1; p. 4, where $x+g_\lambda(x)=P(x-\lambda g(x))$ are the trial points on the projection arc).
--
--   **Formalization Note** The gradient is Mathlib's `gradient f x`, which is the true gradient wherever $f$ is differentiable. The paper defines $g_t(x)$ for $x\in\Omega$ and $t>0$; the Lean function is total, and every statement restricts $x$ and $t$ as the paper does.
-- source:
--   Birgin, Martínez & Raydan, Nonmonotone Spectral Projected Gradient Methods on Convex Sets, authors' updated version (July 2004) of SIAM J. Optim. 10(4) (2000), https://www.ime.unicamp.br/~martinez/bmr.pdf, p. 4, definition of the scaled projected gradient g_t(x)

import Mathlib

namespace SpectralProjGrad.Shared

/-- The scaled projected gradient `g_t(x) = P(x - t g(x)) - x`, where `g = ∇f` is the gradient
of `f` and `P` is a map on `ℝⁿ` (in every statement of the mission, the projection onto `Ω`). -/
noncomputable def scaledProjGrad {n : ℕ}
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  P (x - t • gradient f x) - x

end SpectralProjGrad.Shared


