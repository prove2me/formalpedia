-- Prove2me | Definitions.Def_CubicRegNewton_LocalQuad_delta
-- name    : CubicRegNewton_LocalQuad_delta
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:25:57.131935+00:00
-- url     : https://prove2.me/theorems/2d074c98-5b52-48ea-8142-2da80e9778cf
-- title:
--   The local measure $\delta(x)=L\|f'(x)\|/\lambda_n^2(f''(x))$
-- statement:
--   For $L$, the gradient $f'$ and the Hessian $f''$, set
--
--   $$
--   \delta(x)=\frac{L\,\|f'(x)\|}{\lambda_n^2(f''(x))} .
--   $$
--
--   Along a run $(x_k)$ of the relaxed scheme (3.5) the paper writes $\delta_k=\delta(x_k)$. It measures the gradient against the squared curvature and governs the local behaviour of cubic regularization: Theorem 3 assumes $\delta_0\le\frac14$.
--
--   **Formalization Note** Real division; the denominator is positive exactly when $f''(x)$ is positive definite (and $n\ge1$). That this holds along the run is a conclusion of Theorem 3, item 1, never a hypothesis.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, doi:10.1007/s10107-006-0706-8, p. 186 (PDF p. 10), below (3.5)

import Mathlib
import Definitions.Def_CubicRegNewton_LocalQuad_lamMin

namespace CubicRegNewton.LocalQuad

/-- **The local-convergence measure δ_k.**
Nesterov & Polyak, *Cubic regularization of Newton method and its global performance*,
Math. Program. Ser. A 108 (2006) 177–205, p. 186, below (3.5): "Denote
δk = L‖f'(xk)‖ / λ²n(f''(xk))."

`delta L f' f'' x = L‖f'(x)‖ / λₙ(f''(x))²`, so that `δ_k = delta L f' f'' (x k)`.

**Formalization Note.** Real division. The denominator is positive exactly when `f''(x)` is
positive definite (and `n ≥ 1`); that `δ_k` is well defined in this sense along the run is part of
the conclusion of Theorem 3, item 1, never a hypothesis. `λₙ` is `lamMin` (Reading 5). -/
noncomputable def delta {n : ℕ} (L : ℝ)
    (f' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (f'' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  L * ‖f' x‖ / lamMin (f'' x) ^ 2

end CubicRegNewton.LocalQuad


