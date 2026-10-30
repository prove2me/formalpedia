-- Prove2me | Definitions.Def_DDROCS_UCS
-- name    : DDROCS_UCS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:30:56.265159+00:00
-- url     : https://prove2.me/theorems/fa5a34f4-e1f4-4ca9-9365-6e797a878433
-- title:
--   Mean–covariance uncertainty set $\mathcal U^{CS}_\epsilon$
-- statement:
--   Let $\hat\mu \in \mathbb R^d$, $\Gamma_1 \in \mathbb R$, $C \in \mathbb R^{d\times d}$ and $\epsilon \in \mathbb R$. The **mean–covariance uncertainty set** is
--
--   $$
--   \mathcal U^{CS}_\epsilon \;=\; \Bigl\{\hat\mu + y + C^\top w \;:\; y, w \in \mathbb R^d,\ \|y\| \le \Gamma_1,\ \|w\| \le \sqrt{\tfrac1\epsilon - 1}\Bigr\}.
--   $$
--
--   In the paper $\hat\mu$ is the sample mean, $\Gamma_1$ a threshold for the mean, and $C$ a Cholesky factor with $C^\top C = \hat\Sigma + \Gamma_2 I$. The set is an ellipsoid enlarged by a ball; its support function equals the bound (34) on the worst-case Value at Risk over $\mathcal P^{CS}$.
--
--   **Formalization Note** $\Gamma_1$ and $C$ are parameters; the relation $C^\top C = \hat\Sigma + \Gamma_2 I$ is a hypothesis of the theorems that use the set. $C^\top w$ is the matrix $C^\top$ acting on `EuclideanSpace ℝ (Fin d)`; both norms are Euclidean. Values for $\epsilon \notin (0,1)$ are never read.
-- source:
--   Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, eq. (35), p. 25

import Mathlib
open Matrix

namespace DDROCS

/-- **The mean–covariance uncertainty set `U^CS_ε`**, eq. (35).
Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, eq. (35), p. 25:
"`U^CS_ϵ = { µ̂ + y + Cᵀw : ∃y, w ∈ ℝ^d s.t. ‖y‖ ≤ Γ^B_1, ‖w‖ ≤ √(1/ϵ − 1) }`, where
`CᵀC = Σ̂ + Γ^B_2 I` is a cholesky decomposition."

`UCS μhat Γ₁ C ε` is the set of points `μhat + y + Cᵀw` with `‖y‖ ≤ Γ₁` and
`‖w‖ ≤ √(1/ε − 1)`.

**Formalization Note.** The threshold `Γ₁` and the factor `C` are parameters; the relation
`CᵀC = Σ̂ + Γ₂ I` is a hypothesis of the theorems that use the set. `Cᵀw` is
`Matrix.toEuclideanLin Cᵀ w`, the matrix `Cᵀ` acting on `EuclideanSpace ℝ (Fin d)`. Both norms
are Euclidean (the paper writes `‖·‖`). Values for `ε ∉ (0,1)` are never read. -/
noncomputable def UCS {d : ℕ} (μhat : EuclideanSpace ℝ (Fin d)) (Γ₁ : ℝ)
    (C : Matrix (Fin d) (Fin d) ℝ) (ε : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {u | ∃ y w : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ Γ₁ ∧ ‖w‖ ≤ Real.sqrt (1 / ε - 1) ∧
    u = μhat + y + Matrix.toEuclideanLin Cᵀ w}

end DDROCS


