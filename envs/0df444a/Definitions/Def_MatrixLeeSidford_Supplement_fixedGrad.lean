-- Prove2me | Definitions.Def_MatrixLeeSidford_Supplement_fixedGrad
-- name    : MatrixLeeSidford_Supplement_fixedGrad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T15:13:43.23395+00:00
-- url     : https://prove2.me/theorems/6386e7cb-611a-4229-9bde-780e1a16d4c3
-- title:
--   Fixed-weight gradient $g_G(y)_i=-\alpha\operatorname{tr}[MB_i]$
-- statement:
--   Let $y$ be feasible, $G\succ0$, and let $M$ be the gradient matrix at $(y,G)$. The **fixed-weight gradient** is the vector $g=g_G(y)\in\mathbb R^m$ with
--   $$
--   g_i:=-\alpha\operatorname{tr}[MB_i]\qquad(i\in[m]),
--   $$
--   where $\alpha=10^6s^2$. It is the gradient of $y\mapsto\frac\alpha2f_y(G)$ with $G$ held fixed, and at the optimal weight it equals $\nabla F(y)$.
--
--   **Formalization Note** A vector of $\mathbb R^m$ with its Euclidean structure; $\alpha$ is the base mission's published scaling $10^6s^2$.
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Definition 8.1, p.53; Definition 5.1, p.37

import Mathlib
import Definitions.Def_MatrixLeeSidford_alphaParam
import Definitions.Def_MatrixLeeSidford_Supplement_gradMatG

open Matrix

namespace MatrixLeeSidford.Supplement

/-- The **fixed-weight gradient** `g = g_G(y)`, `gᵢ := −α tr[M Bᵢ]`, at a query state `(y, G)`, with `M` the
gradient matrix at `(y, G)` and `α = 10⁶ s²` (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), Definition 8.1, p.53; `α` from Definition 5.1, p.37).

**Formalization Note** A vector of `EuclideanSpace ℝ (Fin m)` (the same space as the dual point `y`);
`α` is the published `alphaParam s`. -/
noncomputable def fixedGrad {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (s : ℕ) (y : EuclideanSpace ℝ (Fin m))
    (G : Matrix (Fin m) (Fin m) ℝ) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun i => -alphaParam s * (gradMatG A C s y G * normB A (slack A C y) i).trace

end MatrixLeeSidford.Supplement


