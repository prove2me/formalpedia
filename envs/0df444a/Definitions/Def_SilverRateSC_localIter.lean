-- Prove2me | Definitions.Def_SilverRateSC_localIter
-- name    : SilverRateSC_localIter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:45:03.499259+00:00
-- url     : https://prove2.me/theorems/7ffc7d0f-019c-44ec-9c9e-d29fea1ce27c
-- title:
--   The local gradient updates (9)
-- statement:
--   Fix $\kappa$, a local hard function $\Phi:\mathbb R^2\to\mathbb R$, gap stepsizes $h_1,\dots,h_{m_{\rm gap}}$ followed by a checkpoint stepsize $h_{m_{\rm gap}+1}=b_i$, and contributions $f_j$ of the preceding component. Starting from $(X_0,Y_0)$, the local updates are
--   $$\begin{pmatrix}X_j\\Y_j\end{pmatrix}=\Bigl(1-\frac{h_j}{\kappa}\Bigr)\begin{pmatrix}X_{j-1}\\Y_{j-1}\end{pmatrix}-\frac{(1-1/\kappa)h_j}{2}\nabla\Phi(X_{j-1},Y_{j-1})+h_j\begin{pmatrix}f_j\\0\end{pmatrix},\qquad 1\le j\le m_{\rm gap}+1.$$
--   They are the gradient-descent updates of the global objective restricted to two adjacent coordinates while later components are inactive.
--
--   **Formalization Note** The stepsizes are a list read left to right (entry $j-1$ is $h_j$); $\nabla$ is Mathlib's gradient on $\mathbb R^2$, used only for differentiable $\Phi$.
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), §3, (9), p.14

import Mathlib

namespace SilverRateSC

/-- One local update (9): `(1 − h/κ) z − ((1 − 1/κ) h / 2) ∇Φ(z) + h (f, 0)`. -/
noncomputable def localStep (κ : ℝ) (Φ : EuclideanSpace ℝ (Fin 2) → ℝ) (h f : ℝ)
    (z : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  (1 - h / κ) • z - ((1 - 1 / κ) * h / 2) • gradient Φ z + !₂[h * f, 0]

/-- **The local updates** (9): starting from `z₀ = (X_0, Y_0)`, for `1 ≤ j`,
`(X_j, Y_j) = (1 − h_j/κ)(X_{j−1}, Y_{j−1}) − ((1 − 1/κ) h_j / 2) ∇Φ(X_{j−1}, Y_{j−1}) + h_j (f_j, 0)`.

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, §3, (9), p. 14.

**Formalization Note** `steps` is the list `(h_1, …, h_{m_gap}, b_i)` of the gap stepsizes
followed by the checkpoint stepsize, read left to right; `h_j` is its entry at position `j − 1`
(`0` past the end, never used). `f j` is the preceding component's contribution `f_j` at step
`j ≥ 1`. `∇` is Mathlib's `gradient` on `EuclideanSpace ℝ (Fin 2)`, coordinate `0` is `X` and `1`
is `Y`; every statement using it assumes `Φ` differentiable. -/
noncomputable def localIter (κ : ℝ) (Φ : EuclideanSpace ℝ (Fin 2) → ℝ) (steps : List ℝ)
    (f : ℕ → ℝ) (z₀ : EuclideanSpace ℝ (Fin 2)) : ℕ → EuclideanSpace ℝ (Fin 2)
  | 0 => z₀
  | j + 1 => localStep κ Φ (steps.getD j 0) (f (j + 1)) (localIter κ Φ steps f z₀ j)

end SilverRateSC


