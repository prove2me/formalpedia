-- Prove2me | Definitions.Def_MinVolEllipsoid_Supplement_Mmat
-- name    : MinVolEllipsoid_Supplement_Mmat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:33:13.352272+00:00
-- url     : https://prove2.me/theorems/11328b1c-9f44-4af1-b93e-8356fd758f5e
-- title:
--   The matrix $M_{ij}(\alpha,\kappa)$ of Theorem 4
-- statement:
--   For $s\in\mathbb R^K$ (the row $S_{j:}$), $t_j\in\mathbb R$, $Q\in\mathbb R^{K\times K}$, $q\in\mathbb R^K$ (the data $Q_i,q_i$), $\alpha\in\mathbb R^K$ and $\kappa\in\mathbb R$, Theorem 4 uses the $(K+1)\times(K+1)$ matrix
--
--   $$
--   M_{ij}(\alpha,\kappa)=\begin{bmatrix}-\tfrac12\bigl(S_{j:}\alpha^\top Q_i+Q_i\alpha S_{j:}^\top\bigr) & \tfrac12\bigl(t_jQ_i\alpha-(\alpha^\top q_i+\kappa)S_{j:}\bigr)\\ \tfrac12\bigl(t_jQ_i\alpha-(\alpha^\top q_i+\kappa)S_{j:}\bigr)^\top & (\alpha^\top q_i+\kappa)t_j\end{bmatrix}.
--   $$
--
--   For symmetric $Q_i$ its quadratic form at $[x;\tau]$ is $(\tau t_j-S_{j:}^\top x)\bigl(\tau\kappa+\alpha^\top(Q_ix+\tau q_i)\bigr)$, the product of an affine slack and a second-order-cone slack.
--
--   **Formalization Note** It is the published `MinVolEllipsoid.borderedMatrix` whose last column and last row are the same vector; the outer products are written with `vecMulVec`.
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, Theorem 4, definition of M_ij(α, κ), p.15

import Mathlib
import Definitions.Def_MinVolEllipsoid_borderedMatrix

open Matrix

namespace MinVolEllipsoid.Supplement

/-- **The matrix `M_ij(α, κ)`** (Mittal & Hanasusanto, arXiv:1807.07507v4, Theorem 4, p.15):

`M_ij(α, κ) = [−½(S_{j:}α⊤Q_i + Q_iαS_{j:}⊤)   ½(t_jQ_iα − (α⊤q_i + κ)S_{j:});`
`             ½(t_jQ_iα − (α⊤q_i + κ)S_{j:})⊤   (α⊤q_i + κ)t_j]`.

`Mmat s tj Q q α κ` is this `(K+1) × (K+1)` matrix with `s = S_{j:}` (the transpose of the `j`-th
row of `S`), `tj = t_j`, `Q = Q_i`, `q = q_i`.

**Formalization Note** It is the published `MinVolEllipsoid.borderedMatrix` whose last column and
last row are the same vector `c = ½(t_j Q_i α − (α⊤q_i + κ) S_{j:})`. The outer products
`S_{j:}(α⊤Q_i)` and `(Q_iα)S_{j:}⊤` are `vecMulVec s (α ᵥ* Q)` and `vecMulVec (Q *ᵥ α) s`. -/
noncomputable def Mmat {n : ℕ} (s : Fin n → ℝ) (tj : ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (q : Fin n → ℝ)
    (α : Fin n → ℝ) (κ : ℝ) : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
  MinVolEllipsoid.borderedMatrix
    (-((1 / 2 : ℝ) • (vecMulVec s (α ᵥ* Q) + vecMulVec (Q *ᵥ α) s)))
    ((1 / 2 : ℝ) • (tj • (Q *ᵥ α) - (α ⬝ᵥ q + κ) • s))
    ((1 / 2 : ℝ) • (tj • (Q *ᵥ α) - (α ⬝ᵥ q + κ) • s))
    ((α ⬝ᵥ q + κ) * tj)

end MinVolEllipsoid.Supplement


