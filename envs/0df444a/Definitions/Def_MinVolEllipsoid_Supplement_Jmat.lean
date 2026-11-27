-- Prove2me | Definitions.Def_MinVolEllipsoid_Supplement_Jmat
-- name    : MinVolEllipsoid_Supplement_Jmat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:32:41.974675+00:00
-- url     : https://prove2.me/theorems/7a00aaac-0f1d-4bed-bf2a-b33c9e85d0e1
-- title:
--   The matrix $J_i$ of Theorem 4
-- statement:
--   For $Q\in\mathbb R^{K\times K}$ and $q\in\mathbb R^K$, Theorem 4 uses the $(K+1)\times(K+1)$ matrix
--
--   $$
--   J=\begin{bmatrix}Q^2 & Q^\top q\\ q^\top Q & q^\top q-1\end{bmatrix},
--   $$
--
--   with $J_i$ the matrix for $Q=Q_i$, $q=q_i$. For symmetric $Q$ its quadratic form at $[x;\tau]$ is $\|Qx+\tau q\|^2-\tau^2$, so it encodes the ellipsoidal constraint $\|Q_ix+q_i\|^2\le1$ of (16).
--
--   **Formalization Note** It is the published `MinVolEllipsoid.borderedMatrix` with upper-left block $Q\cdot Q$, last column $Q^\top q$, last row $q^\top Q$ and corner $q^\top q-1$, copied literally from p.15.
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, Theorem 4, definition of J_i, p.15

import Mathlib
import Definitions.Def_MinVolEllipsoid_borderedMatrix

open Matrix

namespace MinVolEllipsoid.Supplement

/-- **The matrix `J_i`** (Mittal & Hanasusanto, arXiv:1807.07507v4, Theorem 4, p.15):

`J_i = [Q_i²  Q_i⊤q_i; q_i⊤Q_i  q_i⊤q_i − 1] ∈ 𝕊ᴷ⁺¹`.

`Jmat Q q` is this `(K+1) × (K+1)` matrix for `Q = Q_i`, `q = q_i`.

**Formalization Note** It is the published `MinVolEllipsoid.borderedMatrix` with upper-left block
`Q * Q`, last column `Q⊤ q` (`Qᵀ *ᵥ q`), last row `q⊤ Q` (`q ᵥ* Q`) and corner `q ⬝ᵥ q − 1`,
copied literally from the page (for symmetric `Q`, as in Theorem 4, it is symmetric). -/
def Jmat {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (q : Fin n → ℝ) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
  MinVolEllipsoid.borderedMatrix (Q * Q) (Qᵀ *ᵥ q) (q ᵥ* Q) (q ⬝ᵥ q - 1)

end MinVolEllipsoid.Supplement


