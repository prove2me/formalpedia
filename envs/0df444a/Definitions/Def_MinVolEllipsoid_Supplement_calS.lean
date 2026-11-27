-- Prove2me | Definitions.Def_MinVolEllipsoid_Supplement_calS
-- name    : MinVolEllipsoid_Supplement_calS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:29:59.719263+00:00
-- url     : https://prove2.me/theorems/9a967951-2a14-52be-9913-d8ca4835b90d
-- title:
--   The matrix $\mathcal S=[-S\ \ t]\in\mathbb R^{J\times(K+1)}$
-- statement:
--   For $S\in\mathbb R^{J\times K}$ and $t\in\mathbb R^J$, the matrix
--
--   $$
--   \mathcal S=\begin{bmatrix}-S & t\end{bmatrix}\in\mathbb R^{J\times(K+1)}
--   $$
--
--   has the $K$ columns of $-S$ followed by the column $t$. Its transpose is the matrix $\begin{bmatrix}-S^\top\\ t^\top\end{bmatrix}$ of display (11). For the lifted point $[x;\tau]$ one has $\mathcal S[x;\tau]=\tau t-Sx$, the slack vector of the polytope scaled by $\tau$.
--
--   The matrix appears in the semidefinite certificates (11) of Theorem 2 and (17) of Theorem 4 through the term $-\mathcal S^\top N\mathcal S$.
--
--   **Formalization Note** Columns are indexed by `Fin n ⊕ Unit`, the `Unit` column being the paper's last column $t$, matching the published `MinVolEllipsoid.borderedMatrix` and `MinVolEllipsoid.lift`.
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, Theorem 2, display (11), p.10; Theorem 4, display (17), p.15

import Mathlib

namespace MinVolEllipsoid.Supplement

/-- **The `J × (K+1)` matrix `𝒮 = [−S t]`** (Mittal & Hanasusanto, arXiv:1807.07507v4,
Theorem 2, display (11), p.10, where it appears as `[−S t]` with transpose `[−S⊤; t⊤]`; named `𝒮`
in Theorem 4, display (17), p.15).

`calS S t` has the columns of `−S` followed by the column `t`.

**Formalization Note** Columns are indexed by `Fin n ⊕ Unit`, the `Unit` column being the paper's
last column `t`, matching `MinVolEllipsoid.borderedMatrix` and `MinVolEllipsoid.lift`. The paper's
`[−S⊤; t⊤]` is `(calS S t)ᵀ`, so `−[−S⊤; t⊤] N [−S t] = −𝒮⊤N𝒮` is
`-((calS S t)ᵀ * N * calS S t)`. -/
def calS {n m : ℕ} (S : Matrix (Fin m) (Fin n) ℝ) (t : Fin m → ℝ) :
    Matrix (Fin m) (Fin n ⊕ Unit) ℝ :=
  Matrix.of fun j k => Sum.elim (fun i => -S j i) (fun _ => t j) k

end MinVolEllipsoid.Supplement


