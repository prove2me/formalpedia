-- Prove2me | Definitions.Def_MinVolEllipsoid_stackAb
-- name    : MinVolEllipsoid_stackAb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:43:44.851985+00:00
-- url     : https://prove2.me/theorems/ac828b44-4703-49af-bcbb-04b50b90e8a5
-- title:
--   The $K\times(K+1)$ matrix $[A\ b]$
-- statement:
--   For a $K\times K$ matrix $A$ and $b\in\mathbb R^K$, $[A\ b]$ is the $K\times(K+1)$ matrix obtained by placing the column $b$ to the right of $A$. It appears in display (9), $[0\ 0;\ 0\ 1]\succeq_{\mathcal C(\mathcal K)}[A\ b]^\top[A\ b]$, and as the bottom block row $[A\ b\ \mathbb I]$ of the second matrix of (3).
--
--   **Formalization Note** Columns are indexed by `Fin n ⊕ Unit`, the `Unit` column being the paper's last column $b$.
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, display (9), p.8; display (3), p.6

import Mathlib

namespace MinVolEllipsoid

/-- **The `K × (K+1)` matrix `[A b]`** (Mittal & Hanasusanto, arXiv:1807.07507v4, display (9),
p.8, and the bottom block row `[A b 𝕀]` of (3), p.6).

`stackAb A b` places the column `b` to the right of the `K × K` matrix `A`.

**Formalization Note** Columns are indexed by `Fin n ⊕ Unit`, the `Unit` column being the
paper's last column `b`. -/
def stackAb {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    Matrix (Fin n) (Fin n ⊕ Unit) ℝ :=
  Matrix.of fun i j => Sum.elim (fun k => A i k) (fun _ => b i) j

end MinVolEllipsoid


