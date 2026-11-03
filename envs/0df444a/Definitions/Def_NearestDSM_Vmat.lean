-- Prove2me | Definitions.Def_NearestDSM_Vmat
-- name    : NearestDSM_Vmat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:17:14.048385+00:00
-- url     : https://prove2.me/theorems/808c7145-c75a-45da-b03a-cdc671571e6b
-- title:
--   The matrix $V(M)=A\,\mathrm{Diag}(\mathrm{vec}(M))A^T$
-- statement:
--   For a matrix $M\in\mathbb R^{n\times n}$ define the symmetric $(2n-1)\times(2n-1)$ matrix
--   $$
--   V(M):=A\,\mathrm{Diag}(\mathrm{vec}(M))\,A^T .
--   $$
--   For $M\in\mathcal M(y)$ these matrices make up the generalized Jacobian $\partial F(y)$, and the Newton step of Algorithm 3.1 inverts $V(M)$ for the maximal $M$.
--
--   **Formalization Note** The paper's $n$ is $n+1$; $\mathrm{vec}(M)$ is $M$ read on (row, column) pairs.
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, display (2.8), p.8

import Mathlib
import Definitions.Def_NearestDSM_Amat
open Matrix

namespace NearestDSM

/-- `V(M) := A Diag(vec(M)) Aᵀ`, Hu, Im, Li & Wolkowicz, *A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem*, arXiv:2107.09631v1, display (2.8), p.8, for a matrix
`M ∈ ℝ^{n×n}`. It is a `(2n−1) × (2n−1)` matrix indexed like `Dual n`.

**Formalization Note.** The paper's size `n` is `n + 1`; `vec(M)` is `M` read on index pairs. -/
def Vmat {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin (n + 1) ⊕ Fin n) (Fin (n + 1) ⊕ Fin n) ℝ :=
  (Amat n * (Matrix.diagonal (fun p : Fin (n + 1) × Fin (n + 1) => M p.1 p.2) :
      Matrix (Fin (n + 1) × Fin (n + 1)) (Fin (n + 1) × Fin (n + 1)) ℝ) :
    Matrix (Fin (n + 1) ⊕ Fin n) (Fin (n + 1) × Fin (n + 1)) ℝ) * (Amat n)ᵀ

end NearestDSM


