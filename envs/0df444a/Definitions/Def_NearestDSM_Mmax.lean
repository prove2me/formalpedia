-- Prove2me | Definitions.Def_NearestDSM_Mmax
-- name    : NearestDSM_Mmax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:18:23.923457+00:00
-- url     : https://prove2.me/theorems/e3478625-1195-4716-9e76-ea128c1679f4
-- title:
--   The maximal matrix at $y$
-- statement:
--   For $y\in\mathbb R^{2n-1}$, the maximal matrix is the $0$–$1$ matrix
--   $$
--   (M_{\max})_{ij}=\begin{cases}1,&(\hat x+A^Ty)_{ij}\ge 0,\\ 0,&(\hat x+A^Ty)_{ij}<0.\end{cases}
--   $$
--   It is the unique element of $\mathcal M(y)$ that is maximal in the sense of (3.9), and $V(M_{\max})$ is the matrix $\tilde V_k$ inverted in step 5 of Algorithm 3.1.
--
--   **Formalization Note** The paper's $n$ is $n+1$.
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, display (3.9), p.17; Algorithm 3.1, p.20

import Mathlib
import Definitions.Def_NearestDSM_Ymat

namespace NearestDSM

/-- The maximal matrix of Hu, Im, Li & Wolkowicz, *A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem*, arXiv:2107.09631v1, display (3.9), p.17: entry `1` where
`(x̂ + Aᵀy)_{ij} ≥ 0` and `0` elsewhere. It is the unique `M ∈ M(y)` that is maximal for `y`
(verification file), and `V(Mmax)` is "the maximal `Ṽ ∈ ∂F(ỹ)`" of Algorithm 3.1, p.20. -/
noncomputable def Mmax {n : ℕ} (Xh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (y : Dual n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun a b => if 0 ≤ Ymat Xh y a b then 1 else 0

end NearestDSM


