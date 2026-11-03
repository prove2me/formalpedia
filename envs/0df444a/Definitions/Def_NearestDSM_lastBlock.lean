-- Prove2me | Definitions.Def_NearestDSM_lastBlock
-- name    : NearestDSM_lastBlock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:18:59.570029+00:00
-- url     : https://prove2.me/theorems/5bffbcc4-8ed3-4530-affa-b6b5d7f4f40e
-- title:
--   The last block $X^K$
-- statement:
--   In the block-diagonal form $X=\mathrm{Blkdiag}(X^1,\dots,X^K)$ of $X=\mathrm{Mat}(\hat x+A^Ty)_+$, the last block $X^K$ is the block that contains the last row $n$. Its row multipliers are $r^K\in\mathbb R^{m_K-1}$, one fewer than its number of rows, because the last row has no multiplier.
--
--   The coefficient $\lambda_K$ of $u^K$ is fixed to $0$ in Lemma 3.7 and Theorem 3.9.
--
--   **Formalization Note** Blocks are connected components of the bipartite graph of $X$; the last block is the component of the node of the last row.
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, (3.2)-(3.4), p.13

import Mathlib
import Definitions.Def_NearestDSM_Xmat
import Definitions.Def_NearestDSM_bipGraph

namespace NearestDSM

/-- The last block `X^K` of Hu, Im, Li & Wolkowicz, *A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem*, arXiv:2107.09631v1, (3.2)–(3.4), p.13: the block that contains the
last row `n`, whose row multiplier was dropped (`r^K ∈ ℝ^{m_K − 1}`).

**Formalization Note.** Blocks are connected components of the bipartite graph of
`X = Mat(x̂ + Aᵀy)₊`; the last block is the component of the node of row `Fin.last n`. -/
noncomputable def lastBlock {n : ℕ} (Xh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (y : Dual n) :
    (bipGraph (Xmat Xh y)).ConnectedComponent :=
  (bipGraph (Xmat Xh y)).connectedComponentMk (Sum.inl (Fin.last n))

end NearestDSM


