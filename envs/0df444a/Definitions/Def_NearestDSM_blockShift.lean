-- Prove2me | Definitions.Def_NearestDSM_blockShift
-- name    : NearestDSM_blockShift
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:19:16.864893+00:00
-- url     : https://prove2.me/theorems/ff8b352c-6e5a-4659-824a-9a520ddab055
-- title:
--   The columns $u^k$ of the block matrix $U$
-- statement:
--   Let $X=\mathrm{Mat}(\hat x+A^Ty)_+$ have the block-diagonal form $X=\mathrm{Blkdiag}(X^1,\dots,X^K)$ (up to permutation) with connected blocks, and let $R_k$, $C_k$ be the row and column indices of the $k$-th block. The matrix $U=[u^1\cdots u^K]\in\mathbb R^{(2n-1)\times K}$ has columns
--   $$
--   u^k_i=-1\ \ (i\in C_k),\qquad u^k_{n+i}=1\ \ (i\in R_k),
--   $$
--   and zeros elsewhere. Moving along $u^k$ adds a constant to the row multipliers of block $k$ and subtracts it from its column multipliers, which leaves the block unchanged.
--
--   **Formalization Note** The blocks are the connected components of the bipartite graph of $X$; a zero row or column is a component of its own (the paper's block that is empty in one dimension). $u^\kappa$ is the shift direction of the rows and columns of the component $\kappa$.
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, (3.2) p.13, (3.6)-(3.7) p.16

import Mathlib
import Definitions.Def_NearestDSM_Xmat
import Definitions.Def_NearestDSM_bipGraph
import Definitions.Def_NearestDSM_shiftVec

namespace NearestDSM

/-- The column `u^k` of the matrix `U` of Hu, Im, Li & Wolkowicz, *A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem*, arXiv:2107.09631v1, displays (3.6)–(3.7), p.16, for the
block `k` of `X = Mat(x̂ + Aᵀy)₊`: `u^k_i = −1` for `i ∈ C_k` and `u^k_{n+i} = 1` for `i ∈ R_k`,
where `R_k`, `C_k` are the row and column indices of the `k`-th diagonal block.

**Formalization Note.** The blocks of the block-diagonal form (3.2) ("up to permutation") are the
connected components `κ` of the bipartite graph of `X`; `R_κ` and `C_κ` are the rows and columns
lying in `κ`. A zero row or column of `X` is its own component, which is the paper's block that
is empty in one dimension (p.7). -/
noncomputable def blockShift {n : ℕ} (Xh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (y : Dual n)
    (κ : (bipGraph (Xmat Xh y)).ConnectedComponent) : Dual n :=
  shiftVec {a | (bipGraph (Xmat Xh y)).connectedComponentMk (Sum.inl a) = κ}
    {b | (bipGraph (Xmat Xh y)).connectedComponentMk (Sum.inr b) = κ}

end NearestDSM


