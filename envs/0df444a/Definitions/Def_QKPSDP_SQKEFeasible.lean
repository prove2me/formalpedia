-- Prove2me | Definitions.Def_QKPSDP_SQKEFeasible
-- name    : QKPSDP_SQKEFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:50.792131+00:00
-- url     : https://prove2.me/theorems/d1b2a49a-910a-4852-99a2-e2301d325605
-- title:
--   Feasible points of (SQKE)
-- statement:
--   The SDP relaxation (SQKE) of the quadratic knapsack problem is
--
--   $$
--   \min\Bigl\{ -\langle C, X\rangle :\ a^\top X a - \tau a^\top x = 0,\ \operatorname{diag}(X) = x,\ Y := \begin{pmatrix} 1 & x^\top \\ x & X \end{pmatrix} \in \mathbb S^{n+1}_+ \Bigr\}.
--   $$
--
--   A pair $(x, X) \in \mathbb R^n \times \mathbb R^{n\times n}$ is **feasible** for (SQKE) if it satisfies the three constraints.
--
--   **Formalization Note** $Y$ is a block matrix indexed by $\{\ast\} \sqcup [n]$, the extra index being the paper's first row and column. Positive semidefiniteness includes symmetry, so $X$ is symmetric at every feasible point.
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, (SQKE), p.2

import Mathlib

open Matrix

namespace QKPSDP

/-- Tang & Toh, arXiv:2303.06599v1, (SQKE), p.2: the feasible region of
`(SQKE) min { −⟨C, X⟩ : a⊤Xa − τa⊤x = 0, diag(X) = x, Y := (1 x⊤; x X) ∈ S₊ⁿ⁺¹ }`.

**Formalization Note** The variable is the pair `(x, X)`, `x ∈ ℝⁿ`, `X ∈ ℝ^{n×n}`. The block
matrix `Y = (1 x⊤; x X)` is `Matrix.fromBlocks 1 (replicateRow Unit x) (replicateCol Unit x) X`, indexed by `Unit ⊕ Fin n`
(the `Unit` index is the paper's first row/column). `Y ∈ S₊ⁿ⁺¹` is `Matrix.PosSemidef`, which over
`ℝ` includes symmetry, so `X` is symmetric for every feasible pair. -/
def SQKEFeasible {n : ℕ} (a : Fin n → ℝ) (τ : ℝ) (x : Fin n → ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  a ⬝ᵥ (X *ᵥ a) - τ * (a ⬝ᵥ x) = 0 ∧ X.diag = x ∧
    (fromBlocks (1 : Matrix Unit Unit ℝ) (replicateRow Unit x) (replicateCol Unit x) X).PosSemidef

end QKPSDP


